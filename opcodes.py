#!/usr/bin/env python3

import hashlib
import struct
import sys
from typing import final

import verystable.core.key
import verystable.core.messages
import verystable.core.script
import verystable.core.secp256k1

import ripemd160

from element import Element, Atom, Cons, Error, SerDeser, int_to_bytes

class Tree:
    def __init__(self):
        self.tree = []

    @classmethod
    def dbl_n(cls, n, offset=0, size=0):
        assert offset >= 0 and (offset >> size) == 0
        r = [1]
        while n > 0:
            r = [a*2 for a in r] + [a*2+1 for a in r]
            n -= 1
        if size > 0:
            r = [(a << size) + offset for a in r]
        return r

    @classmethod
    def get_values(cls, n, offset=0, size=0):
        k, v = 0,1
        while v < n:
            k += 1
            v *= 2
        values = []
        while n > 0:
            while v > n:
                k -= 1
                v //= 2
            values.extend(cls.dbl_n(k, offset, size))
            offset = (offset * 2) + 1
            size += 1
            n -= v
        return values

    @classmethod
    def get_values_pair(cls, n1, n2):
        if n1 == 0:
            return [], cls.get_values(n2)
        elif n2 == 0:
            return cls.get_values(n1), []
        else:
            return (cls.get_values(n1, offset=0, size=1),
                    cls.get_values(n2, offset=1, size=1))

    def add(self, element):
        i = 0
        while i < len(self.tree):
            if self.tree[i] is None:
                self.tree[i] = element
                return
            element = Cons(self.tree[i], element)
            self.tree[i] = None
            i += 1
        self.tree.append(element)

    def resolve(self):
        x = None
        for el in self.tree:
            if el is None: continue
            if x is None:
                x = el
            else:
                x = Cons(el, x)
        return x

class Opcode:
    @classmethod
    @final
    def opcode_name(cls):
        return cls.__name__

    @staticmethod
    def initial_state():
        return Atom(0)

    @staticmethod
    def initial_int_state():
        return None

    @classmethod
    def argument(cls, int_state, state, arg): raise NotImplementedError

    @classmethod
    def finish(cls, int_state, state): raise NotImplementedError

class BinOpcode(Opcode):
    """For opcodes that are essentially binary operators"""
    @classmethod
    def binop(cls, left, right):
        raise NotImplementedError

    @final
    @classmethod
    def argument(cls, int_state, state, arg):
        assert int_state is None
        r = cls.binop(state, arg)
        return (r, None)

    @staticmethod
    def finish(int_state, state):
        assert int_state is None
        return state.bumpref()

class FixOpcode(Opcode):
    min_args = max_args = -1

    @classmethod
    def operation(cls, *args):
        raise NotImplementedError

    @final
    @staticmethod
    def state_info(state):
        if state.is_nil(): return 0, state
        assert state.is_cons() and state.val2.is_atom()
        return state.val2.as_int(), state.val1

    @final
    @classmethod
    def argument(cls, int_state, state, arg):
        assert int_state is None
        n, rest = cls.state_info(state)
        if n >= cls.max_args:
            return Error("too many arguments")
        return (Cons(Cons(arg.bumpref(), rest.bumpref()), Atom(n+1)), None)

    @final
    @classmethod
    def finish(cls, int_state, state):
        assert int_state is None
        n, rest = cls.state_info(state)
        if n < cls.min_args:
            return Error("too few arguments")
        args = []
        for _ in range(n):
            args.append(rest.val1)
            rest = rest.val2
        return cls.operation(*(args[::-1]))

class op_x(FixOpcode):
    min_args = 0
    max_args = 10
    @classmethod
    def operation(cls, *args):
        return Error(f"Exception: {" ".join(str(a) for a in args)}")

class op_add(BinOpcode):
    @classmethod
    def binop(cls, left, right):
        if left.is_atom() and right.is_atom():
            return Atom(left.as_int() + right.as_int())
        else:
            return Error("add requires atoms")

class op_sub(BinOpcode):
    @staticmethod
    def initial_state():
        return Cons(Atom(0), Atom(0))

    @classmethod
    def binop(cls, left, right):
        if not right.is_atom():
            return Error("sub requires atoms")
        if left.is_cons() and left.val1.is_nil():
            return Cons(Atom(1), right.bumpref())
        elif left.is_cons():
            return Atom(left.val2.as_int() - right.as_int())
        else:
            return Atom(left.as_int() - right.as_int())

    @staticmethod
    def finish(intstate, state):
        if state.is_cons():
            return Atom(0 - state.val2.as_int())
        else:
            return state.bumpref()

class op_mul(BinOpcode):
    @staticmethod
    def initial_state():
        return Atom(1)

    @classmethod
    def binop(cls, left, right):
        if left.is_atom() and right.is_atom():
            return Atom(left.as_int() * right.as_int())
        else:
            return Error("mul requires atoms")

class op_mod(FixOpcode):
    min_args = max_args = 2

    @classmethod
    def operation(cls, num, den):
        if not num.is_atom() or not den.is_atom():
            return Error("mod requires atoms")
        return Atom(num.as_int() % den.as_int())

class op_lt_num(BinOpcode):
    @staticmethod
    def initial_state():
        return Atom(1)

    @classmethod
    def binop(cls, left, right):
        if not right.is_atom():
            return Atom(0)
        if left.is_cons():
            if left.val2.as_int() >= right.as_int():
                return Atom(0)
        return Cons(Atom(1), right.bumpref())

    @staticmethod
    def finish(intstate, state):
        if state.is_atom():
            return state.bumpref()
        else:
            return state.val1.bumpref()

class op_i(FixOpcode):
    min_args = 1
    max_args = 3

    @classmethod
    def operation(cls, c, t=None, e=None):
        if c.is_nil():
            return e.bumpref() if e is not None else c.bumpref()
        else:
            return t.bumpref() if t is not None else Atom(1)

class IntStateOpcode(Opcode):
    @classmethod
    @final
    def argument(cls, int_state, state, arg):
        assert state.is_nil()
        next_state = cls.update_state(int_state, arg)
        if isinstance(next_state, Element):
            assert next_state.is_error()
            return (next_state, None)
        return (state.bumpref(), next_state)

    @classmethod
    @final
    def finish(cls, int_state, state):
       assert state.is_nil()
       return cls.final_state(int_state)

    @classmethod
    def update_state(cls, int_state, arg):
        raise NotImplementedError

    @classmethod
    def final_state(cls, int_state):
        raise NotImplementedError

class op_sha256(IntStateOpcode):
    @classmethod
    def initial_int_state(cls):
        return hashlib.sha256()

    @classmethod
    def update_state(cls, int_state, arg):
        if not arg.is_atom():
            return Error("cannot hash list")
        h = int_state.copy()
        h.update(arg.val2)
        return h

    @classmethod
    def final_state(cls, int_state):
        return Atom(int_state.digest())

class op_ripemd160(op_sha256):
    @classmethod
    def initial_int_state(cls):
        return ripemd160.hasher()

class op_hash160(op_sha256):
    @classmethod
    def final_state(cls, int_state):
        x = ripemd160.hasher()
        x.update(int_state.digest())
        return Atom(x.digest())

class op_hash256(op_sha256):
    @classmethod
    def final_state(cls, int_state):
        x = hashlib.sha256()
        x.update(int_state.digest())
        return Atom(x.digest())

class op_rc(BinOpcode):
    @classmethod
    def binop(cls, left, right):
        if left.is_cons():
            return Cons(left.val1.bumpref(), Cons(right.bumpref(), left.val2.bumpref()))
        else:
            return Cons(left.bumpref(), right.bumpref())

    @classmethod
    def finish(cls, intstate, state):
        if state.is_cons():
            return state.val2.bumpref()
        else:
            return state.bumpref()

class op_b(BinOpcode):
    @classmethod
    def binop(cls, left, right):
        if left.is_nil():
            return Cons(Cons(right.bumpref(), Atom(0)), Atom(1))
        else:
            assert left.is_cons() and left.val1.is_cons() and left.val2.is_atom()
            n = left.val2.as_int()
            n_next = n + 1
            v = right.bumpref()
            m = left.val1
            while n % 2 == 1:
                assert m.is_cons()
                n //= 2
                v = Cons(m.val1.bumpref(), v)
                m = m.val2
            return Cons(Cons(v, m.bumpref()), Atom(n_next))

    @classmethod
    def finish(cls, intstate, state):
        if state.is_nil():
            return state.bumpref()
        else:
            assert state.is_cons() and state.val1.is_cons() and state.val2.is_atom()
            l = state.val1.val1.bumpref()
            rest = state.val1.val2
            while rest.is_cons():
                l = Cons(rest.val1.bumpref(), l)
                rest = rest.val2
            assert rest.is_nil()
            return l

class op_h(FixOpcode):
    min_args = max_args = 1

    @classmethod
    def operation(cls, lst):
        if not lst.is_cons():
            return Error("not a list")
        return lst.val1.bumpref()

class op_t(FixOpcode):
    min_args = max_args = 1

    @classmethod
    def operation(cls, lst):
        if not lst.is_cons():
            return Error("not a list")
        return lst.val2.bumpref()

class op_l(FixOpcode):
    min_args = max_args = 1

    @classmethod
    def operation(cls, lst):
        return Atom(1 if lst.is_cons() else 0)

class op_nand(BinOpcode):
    # aka is any false?
    @classmethod
    def binop(cls, left, right):
        if right.is_nil():
            return Atom(1)
        else:
            return left.bumpref()

class op_and(BinOpcode):
    # aka are all true?

    @staticmethod
    def initial_state():
        return Atom(1)

    @classmethod
    def binop(cls, left, right):
        if right.is_nil():
            return Atom(0)
        else:
            return left.bumpref()

class op_or(BinOpcode):
    # aka are any true?

    @classmethod
    def binop(cls, left, right):
        if not right.is_nil():
            return Atom(1)
        else:
            return left.bumpref()

class op_or_bytes(BinOpcode):
    @classmethod
    def binop(cls, left, right):
        if not right.is_atom():
            return Error("or_bytes: argument must be atom")
        out = bytearray(max(left.val1, right.val1))
        for i,e in enumerate(left.val2):
            out[i] = e
        for i,e in enumerate(right.val2):
            out[i] |= e
        return Atom(bytes(out))

class op_xor_bytes(BinOpcode):
    @classmethod
    def binop(cls, left, right):
        if not right.is_atom():
            return Error("xor_bytes: argument must be atom")
        out = bytearray(max(left.val1, right.val1))
        for i,e in enumerate(left.val2):
            out[i] = e
        for i,e in enumerate(right.val2):
            out[i] ^= e
        return Atom(bytes(out))

class op_and_bytes(BinOpcode):
    @classmethod
    def binop(cls, left, right):
        if not right.is_atom():
            return Error("and_bytes: argument must be atom")
        if left.is_nil():
            return right.bumpref()
        else:
            out = bytearray((0 for _ in range(max(left.val1, right.val1))))
            for i,(el, er) in enumerate(zip(left.val2, right.val2)):
                out[i] = el & er
            return Atom(bytes(out))

class op_nand_bytes(BinOpcode):
    @classmethod
    def binop(cls, left, right):
        if not right.is_atom():
            return Error("nand_bytes: argument must be atom")
        out = bytearray((255 for _ in range(max(left.val1, right.val1))))
        for i,e in enumerate(left.val2):
            out[i] = (e ^ 255)
        for i,e in enumerate(right.val2):
            out[i] &= e
        for i in range(len(out)):
            out[i] ^= 255
        return Atom(bytes(out))

class op_shift(FixOpcode):
    min_args = max_args = 2

    @classmethod
    def operation(cls, inp, n):
        if not isinstance(inp, Atom) or not isinstance(n, Atom):
            return Error("shift: expects atomic arguments")
        delta = n.as_int()
        if delta == 0:
            return inp.bumpref()

        bb = bytearray(delta//8) if delta > 0 else bytearray()
        overflow = 0
        if delta > 0:
            delta %= 8
        for b in inp.val2:
            if delta < -8:
                delta += 8
                continue
            elif delta < 0:
                overflow = b >> (-delta)
                delta += 8
                continue
            x = (b << delta) + overflow
            bb.append(x & 0xFF)
            overflow = x >> 8
        bb.append(overflow)
        return Atom(bytes(bb))

class op_eq(BinOpcode):
    @staticmethod
    def initial_state():
        return Atom(1)

    @classmethod
    def binop(cls, left, right):
        if left.is_nil():
            # failed already
            return left.bumpref()
        elif not right.is_atom():
            # non-atoms aren't compared with this opcode
            return Atom(0)
        elif left.is_atom():
            # first arg, nothing to be equal to
            return Cons(right.bumpref(), left.bumpref())
        else:
            assert left.is_cons() and left.val1.is_atom()
            if left.val1.val1 != right.val1 or left.val1.val2 != right.val2:
                return Atom(0)
            else:
                return left.bumpref()

    @staticmethod
    def finish(intstate, state):
        if state.is_cons():
            return state.val2.bumpref()
        else:
            return state.bumpref()

class op_bigeq(BinOpcode):
    @staticmethod
    def initial_state():
        return Atom(1)

    @classmethod
    def binop(cls, left, right):
        if left.is_nil():
            # failed already
            return left.bumpref()
        elif left.is_atom():
            # first arg, nothing to be equal to
            return Cons(right.bumpref(), left.bumpref())
        else:
            chk = [(left.val1, right)]
            while chk:
                a, b = chk.pop()
                if a.is_atom():
                    if not b.is_atom() or a.val1 != b.val1 or a.val2 != b.val2:
                        return Atom(0)
                elif b.is_atom():
                    return Atom(0)
                else:
                    assert a.is_cons() and b.is_cons()
                    chk.append((a.val1, b.val1))
                    chk.append((a.val2, b.val2))
            return left.bumpref()

    @staticmethod
    def finish(intstate, state):
        if state.is_cons():
            return state.val2.bumpref()
        else:
            return state.bumpref()

class op_strlen(BinOpcode):
    @classmethod
    def binop(cls, left, right):
        if not right.is_atom():
            return Error(f"strlen: not an atom {right}")
        return Atom(left.as_int() + len(right.val2))

class op_cat(BinOpcode):
    @classmethod
    def binop(cls, left, right):
        if not right.is_atom():
            return Error(f"cat: not an atom {right}")
        return Atom(left.val2 + right.val2)

class op_substr(FixOpcode):
    min_args = 0
    max_args = 3

    @classmethod
    def operation(cls, el=None, start=None, end=None):
        if el is None:
            return Atom(0)
        if not el.is_atom():
            return Error("substr: cannot take substr of non-atom")

        if start is None:
            return el.bumpref()
        if not start.is_atom():
            return Error("substr: start must be atom")
        start = start.as_int()

        if end is not None and not end.is_atom(): 
            return Error("substr: end must be atom")
        if end is None:
            end = el.val1
        else:
            end = end.as_int()

        if start == 0 and end >= el.val1:
            return el.bumpref()

        if start > el.val1:
            return Atom(0)

        return Atom(el.val2[start:end])

class op_lt_str(BinOpcode):
    @staticmethod
    def initial_state():
        return Atom(1)

    @classmethod
    def binop(cls, left, right):
        if not right.is_atom():
            return Atom(0)
        if left.is_cons():
            if left.val2.val2 >= right.val2:
                return Atom(0)
        return Cons(Atom(1), right.bumpref())

    @staticmethod
    def finish(intstate, state):
        if state.is_atom():
            return state.bumpref()
        else:
            return state.val1.bumpref()

'''
# op_mod / op_divmod
class op_div_u64(Operator):
    def __init__(self):
        self.i = None

    def argument(self, el):
        if not el.is_atom(): raise Exception("div: arguments must be atoms")
        n = el.atom_as_u64()
        el.deref()
        if self.i is None:
            self.i = n
        else:
            ## if el >= 2**64 should we just set i to 0?
            if n == 0:
                raise Exception("div: attempted div by 0")
            self.i //= n

    def finish(self):
        if self.i is None:
            raise Exception("div: missing arguments")
        return Atom(self.i)
'''

class op_list_read(FixOpcode):
    min_args = max_args = 1

    @classmethod
    def operation(cls, el):
        if not el.is_atom():
            raise Exception("rd: argument must be atom")
        edeser = SerDeser.Deserialize(el.val2)
        return edeser

class op_list_write(FixOpcode):
    min_args = max_args = 1

    @classmethod
    def operation(cls, el):
        eser = SerDeser.Serialize(el)
        return Atom(eser)

class op_secp256k1_muladd(BinOpcode):
    """(secp256k1_muladd a (b) (c . d) (1 . e) (nil . f))
       checks that a*G - b*G + c*D + E - F = 0
       Script aborts otherwise.

       That is, an atom on its own is interpreted as a scalar and
       multiplied by G; a cons pair is interpreted as a scalar followed
       by a point; if the point is nil, it is interpreted as -G; if the
       scalar is nil, it is treated as -1.

       Scalars are interpreted as little endian. 33-byte values for the
       point are treated as compressed points, 32-byte values for the
       points are evaluated via BIP340's lift_x().

       BIP340 validation is thus equivalent to:
           (secp256k1_muladd ('1 . R) (e . P) (s))
       where e is H(R,P,m) as per BIP340.
    """

    @classmethod
    def binop(cls, left, right):
        if right.is_cons():
            scalar = right.val1
            if not right.val2.is_atom():
                return Error("secp256k1_muladd: point must be atom")
        else:
            scalar = right
        if not scalar.is_atom():
            return Error("secp256k1_muladd: scalar must be atom")
        if scalar.val1 > 32:
            return Error("secp25691_muladd: scalar out of range")

        return Cons(right.bumpref(), left.bumpref())

    @staticmethod
    def finish(intstate, state):
        assert intstate is None
        aps = []
        while isinstance(state, Cons):
            el, state = state.val1, state.val2
            if el.is_atom():
                bscalar = el.val2
                bpoint = None
            else:
                assert el.is_cons()
                assert el.val1.is_atom() and el.val2.is_atom()
                bscalar = el.val1.val2
                bpoint = el.val2.val2
            if bpoint is None:
                point = verystable.core.secp256k1.G
            elif bpoint == b'':
                point = -verystable.core.secp256k1.G
            elif len(bpoint) == 32:
                point = verystable.core.secp256k1.GE.from_bytes_xonly(bpoint)
            elif len(bpoint) == 33 and (bpoint[0] == 2 or bpoint[0] == 3):
                point = verystable.core.secp256k1.GE.from_bytes(bpoint)
            else:
                return Error(f"secp256k1_muladd: unparseable point 0x{bpoint.hex()}")
            if point is None:
                return Error(f"secp256k1_muladd: invalid point 0x{bpoint.hex()}")
            if bscalar == b'':
                scalar = 1
                point = -point
                # or scalar = GE.ORDER-1
            else:
                # XXX treating as big-endian for compatibility with bip340, and lack of `rev` opcode
                scalar = int.from_bytes(bscalar, byteorder='big', signed=False) % verystable.core.secp256k1.GE.ORDER
                if scalar == 0:
                    return Error("secp256k1_muladd: scalar is 0")
            aps.append((scalar,point))
        x = verystable.core.secp256k1.GE.mul(*aps)
        if not x.infinity:
            return Error(f"secp256k1_muladd: did not sum to inf; {x.to_bytes_compressed().hex()}")
        return Atom(1)

class op_bip340_verify(FixOpcode):
    min_args = max_args = 3

    @classmethod
    def operation(cls, pk, m, sig):
        if not pk.is_atom() or pk.val1 != 32:
            return Error(f"invalid pubkey {pk}")
        if not m.is_atom() or m.val1 != 32:
            return Error("invalid msg")

        if sig.is_nil():
            return sig.bumpref()

        if not sig.is_atom() or (sig.val1 != 64 and sig.val1 != 0):
            return Error("invalid sig")

        r = verystable.core.key.verify_schnorr(key=pk.val2, sig=sig.val2, msg=m.val2)
        if not r:
            # must be an error to allow for batch verification
            return Error("bip340_verify: invalid, non-empty signature")

        return Atom(1)

class op_ecdsa_verify(FixOpcode):
    min_args = max_args = 3

    @classmethod
    def operation(cls, pk, m, sig):
        if not pk.is_atom() or (pk.val1 != 33 and pk.val1 != 65):
            return Error(f"invalid pubkey size {pk.val1}")

        ecpk = verystable.core.key.ECPubKey()
        ecpk.set(pk.val2)
        if not ecpk.is_valid:
            return Error(f"invalid pubkey {pk.val2.hex()}")

        if not m.is_atom() or m.val1 != 32:
            return Error("invalid msg")

        if sig.is_nil():
            return sig.bumpref()

        if not sig.is_atom():
            return Error("invalid sig")

        r = ecpk.verify_ecdsa(sig.val2, m.val2, low_s=False)
        if not r:
            # treat as an error for consistency with bip340_verify, and avoid
            # wasted calculations
            return Error("ecdsa_verify: invalid, non-empty signature")

        return Atom(1)

class op_bip342_txmsg(FixOpcode):
    min_args = 0
    max_args = 1

    @classmethod
    def operation(cls, sighash=None):
        global GLOBAL_TX, GLOBAL_TX_INPUT_IDX, GLOBAL_TX_SCRIPT, GLOBAL_UTXOS

        if sighash is None:
            sighash = 0
        elif sighash.is_atom() and sighash.val1 == 1:
            sighash = sighash.val2[0]
        else:
            return Error("bip342_txmsg: expects a single sighash byte")
        if sighash not in [0x00, 0x01, 0x02, 0x03, 0x81, 0x82, 0x83]:
            return Error("bip342_txmsg: unknown sighash byte")

        if GLOBAL_TX is None:
            return Error("bip342_txmsg: tx is not set")
        if GLOBAL_TX_INPUT_IDX is None:
            return Error("bip342_txmsg: tx input idx not set")
        if GLOBAL_TX_SCRIPT is None:
            return Error("bip342_txmsg: tx script not set")
        if GLOBAL_UTXOS is None:
            return Error("bip342_txmsg: utxos not set")

        annex = None
        if len(GLOBAL_TX.wit.vtxinwit) > 0:
            w = GLOBAL_TX.wit.vtxinwit[GLOBAL_TX_INPUT_IDX].scriptWitness.stack
            if len(w) > 0 and w[-1][0] == 0x50:
                annex = w[-1]
        r = verystable.core.script.TaprootSignatureHash(txTo=GLOBAL_TX, spent_utxos=GLOBAL_UTXOS, hash_type=sighash, input_index=GLOBAL_TX_INPUT_IDX, scriptpath=True, annex=annex, script=GLOBAL_TX_SCRIPT)
        return Atom(r)

class op_tx(BinOpcode):
    @classmethod
    def binop(cls, left, right):
        assert left.is_atom()
        if right.is_atom():
            code = right.as_int()
            which = None
        elif right.is_cons() and right.val1.is_atom() and right.val2.is_atom():
            code = right.val1.as_int()
            which = right.val2.as_int()
        else:
            return Error("tx: bad argument")

        result = cls.get_tx_info(code, which)
        if isinstance(result, Element):
            return result
        else:
            assert isinstance(result, bytes), f"invalid tx result {result}"
            return Atom(left.val2 + result)

    @classmethod
    def get_tx_info(cls, code, which):
        if 0 <= code <= 9:
            if which is not None: return Error(f"tx: {code} should be an atom not a pair")
            return cls.get_tx_global_info(code)
        elif 10 <= code <= 19:
            if which is None: which = GLOBAL_TX_INPUT_IDX
            if which < 0 or which >= len(GLOBAL_TX.vin):
                return Error(f"tx: {code} has invalid input index {which}")
            return cls.get_tx_input_info(code, which)
        elif 20 <= code <= 29:
            if which is None: which = GLOBAL_TX_INPUT_IDX
            if which < 0 or which >= len(GLOBAL_TX.vout):
                return Error(f"tx: {code} requires valid output index")
            return cls.get_tx_output_info(code, which)
        else:
            return Error(f"tx: {code} out of range")

    @classmethod
    def get_bip341info(cls):
        # XXX currently unexposed
        wit = GLOBAL_TX.wit.vtxinwit[GLOBAL_TX_INPUT_IDX].scriptWitness.stack
        n = len(wit) - 1
        if n > 0 and wit[n][0] == 0x50: n -= 1 # skip annex
        if n <= 0 or len(wit[n]) == 0: return None, None # key spend, or no witness data

        cb = wit[n]
        leafver = cb[0] & 0xFE
        sign = cb[0] & 0x01
        if len(cb) % 32 == 1:
            ipk = cb[1:33]
            path = [cb[i:i+32] for i in range(33, len(cb), 32)]
        else:
            ipk = path = None
        return leafver, sign, ipk, path

    @classmethod
    def get_tx_global_info(cls, code):
        if code == 0:
            return struct.pack("<i", GLOBAL_TX.nVersion)
        elif code == 1:
            return struct.pack("<I", GLOBAL_TX.nLockTime)
        elif code == 2:
            return int_to_bytes(len(GLOBAL_TX.vin))
        elif code == 3:
            return int_to_bytes(len(GLOBAL_TX.vout))
        elif code == 4:
            return int_to_bytes(GLOBAL_TX_INPUT_IDX)
        elif code == 5:
            return GLOBAL_TX.serialize_without_witness()
        elif code == 6:
            # the TapLeaf hash for the current script
            wit = GLOBAL_TX.wit.vtxinwit[GLOBAL_TX_INPUT_IDX].scriptWitness.stack
            n = len(wit) - 1
            if n >= 0 and wit[n][0] == 0x50: n -= 1 # skip annex
            if n >= 1 and len(wit[n]) > 0:
                v = (wit[n][0] & 0xFE)
                s = wit[n-1]
                h = verystable.core.key.TaggedHash("TapLeaf", bytes([v]) + verystable.core.messages.ser_string(s))
                return h
            else:
                return b''
        elif code == 7:
            # taproot internal pubkey
            leafver, sign, ipk, path = cls.get_bip341info()
            return ipk
        elif code == 8:
            # taproot merkle path
            leafver, sign, ipk, path = cls.get_bip341info()
            return b"".join(path)
        elif code == 9:
            # leafver, sign
            leafver, sign, ipk, path = cls.get_bip341info()
            return Cons(Atom(leafver), Atom(sign)) # XXX split?
        else:
            assert False # unreachable

    @classmethod
    def get_tx_input_info(cls, code, which):
        txin = GLOBAL_TX.vin[which]
        wit = GLOBAL_TX.wit.vtxinwit[which].scriptWitness.stack
        if code == 10:
             return struct.pack("<I", txin.nSequence)
        elif code == 11:
             return verystable.core.messages.ser_uint256(txin.prevout.hash)
        elif code == 12:
             return struct.pack("<I", txin.prevout.n)
        elif code == 13:
             return txin.scriptSig
        elif code == 14:
             # annex, including 0x50 prefix
             if len(wit) > 0 and len(wit[-1]) > 0 and wit[-1][0] == 0x50:
                 return wit[-1]
             else:
                 return b''
        elif code == 15:
             coin = GLOBAL_UTXOS[which]
             return struct.pack("<Q", coin.nValue)
        elif code == 16:
             coin = GLOBAL_UTXOS[which]
             return coin.scriptPubKey
        else:
             return b''

    @classmethod
    def get_tx_output_info(cls, code, which):
        out = GLOBAL_TX.vout[which]
        if code == 20:
             return struct.pack("<Q", out.nValue)
        elif code == 21:
             return out.scriptPubKey
        else:
             return b''

FUNCS = [
#  (b'', "q", None), # quoting indicator, special
#  (0x01, "a", op_a),  # apply
#  (0x02, "sf", op_softfork),
#  (0x03, "partial", op_partial),  # partially apply the following function
     # these are "magic" opcodes. "q" is magic because its args aren't evaluated and
     # do not need to be a proper list; "a" and "sf" are magic because their result
     # gets evaluated further; "partial" is magic, because it returns and accepts a
     # non-representable function object, rather than bll-code

  (0x04, "x", op_x),  # exception
  (0x05, "i", op_i),  # eager-evaluated if

  (0x06, "rc", op_rc), # construct a list in reverse
  (0x07, "h", op_h), # head / car
  (0x08, "t", op_t), # tail / cdr
  (0x09, "l", op_l), # is cons?
  (0x0a, "b", op_b), # convert list to binary tree

  (0x0b, "notall", op_nand),
  (0x0c, "all", op_and),
  (0x0d, "any", op_or),

  (0x0e, "=", op_eq),  # compares atoms only
  (0x0f, "<s", op_lt_str),
  (0x10, "strlen", op_strlen),
  (0x11, "substr", op_substr),
  (0x12, "cat", op_cat),

  (0xff, "===", op_bigeq), ## XXX shouldn't be an opcode?

  (0x13, "~", op_nand_bytes),
  (0x14, "&", op_and_bytes),
  (0x15, "|", op_or_bytes),
  (0x16, "^", op_xor_bytes),

  (0x17, "+", op_add),
  (0x18, "-", op_sub),
  (0x19, "*", op_mul),
  (0x1a, "%", op_mod),
  (0x1b, "shift", op_shift),
  (0x1e, "<", op_lt_num),   # not restricted to u64
# 0x1c, 0x1d, 0x1f missing

  (0x20, "rd", op_list_read), # read bytes to Element
  (0x21, "wr", op_list_write), # write Element as bytes

  (0x22, "sha256", op_sha256),
  (0x23, "ripemd160", op_ripemd160),
  (0x24, "hash160", op_hash160),
  (0x25, "hash256", op_hash256),
  (0x26, "bip340_verify", op_bip340_verify),
  (0x27, "ecdsa_verify", op_ecdsa_verify),
  (0x28, "secp256k1_muladd", op_secp256k1_muladd),

  (0x29, "tx", op_tx),
  (0x2a, "bip342_txmsg", op_bip342_txmsg),

#  ideas:
#    (signextend 0x81 4) -> 0x01000080
#       (signextend 0x123400 0) = (signextend 0x123400) -> 0x1234
#       (= (signextend a) (signextend b)) <-- numequal
#       ... maybe (substr ...) should pad short strings with trailing 0's?
#    (max/min a b c) -> (using < or <s ?)
#    (rev 0x01020304) -> 0x04030201
#    (abs 0x81) -> 0x01
#    (constant K) -> (G, H, G/2, curve order, etc)
#    (log2b42 N) -> floor(log_2(n) * 2**42), error if n<=0
#    / /% -> division, divmod
]


def _Do_FUNCS():
    se = {}
    op = {}
    for (val, name, fn) in FUNCS:
        assert name not in se
        assert val not in op
        se[name] = val
        op[val] = fn
    return se, op
SExpr_FUNCS, Op_FUNCS = _Do_FUNCS()

GLOBAL_TX = None
GLOBAL_TX_INPUT_IDX = None
GLOBAL_TX_SCRIPT = None
GLOBAL_UTXOS = None

def Set_GLOBAL_TX(tx):
    global GLOBAL_TX
    GLOBAL_TX = tx

def Get_GLOBAL_TX():
    global GLOBAL_TX
    return GLOBAL_TX

def Set_GLOBAL_TX_INPUT_IDX(idx):
    global GLOBAL_TX_INPUT_IDX
    GLOBAL_TX_INPUT_IDX = idx

def Get_GLOBAL_TX_INPUT_IDX():
    global GLOBAL_TX_INPUT_IDX
    return GLOBAL_TX_INPUT_IDX

def Set_GLOBAL_TX_SCRIPT(scr):
    global GLOBAL_TX_SCRIPT
    GLOBAL_TX_SCRIPT = scr

def Get_GLOBAL_TX_SCRIPT():
    global GLOBAL_TX_SCRIPT
    return GLOBAL_TX_SCRIPT

def Set_GLOBAL_UTXOS(utxos):
    global GLOBAL_UTXOS
    GLOBAL_UTXOS = utxos

def Get_GLOBAL_UTXOS():
    global GLOBAL_UTXOS
    return GLOBAL_UTXOS

