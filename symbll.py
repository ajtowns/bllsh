#!/usr/bin/env python3

from __future__ import annotations

import abc
import functools

from dataclasses import dataclass, field
from typing import List, Optional, Any

from element import ALLOCATOR, Element, SExpr, Atom, Cons, Error, Func, FuncClass, Symbol
from opcodes import SExpr_FUNCS, Op_FUNCS, Opcode
from bll import OpAtom
from workitem import fn_fin, fn_quote, fn_op, fn_partial

####

@dataclass
class SymbolInfo:
    is_func: bool
    position: Optional[int] = None
    sexpr: Optional[Element] = None
    params: Optional[List[str]] = None

class SymbolContainer(abc.ABC):
    @abc.abstractmethod
    def __getitem__(self, n):
        pass

class SymbolTable(SymbolContainer):
    """maps symbols (by name) to values"""

    def __init__(self):
        self.refcnt = 1
        self.syms = {}

    @classmethod
    def mkinfo(cls, symvalue):
        if isinstance(symvalue, tuple):
            return SymbolInfo(is_func=True, sexpr=symvalue[1], params=symvalue[0])
        else:
            return SymbolInfo(is_func=False, sexpr=symvalue)

    @classmethod
    def from_list(cls, symlist : Element) -> SymbolTable:
        s = cls()
        while isinstance(symlist, Cons):
            v, symlist = symlist.steal_children()
            assert isinstance(v, Cons) and isinstance(v.val2, Symbol)
            if v.val2.val2 not in s.syms:
                s.set(v.val2.val2, v.val1.bumpref())
            v.deref()
        assert symlist.is_nil()
        symlist.deref()
        return s

    def __iter__(self):
        yield from self.syms.keys()

    def __getitem__(self, symname):
        if symname not in self.syms:
            return None
        return self.mkinfo(self.syms[symname])

    def set(self, symname, value):
        # XXX: cope with default values for parameters
        assert self.refcnt == 1
        assert isinstance(symname, str)
        if not isinstance(value, Element):
            assert isinstance(value, tuple) and len(value) == 2
            assert all(isinstance(v, Element) for v in value)

        if symname in self.syms:
            if isinstance(self.syms[symname], tuple):
                for e in self.syms[symname]:
                    e.deref()
            else:
                self.syms[symname].deref()
        self.syms[symname] = value

    def unset(self, symname):
        assert self.refcnt == 1
        assert isinstance(symname, str), f"{repr(symname)} not a str?"
        if symname in self.syms:
            if isinstance(self.syms[symname], tuple):
                for e in self.syms[symname]:
                    e.deref()
            else:
                self.syms[symname].deref()
            del self.syms[symname]

    def bumpref(self):
        self.refcnt += 1
        return self

    def deref(self):
        self.refcnt -= 1
        if self.refcnt == 0:
            for _, v in self.syms.items():
                v.deref()
            self.syms = None

class SymbolIndex(SymbolContainer):
    """maps symbols (by name) to their position in a BLL environment"""

    def __init__(self, vals, offset=1):
        if isinstance(vals, SymbolTable):
            vals = [(v, vals[v]) for v in vals]
        else:
            vals = [(v, SymbolInfo()) for v in vals]

        x = []
        for vsi in vals:
            self.add(x, vsi)
        x = self.finish(x)

        m,a = 1,offset
        while offset > 1:
            m *= 2
            offset //= 2
        a -= m

        self.ordering = [n for (n,si),pos in x]
        self.indexes = {}
        for (n,si),pos in x:
            si.position = pos*m + a
            self.indexes[n] = si

    def __iter__(self):
        yield from self.ordering

    def __getitem__(self, n):
        return self.indexes.get(n, None)

    @staticmethod
    def add(sofar, symname):
        sofar.append( (1, [(symname, 1)]) )

        while len(sofar) > 1 and sofar[-1][0] == sofar[-2][0]:
            cntb, b = sofar.pop()
            cnta, a = sofar.pop()
            c = [(n, v*2) for n,v in a] + [(n, v*2+1) for n,v in b]
            sofar.append( (cnta + cntb, c) )

    @staticmethod
    def finish(sofar):
        if len(sofar) == 0: return []
        res = sofar.pop()[1]
        while sofar:
            _, a = sofar.pop()
            res = [(n, v*2) for n,v in a] + [(n, v*2+1) for n,v in res]
        return res

def ResolveSymbol(localsyms : SymbolTable, globalsyms : SymbolTable, symname : str) -> Optional[Element]:
    if symname == "if":
        return Func(fn_if, None, Atom(0))

    if symname == "q":
        return Func(fn_quote, None, Atom(0))

    if symname == "report":
        return Func(fn_report, None, Atom(0))

    if symname == "partial":
        return Func(fn_partial, None, Atom(0))

    if symname in SExpr_FUNCS:
        opcls = Op_FUNCS[SExpr_FUNCS[symname]]
        return Func(fn_op, (opcls, opcls.initial_int_state()), opcls.initial_state())

    # locals override globals, but do not override builtins
    r = localsyms[symname]
    if r is None:
        r = globalsyms[symname]
    if r is None:
        return None

    if r.is_func:
        return Func(fn_userfunc, None, Cons(r.sexpr.bumpref(), Cons(r.params.bumpref(), Atom(0))))
    else:
        return r.sexpr.bumpref()

#### evaluation model = workitem with continuations

@FuncClass.implements_API
class fn_symbll_eval(FuncClass):
    @classmethod
    def step(cls, state : Element, args : Element, env : Any, workitem : Any) -> None:
        assert state.is_nil()
        state.deref()

        if isinstance(args, Atom) or isinstance(args, Error):
            env.deref()
            workitem.fin_value(args)
        elif isinstance(args, Cons):
            op, args = args.steal_children()
            if op.is_symbol():
                r = ResolveSymbol(env, workitem.globalsyms, op.val2)
                if r is None:
                    args.deref()
                    env.deref()
                    workitem.error(f"undefined symbol {op}")
                elif isinstance(r, Func):
                    workitem.new_continuation(r, args, env)
                else:
                    workitem.error("symbolic expression treated as function")
                    r.deref()
                    args.deref()
                    env.deref()
                op.deref()
            else:
                op.deref()
                args.deref()
                env.deref()
                workitem.error("expression does not have a function/operator")
        elif args.is_func():
            # not sure?
            env.deref()
            args.deref()
            workitem.error("BUG? expression with raw function??")
        elif args.is_symbol():
            r = ResolveSymbol(env, workitem.globalsyms, args.val2)
            if r is None:
                env.deref()
                workitem.error(f"undefined symbol {args}")
                args.deref()
            elif isinstance(r, Element):
                workitem.fin_value(r)
                args.deref()
                env.deref()
            else:
                workitem.error(f"BUG? symbol {args}={r} isn't an element")
                args.deref()
                env.deref()
        else:
            # internal error
            args.deref()
            env.deref()
            workitem.error("BUG? not sure what to eval")

@FuncClass.implements_API
class fn_if(FuncClass):
    @classmethod
    def step(cls, state : Element, args : Element, env : Any, workitem : Any) -> None:
        assert state.is_nil()
        state.deref()

        if not isinstance(args, Cons):
            args.deref()
            env.deref()
            workitem.error("if requires at least one argument")
            return

        cond, args = args.steal_children()
        workitem.new_continuation(Func(cls, None, Atom(0)), args, env)
        workitem.eval_arg(cond, env.bumpref())

    @classmethod
    def feedback(cls, state : Element, value : Element, args : Element, env : Any, workitem : Any) -> None:
        assert state.is_nil()
        state.deref()
        assert not isinstance(value, Error)

        if isinstance(args, Cons):
            iftrue, args = args.steal_children()
        elif args.is_nil():
            iftrue = Atom(1)

        if isinstance(args, Cons):
            iffalse, args = args.steal_children()
        elif args.is_nil():
            iffalse = Atom(0)

        if not args.is_nil():
            is_cons = isinstance(args, Cons)
            Element.deref_all(iftrue, iffalse, value, args)
            env.deref()
            if is_cons:
                workitem.error("if must have at most three arguments")
            else:
                workitem.error("argument to if are improper list")
            return
        args.deref()

        if value.is_nil():
            iftrue.deref()
            workitem.eval_arg(iffalse, env)
        else:
            iffalse.deref()
            workitem.eval_arg(iftrue, env)

        value.deref()

@FuncClass.implements_API
class fn_report(FuncClass):
    @staticmethod
    def report(state):
        a = []
        while state.is_cons():
            a.append(state.val1)
            state = state.val2
        if not a:
            last = state
        else:
            last = a[-1]
        print(f"report: ({" ".join(map(str, reversed(a)))})")
        return last.bumpref()

    @classmethod
    def step(cls, state : Element, args : Element, env : Any, workitem : Any) -> None:
        if args.is_nil():
            result = cls.report(state)
            env.deref()
            Element.deref_all(state, args)
            workitem.fin_value(result)
        elif isinstance(args, Cons):
            arg, rest = args.steal_children()
            workitem.new_continuation(Func(cls, None, state), rest, env)
            if not state.is_nil() and isinstance(arg, Cons) and isinstance(arg.val1, Symbol) and isinstance(arg.val2, Symbol) and arg.val1.val1 == 'q':
                # special case: when reporting, quoting a symbol is legal if it's not the value that will be returned
                workitem.fin_value(arg, arg.val2.bumpref())
            else:
                workitem.eval_arg(arg, env.bumpref())
        else:
            env.deref()
            Element.deref_all(state, args)
            workitem.error("argument to report is improper list")

    @classmethod
    def feedback(cls, state : Element, value : Element, args : Element, env : Any, workitem : Any) -> None:
        assert not isinstance(value, Error)
        workitem.new_continuation(Func(cls, None, Cons(value, state)), args, env)

@FuncClass.implements_API
class fn_userfunc(FuncClass):
    # state is:
    #   ( expr . (dangling . satisfied) )
    # dangling is a list of symbols
    # satisfied is a list of (expr . symbol) pairs

    @classmethod
    def step(cls, state : Element, args : Element, env : Any, workitem : Any) -> None:
        assert isinstance(state, Cons)
        expr, dangsat = state.steal_children()
        assert isinstance(dangsat, Cons)
        dangling, satisfied = dangsat.steal_children()

        if args.is_nil():
            env.deref()
            args.deref()
            if dangling.is_nil():
                # done!
                dangling.deref()
                workitem.eval_arg(expr, SymbolTable.from_list(satisfied))
            #elif self.params.is_cons() and self.params.val1.is_cons():
            #   XXX fill in default arguments
            else:
                Element.deref_all(expr, dangling, satisfied)
                workitem.error("insufficient arguments for user defined function")
        elif isinstance(args, Cons):
            if dangling.is_nil():
                env.deref()
                Element.deref_all(expr, dangling, satisfied, args)
                workitem.error(f"too many arguments for user defined functions {state}")
            elif isinstance(dangling, Cons) and isinstance(dangling.val1, Symbol):
                # XXX handle default arguments here too
                val, args = args.steal_children()
                myfunc = Func(cls, None, Cons(expr, Cons(dangling, satisfied)))
                workitem.new_continuation(myfunc, args, env)
                workitem.eval_arg(val, env.bumpref())
            else:
                env.deref()
                Element.deref_all(expr, dangling, satisfied, args)
                workitem.error("user defined function has non-symbol as param name?")
        else:
            env.deref()
            Element.deref_all(expr, dangling, satisfied, args)
            workitem.error("call to user defined function is not proper list")

    @classmethod
    def feedback(cls, state : Element, value : Element, args : Element, env : Any, workitem : Any) -> None:
        assert not isinstance(value, Error)

        assert isinstance(state, Cons)
        expr, dangsat = state.steal_children()
        assert isinstance(dangsat, Cons)
        dangling, satisfied = dangsat.steal_children()
        assert isinstance(dangling, Cons)
        toassign, dangling = dangling.steal_children()
        assert isinstance(toassign, Symbol)

        satisfied = Cons( Cons(value, toassign), satisfied )

        myfunc = Func(cls, None, Cons(expr, Cons(dangling, satisfied)))
        workitem.new_continuation(myfunc, args, env)

@dataclass
class Continuation:
    fn: Func
    args: Element           # (remaining) arguments to fn
    localsyms: SymbolTable

    def __repr__(self):
        return f"Continuation({self.fn}, {self.args})"

    def deref(self):
        self.fn.deref()
        self.args.deref()
        self.localsyms.deref()

@dataclass
class WorkItem:
    globalsyms: SymbolTable
    continuations: List[Continuation]
    dummylocalsyms: SymbolTable
    costleft: int = 100000

    @classmethod
    def begin(cls, sexpr, syms):
        wi = WorkItem(globalsyms=syms, continuations=[], dummylocalsyms=SymbolTable())
        wi.eval_arg(sexpr, wi.dummylocalsyms.bumpref())
        return wi

    def get_partial_func(self, value : Element) -> Optional[Element]:
        if isinstance(value, Func):
            if issubclass(value.val1[0], (fn_op, fn_partial)):
                return value
        value.deref()
        return None

    def new_continuation(self, fn : Element, args : Element, env : SymbolTable) -> None:
        if isinstance(fn, Error):
            self.fin_value(fn)
        else:
            assert isinstance(fn, Func)
            self.continuations.append(Continuation(fn, args, env))

    def fin_value(self, value : Element) -> None:
        self.new_continuation(Func(fn_fin, None, Atom(0)), value, self.dummylocalsyms.bumpref())

    def eval_arg(self, args : Element, env : SymbolTable) -> None:
        self.new_continuation(Func(fn_symbll_eval, None, Atom(0)), args, env)

    def error(self, msg):
        self.fin_value(Error(msg))

    def step(self) -> None:
        c = self.continuations.pop()
        fnobj, state = c.fn.steal_func()
        fnobj.step(state, c.args, c.localsyms, self)
        self.costleft -= 1
        if self.costleft <= 0 and self.continuations[-1].fn.val1[0] != fn_fin:
            self.error("cost overrun, aborting")
        if ALLOCATOR.x > 400000:
            self.error("memory overrun, aborting")

    def feedback(self, value : Element) -> None:
        if isinstance(value, Error):
            for c in self.continuations:
                c.deref()
            self.continuations = []

        if self.continuations:
            c = self.continuations.pop()
            fnobj, state = c.fn.steal_func()
            fnobj.feedback(state, value, c.args, c.localsyms, self)
        else:
            self.fin_value(value)

    def finished(self) -> bool:
        return len(self.continuations) == 1 and self.continuations[0].fn.val1[0] == fn_fin

    def get_result(self) -> Element:
        assert self.finished()
        r = self.continuations[0].args.bumpref()
        self.continuations.pop().deref()
        if r.is_bll() or r.is_error():
            return r
        else:
            err = Error(f"result was not bll {r}")
            r.deref()
            return err

def symbolic_eval(sexpr, globalsyms):
    wi = WorkItem.begin(sexpr, globalsyms)

    while not wi.finished():
        wi.step()

    return wi.get_result()

def ResolveIndex(symname, globalidx, localidx):
    s = localidx[symname]
    if s is None:
        s = globalidx[symname]
    if s is None:
        return s
    assert isinstance(s, SymbolInfo) and s.position is not None
    return s

def compile_args(args, globalidx, localidx):
    l = []
    while isinstance(args, Cons):
        l.append(compile_expr(args.val1, globalidx, localidx))
        args = args.val2
    l = SExpr.list_to_element(l)
    if not args.is_nil():
        l.deref()
        raise Exception("call via improper list")
    return l

def compile_expr(sexpr, globalidx, localidx):
    assert isinstance(sexpr, Element)
    assert isinstance(globalidx, SymbolIndex)
    assert isinstance(localidx, SymbolIndex)

    assert not sexpr.is_func() and not sexpr.is_error()

    if sexpr.is_nil():
        return sexpr.bumpref()
    elif sexpr.is_atom():
        return Cons(Atom(0), sexpr.bumpref())
    elif sexpr.is_symbol():
        s = ResolveIndex(sexpr.val2, globalidx, localidx)
        if s is None:
            raise Exception(f"invalid symbol {sexpr.val2}")
        return Atom(s.position)
    else:
        assert isinstance(sexpr, Cons) and isinstance(sexpr.val1, Symbol)
        symname = sexpr.val1.val2
        if symname == 'q':
            assert sexpr.val2.is_bll()
            return Cons(Atom(0), sexpr.val2.bumpref())
        elif symname == "report":
            if isinstance(sexpr.val2, Cons):
                return compile_expr(sexpr.val2.val1, globalidx, localidx)
            elif sexpr.val2.is_nil():
                # weird thing to do
                return compile_expr(sexpr.val2, globalidx, localidx)
            else:
                raise Exception(f"report with improper list {sexpr}")
        elif symname == 'if':
            assert sexpr.val2.is_cons()
            cond_expr = compile_expr(sexpr.val2.val1, globalidx, localidx)
            if not sexpr.val2.val2.is_cons():
                assert sexpr.val2.val2.is_nil()
                return SExpr.list_to_element([OpAtom("i"), cond_expr])
            elif not sexpr.val2.val2.val2.is_cons():
                assert sexpr.val2.val2.val2.is_nil()
                then_expr = Cons(OpAtom('q'), compile_expr(sexpr.val2.val2.val1, globalidx, localidx))
                i_expr = SExpr.list_to_element([OpAtom("i"), cond_expr, then_expr])
                return SExpr.list_to_element([OpAtom("a"), i_expr])
            elif not sexpr.val2.val2.val2.val2.is_cons():
                assert sexpr.val2.val2.val2.val2.is_nil()
                then_expr = Cons(OpAtom('q'), compile_expr(sexpr.val2.val2.val1, globalidx, localidx))
                else_expr = Cons(OpAtom('q'), compile_expr(sexpr.val2.val2.val2.val1, globalidx, localidx))
                i_expr = SExpr.list_to_element([OpAtom("i"), cond_expr, then_expr, else_expr])
                return SExpr.list_to_element([OpAtom("a"), i_expr])
            else:
                raise Exception("invalid if expression")
        elif symname == "partial":
            args = sexpr.val2
            if not isinstance(args, Cons):
                raise Exception("partial requires an argument")
            fn, rest = args.val1, args.val2
            l = compile_args(rest, globalidx, localidx)
            if isinstance(fn, Symbol) and fn.val2 in SExpr_FUNCS:
                return Cons(OpAtom(symname), Cons(Cons(Atom(0), OpAtom(fn.val2)), l))
            else:
                fn = compile_expr(fn, globalidx, localidx)
                return Cons(OpAtom(symname), Cons(fn, l))
        elif symname in SExpr_FUNCS:
            l = compile_args(sexpr.val2, globalidx, localidx)
            return Cons(OpAtom(symname), l)
        else:
            s = ResolveIndex(symname, globalidx, localidx)
            if s is None:
                raise Exception("invalid symbol")
            loc_l = Cons(OpAtom('b'), compile_args(sexpr.val2, globalidx, localidx))
            globloc_l = [OpAtom('rc'), loc_l, Atom(2)]
            a_l = [OpAtom('a'), Atom(s.position), SExpr.list_to_element(globloc_l)]
            return SExpr.list_to_element(a_l)

def compile_fn(symname, globs, globidx):
    loc = SymbolTable()
    if isinstance(globs.syms[symname], Element):
        sexpr = globs.syms[symname]
    else:
        params = globs.syms[symname][0]
        while params.is_cons():
            if params.val1.is_symbol():
                loc.set(params.val1.val2, Atom(0))
            else:
                raise Exception("function parameters aren't symbols")
            params = params.val2
        sexpr = globs.syms[symname][1]
    x = compile_expr(sexpr, globidx, SymbolIndex(loc, offset=3))
    loc.deref()
    return x

def compile_program(symname, globalsyms):
    # (a (q a N) (rc 1 (b GLOBALS)))

    assert isinstance(symname, str)
    assert isinstance(globalsyms, SymbolTable)
    assert symname in globalsyms.syms

    globidx = SymbolIndex(globalsyms, offset=2)
    b_lst = [OpAtom('b')]
    for globsym in globidx:
        globex = compile_fn(globsym, globalsyms, globidx)
        b_lst.append(Cons(OpAtom('q'), globex))

    rc_lst = [OpAtom('rc'), Atom(1), SExpr.list_to_element(b_lst)]
    in_lst = [OpAtom('q'), OpAtom('a'), Atom(globidx[symname].position)]
    fin_lst = [OpAtom('a'), SExpr.list_to_element(in_lst), SExpr.list_to_element(rc_lst)]

    return SExpr.list_to_element(fin_lst)
