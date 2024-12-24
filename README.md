
# bllsh - A bullish shell for a bitcoin lisp language

![](bllsh-beach-sml.jpg)

## bll - The Basic Bitcoin Lisp Language

To start: bll is the basic bitcoin lisp language. Programs in this
language are created by the combination of two concepts: atoms and pairs;
atoms are byte-strings, and pairs are two elements, each of which may
be an atom or a pair. A list is either the zero-length byte string
(aka nil), or a pair, of which the second element is also a list.

Any expression can be treated as a program and evaluated. The result of
evaluation an expression is:

 * if the expression is nil, the result is nil
 * if the expression is some other atom, the result is the value in the environment
   keyed upon the atom if it exists, or an error
 * if the expression is a pair, and its first element is nil, the result is
   the second element (this is called "quoting" the second element)
 * otherwise, the expression must be a list, and the first element must
   be an atom that is the numeric id of a valid opcode, and the remainder
   of the list are treated as the arguments for that opcode, after being
   evaluated themselves. (the result of the expression is determined by
   the opcode)

### Opcodes

The following special opcodes are defined:

 * `(q . X)` aka `(nil . X)` -- quote operation, returning X literally
 * `(a EXPR ENV)` -- evaluate EXPR with ENV as its environment
 * `(sf XX)` -- softfork behaviour; unimplemented
 * `(partial FN ARGS)` -- partial application of normal opcodes (`X=(partial + 1 2 3)`; `Y=(partial + 4)`; `10=(partial Y)`)

The following normal opcodes are defined:

 * Control flow:
   * `(x MSG...)` -- abort evaluation, returning an error
   * `(i COND THEN ELSE)` -- eager evaluated if (THEN defaults to 1, ELSE defaults to nil)

 * Lists:
   * `(rc A B C...)` -- construct a list in reverse (`(rc A B C)` results in `(C B . A)`)
   * `(h L)` -- return the head of a list (first item in the pair)
   * `(t L)` -- return the tail of a list (second item in the pair)
   * `(l E)` -- return 1 if E is a pair, 0 otherwise
   * `(b A B C...)` -- construct a left-biased balanced tree from its arguments

 * Logic:
   * `(not A B C...)` -- logical nand of the arguments, defaults to nil (nil is false, any other atom is true; non atoms cause an error; returns nil, 1 or an error)
   * `(all A B C...)` -- logical and of the arguments, defaults to 1
   * `(any A B C...)` -- logical or of the arguments, defaults to nil

 * Strings:
   * `(= A B C...)` -- are all the arguments equal (non-atoms result in an error)
   * `(<s A B C...)` -- are the arguments strictly increasing, lexically
   * `(strlen A)` -- what is the size of A
   * `(substr A START END)` -- the substring of A starting at START, ending at END
   * `(cat A B C...)` -- a new atom composed of the contents of the
     arguments concatenated

 * Bitwise:
   * `(~ A B C...)` -- bitwise nand of the arguments
   * `(& A B C...)` -- bitwise and of the arguments
   * `(| A B C...)` -- bitwise or of the arguments
   * `(^ A B C...)` -- bitwise xor of the argumnets

 * Maths: (numbers are encoded as little-endian with a sign bit)
   * `(+ A B C...)` -- sum the arguments
   * `(- A B C...)` -- if a single argument, negate it; otherwise subtract the second, third etc argument from the first
   * `(* A B C...)` -- multiply the arguments
   * `(% N D)` -- the remainder of N divided by D
   * `(< A B C...)` -- arguments are strictly increasing when treated as numbers

 * List encoding: (broken)
   * `(rd ENCODING)` -- convert an encoded string into an expression
   * `(wr EXPR)` -- convert an expression into an encoded string

 * Cryptographic hashing:
   * `(sha256 A B C...)` -- calculate the sha256 hash of the arguments
   * `(ripemd160 A B C...)` -- calculate the ripemd160 hash of the arguments
   * `(hash160 A B C...)` -- shorthand for `(ripemd160 (sha256 A B C...))`
   * `(hash256 A B C...)` -- shorthand for `(sha256 (sha256 A B C...))`

 * Elliptic curve cryptography:
   * `(secp256k1_muladd A (B) (C . P) (1 . Q) (nil . R)...)` -- multiple secp256k1 points by a scalar, sum them, and return 1 if the evaluate to the point at infinity; otherwise return an error. The example here is equivalent to `A*G - B*G + C*P + 1*Q - 1*R = O` where `O` is the point at infinity.
   * `(bip340_verify PUBKEY MSG SIG)` -- perform BIP 340 verification; returns nil if SIG is nil; 1 if verification succeeds; otherwise results in an error
   * `(ecdsa_verify PUBKEY MSG SIG)` -- perform ECDSA signature verification

 * Transaction introspection:
   * `(tx N...)` -- extract various bits of information about the tx being verified
   * `(bip342_txmsg SIGHASH)` -- calculate the message digest for the tx; script's `SIG PUBKEY OP_CHECKSIG` is roughly equivalent to `(bip340_verify PUBKEY (bip342_txmsg (substr SIG '64) (substr SIG 0 64)))`

## symbll - The Symbolic Bitcoin Lisp Language

Writing code for bll is kind-of a pain; working with the environment
is annoying, and having to quote things by pairing them with nil to
encode literals is also annoying. To ameliorate this, we introduce a
second language that's designed to be easier to program in while also
being straightforward to translate to bll. We call this language symbll;
which is intended to be reminiscent of "simple" or "symbol", and is
pronounced like "cymbal".

Expressions in the language may be symbols, atoms or pairs; with atoms
being the same as in bll, symbols being alphanumeric strings, and pairs
consist of two sub-expressions, which can each be either symbols, atoms
or pairs. A list is either the empty atom, or a pair of which the second
sub-expression is a list.

As far as evaluating symbll expressions goes, the first major change in
comparsion to bll expressions is that the "environment" is replaced by
a symbol table, mapping symbols to functions/values. The second is that
atoms are always treated as literal values, and opcodes/etc are always
referenced via a symbol (ie, identified by name rather than a numeric id).

### Symbols

There are symbols for each of the normal bll opcodes listed above.

Additionally, there are the following special symbols:

 * `(q . X)` -- quoting
 * `(sf XX)` -- softfork behaviour; unimplemented
 * `(partial XX)` -- partial application
 * `(if COND THEN ELSE)` -- lazily evaluated version of `(i ...)`
 * `(report VAL NOTES...)` -- prints the value of its arguments on stdout, and
   returns its first argument, used for debugging
 * `(qq ... (uq . Y) ..)` -- quasi-quoting and unquoting, intended to replace
   having to manually construct structures with `(rc ...)`; unimplemented

And beyond that, you can define your own symbols which may be expressions or
functions taking their own parameters.

## bllsh - The shell/REPL

That brings us to the bll shell, bllsh, which is, of course, pronounced
"bullish".

It's designed to allow evaluation of both symbll and bll expressions. It
offers the following commands:

 * Evaluation:
   * `eval SYMBLL` -- evaluate a symbll expression
   * `blleval BLL ENV` -- evaluate a bll expression, with an optional environment
     (note, for convenience, blleval will translate the names of bll
     opcodes to their corresponding numeric ids; this only applys to the BLL argument)

 * Symbol definition:
   * `def A SYMBLL` -- define a symbll symbol
   * `def (A X Y Z...) SYMBLL` -- define a symbll function with parameters
   * `undef A` -- remove the definition of a symbll symbol

 * Transaction context:
   * `tx` -- provide the hex encoded tx
   * `tx_in_idx` -- provide the decimal index of the tx input being validated
   * `tx_script` -- provide the hex encoded script (for signature validation/introspection; does not otherwise affect symbll/bll evaluation)
   * `utxos` -- provide hex serialized CTxOut object for the utxos being spent, separated by spaces

 * Debugging:
   * `debug SYMBLL` -- begin debugging a symbll expression
   * `blldebug BLL ENV` -- beging debugging a bll expression
   * `step` -- take one step forward in the evaluation
   * `next` -- step through any sub evaluations
   * `cont` -- finish evaluating
   * `trace` -- finish evaluating, but print every step taken

 * Compilation:
   * `compile SYMBLL` -- compile a symbll expression to bll code (symbols compile to env references)
   * `program SYMBLL` -- compile a symbll expression to a bll program that populates its own environment with any global symbol definitions
   * `program @SYMBOL` -- compile the symbll global into a bll program

 * Convenience:
   * `import PATH` -- import and run code from a given file

## Implementation details

### Element

The Element class and its sublasses (Cons, Atom, Symbol, Error, Func)
manage the different types of data that make up bll and symbll programs,
as well as their execution state (with Symbol only being used by symbll
programs).

### Allocator

The Allocator is used to tracks the memory usage needed by Elements
during program execution.

### SExpr

Given a string defining a program, SExpr.parse() will turn it into
a list.

### Continuations

The evaluation model is roughly continuation passing style; that is when
evaluation `(* 2 3)` in the symbll expression `(+ 1 (* 2 3) 4)`, we have
a "work item" that is `(* 2 3)` which we will eventually evaluate as
`6`, and its continuation which is `op_add(1)` ("we are adding things,
and the total so far is 1") and `(4)` ("once we've dealt with the current
thing, we need to evaluate one more item, namely 4").

This makes step-through debugging easy, handles tail-recursion
optimisation well, allows handling errors/exceptions fairly well, and
makes it easy to track resource usage.

See the `WorkItem` and `Continuation` classes, as well as things decorated
with `@FuncClass.implements_API`.

### Special Opcodes

All opcodes are ultimately implemented by a `@FuncClass.implements_API` class.
These provide two functions:

 - `step()` which do a single unit of work one one or more pending
   arguments of the opcode. Often that work is simply delegation, eg
   when the addition opcode sees `(* 2 3)` as its next argument, it needs
   that expression evaluated into the value `6` before it can do anything.
 - `feedback()` which accepts the result of delegated work and processes it.

### Normal Opcodes

Most opcodes behave in a similar way, always delegating their arguments
to be evaluated, and only doing work on the result, with perhaps some
finalisation once there are no further arguments. This common behaviour
is handled via `fn_op` in workitem.py, with the actual opcode behaviour
implemented in opcodes.py.

### Example

We can calculate a factorial recursively or iteratively. Recursively,
this looks like:

```
def factorial_recursive(n):
    if n == 0:
        return 1
    else:
        return n * factorial_recursive(n-1)
```

This is not amenable to tail recursion, so builds up a stack of n elements
(n, n-1, n-2, ..) then multiplies them together.

Done tail-recursively, it looks like:

```
def factorial_tail_recursive(n, accumulator):
    if n == 0:
        return accumulator
    else:
        return factorial_tail_recursive(n-1, n*accumulator)
```

With tail-recursion optimisation, this becomes equivalent to:

```
def factorial_iterative(n, accumulator):
    while n != 0:
        n, accumulator = n-1, n*accumulator
    return accumulator
```

We implement the plain recursive version as follows:

```
>>> def (FR N) (if N (* N (FR (- N 1))) 1)
>>> eval (FR 5)
120
```

This becomes the following bll program:

```
>>> program FR
(1 (nil 1 2) (6 1 (10 (nil 1 (5 3 (nil 25 3 (1 2 (6 (10 (24 3 (nil . 1))) 2))) (nil nil . 1))))))
```

The tail-recursive version looks like:

```
>>> def (FTR N ACC) (if N (FTR (- N 1) (* N ACC)) ACC)
>>> eval (FTR 5 1)
120
```

This becomes the following bll program:

```
>>> program FTR
(1 (nil 1 2) (6 1 (10 (nil 1 (5 5 (nil 1 2 (6 (10 (24 5 (nil . 1)) (25 5 7)) 2)) (nil . 7))))))
```
