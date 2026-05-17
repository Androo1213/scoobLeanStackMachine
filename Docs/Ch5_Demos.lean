import VersoManual
import VersoManual.InlineLean
import Docs.Ch4_Optimiser

set_option autoImplicit false
set_option tactic.hygienic false
set_option verso.code.warnLineLength 0

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open LoVe.ScoobMiniMachine

#doc (Manual) "Demos" =>

_TODO_

```lean (name := evalRaw)
/-
Demos now!
`#eval`s  have `optimise` actually firing on 'programs'.
So
  1) each pair runs prog with `exec` first to get naive stack
  2) then `optimise` on the program to get collpased stack.
  3) finally `optimise_sound` shows that two forms are guaranteed `~`-equivalent for all envs/starting stack.
  `#check @optimise_sound` at the bottom prints the full theorem signature.
  So for example
  `push 2, push 3, add, push 0, add, push 1, mul`  just does `((2+3)+0)*1`
  Optimisations ought to ake this actually look like:
    const_fold_add → `[push 2, push 3, add, …]` → `push 5`;
    const_fold_add → `[push 5, push 0, add, …]` → `push 5`
    const_fold_mul → `[push 5, push 1, mul]` → `push 5`
  So then one gets `[push 5]`.
Structural, and would work under just the diea of strucural equality w/in stacks, and was original proposal.
-/

/- `mul 1 (add 0 (add 3 2))`. -/
#eval exec
  [ Instr.push (Expr.lit 2), Instr.push (Expr.lit 3), Instr.add
  , Instr.push (Expr.lit 0), Instr.add
  , Instr.push (Expr.lit 1), Instr.mul]
  []
```

```leanOutput evalRaw (allowDiff := 10000)
_
```

```lean (name := evalOpt)
--Post `optimise` → `[Instr.push (Expr.lit 5)]`
#eval optimise
  [ Instr.push (Expr.lit 2), Instr.push (Expr.lit 3), Instr.add
  , Instr.push (Expr.lit 0), Instr.add
  , Instr.push (Expr.lit 1), Instr.mul]
```

```leanOutput evalOpt (allowDiff := 10000)
_
```

```lean (name := evalOptExec)
/- And running THAT optimised program on `[]` gives the same value
   you'd get by evaluating the unoptimised output under any env:
   `[lit 5]` literally — no symbolic tree, just the constant.
   `optimise_sound` certifies the two `#eval`s above are `~`-equivalent. -/
#eval exec (optimise
  [ Instr.push (Expr.lit 2), Instr.push (Expr.lit 3), Instr.add
  , Instr.push (Expr.lit 0), Instr.add
  , Instr.push (Expr.lit 1), Instr.mul ]) []
```

```leanOutput evalOptExec (allowDiff := 10000)
_
```

```lean (name := evalSymAdd)
/- 'Symbolic' programs With addition of .map (eval env) projection in Equiv,
along with with the ∀ env quantifier in front of it.-/

/-add 0 to any symbol like `[push x, push 0, add]` should boild down to `[push x]`. -/
#eval optimise
  [ Instr.push (Expr.var "x") , Instr.push (Expr.lit 0) , Instr.add ]
```

```leanOutput evalSymAdd (allowDiff := 10000)
_
```

```lean (name := evalSymMul)
-- Similarly, `[push x, push 1, mul]` ought to `[push x]`
#eval optimise
  [ Instr.push (Expr.var "x") ,Instr.push (Expr.lit 1) ,Instr.mul ]
```

```leanOutput evalSymMul (allowDiff := 10000)
_
```

```lean (name := evalPushPop)
/- push_pop on any literal ought to go to`[]`. -/
#eval optimise [ Instr.push (Expr.lit 7), Instr.pop ]
```

```leanOutput evalPushPop (allowDiff := 10000)
_
```

```lean (name := evalCombined)
/- Constant folding down to add_zero on a lit:
   - `[push 2, push 3, add, push x, push 0, add,pop]`
   - const_fold_add: `[push 5, push x, push 0, add, pop]`
   - add_zero (w/ e =var "x"): `[push 5,push x, pop]`
   - push_pop (popping the just-pushed `x`): `[push 5]`
   Should be: `[push 5]`.
-/
#eval optimise
  [ Instr.push (Expr.lit 2), Instr.push (Expr.lit 3), Instr.add,
  Instr.push (Expr.var "x"),Instr.push (Expr.lit 0), Instr.add,
  Instr.pop]
```

```leanOutput evalCombined (allowDiff := 10000)
_
```

```lean (name := checkSound)
#check @optimise_sound
```

```leanOutput checkSound (allowDiff := 10000)
_
```
