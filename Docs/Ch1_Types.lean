import VersoManual
import VersoManual.InlineLean
import LoVe.LoVelib

set_option autoImplicit false
set_option tactic.hygienic false
set_option verso.code.warnLineLength 0

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

namespace LoVe.ScoobMiniMachine
end LoVe.ScoobMiniMachine

open LoVe.ScoobMiniMachine

#doc (Manual) "Types and interpreter" =>

Here the language gets set up: a symbolic expression type Expr (lit/var/add/mul), as well as a simple environment Env := String → ℤ, a
recursive evaluation interpreter, a btyecode type Instr with the 6 allowed instructions.

With stacks holding Expr trees, something even mildly intresting can come out and be asserted rather than something purely numerical based.

There are eight `\@[simp]` step_X / exec_Y lemmas. Each proves via rfl which consideres definitional equality, and `\@[simp]` allows for all later proof rewrites to auto go through them.
Instead of relational semantics, functional helps get closer to a denotational flavor, helping the next sections per-rule proofs line or two of simp.

Also underflow `(| _, stack => stack)` helps for `add_zero`, `mul_one`, etc. to be stated over a 3 instruction scope rather than 2.

```lean
namespace LoVe
namespace ScoobMiniMachine

/-
`Expr`: is type ∀things that live ∈ our stack
Just`AExp` ∈ love2 w/o the div/sub extras
inductive AExp : Type where
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp
but w/ did literals since this makes more sense-/
inductive Expr : Type where
  | lit : ℤ → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  deriving Repr /-For #eval print expressions-/

/- `Env` just maps string var names to int val Same as AExp
 Note no, mutability, just reading from  env but no writing.-/
def Env : Type := String → ℤ

/-
  `eval env e` interprets symbolic expresions w/ an env to get an int
  (since `programs` can only do the simplest of math)
  Just like love2's eval -/
def eval (env : Env) : Expr → ℤ
  | Expr.lit litValue => litValue
  | Expr.var varName => env varName
  | Expr.add leftExpr rightExpr => eval env leftExpr + eval env rightExpr
  | Expr.mul leftExpr rightExpr => eval env leftExpr * eval env rightExpr

/-
  Since each `instr` is an instruction, a program can be though of as a `List Intrsution`
  All valid instructions for now are:
  - `push e`: put e onto the stack
  - `add`: pop our first two elemtents on the stack and replace with their sum
  - `mul`: pop our first two elemtents on the stack and replace with their product
  - `dup` : pushes top element on the program stack.
  - `pop`: throws away the top element of the stack
  - `swap`: swaps first two elements on teh stack.
  Almost the same as `Stmt` ∈ love9 but 'bytecodey' -/
inductive Instr : Type where
  | push : Expr → Instr
  | add  : Instr
  | mul  : Instr
  | dup  : Instr
  | pop  : Instr
  | swap : Instr
  deriving Repr

/-
`step i stack` executes one instruction on the stack, and gives back updated stack.
  TODO: Add erroring for if there isn't enough args to complete a swap, add, mul etc.
-/
/-
universial relaion not a function, each constructor
  -under these premises, this program ends in this state.
  step i guess is functional analogue for one bytecode instruction
  (probably more similar to `SmallStep` than bug
  `exec` — running a whole program to completion, is what's similar to bigstep
-/
def step (instr : Instr) (stack : List Expr) : List Expr :=
  match instr, stack with
  | Instr.push newExpr, stack =>
      newExpr :: stack
  --for add: take top two, then just replace with sum
  | Instr.add, topExpr :: nextExpr :: rest =>
      Expr.add topExpr nextExpr :: rest
  --take the top two, then just with product
  | Instr.mul, topExpr :: nextExpr :: rest =>
      Expr.mul topExpr nextExpr :: rest
  --dup copies top element so it appears twice
  | Instr.dup, topExpr :: rest =>
      topExpr :: topExpr :: rest
  | Instr.pop, _ :: rest =>
      rest
  | Instr.swap, topExpr :: nextExpr :: rest =>
      nextExpr :: topExpr :: rest
  --catch all gets stack underflow placeholder for now is just to do nothing
  | _, stack =>
      stack

/-
  `exec prog stk` runs the whole program starting stack left folding `step` for every instr threading stack through
  `(β → α → β) → β → List α → β` for foldl, so needs stack/accumulator first, then elem/instr,
  should get forwarded to step in right order then..., need to swap
  Also just for foresight `foldl` will guarentee for example:
  `exec (xs ++ ys) stk = exec ys (exec xs stk)`
  so this will be good for correctness.
-/
def exec (program : List Instr) (stack : List Expr) : List Expr :=
  program.foldl (fun currentStack nextInstr ↦ step nextInstr currentStack) stack

/-
Step & Exec lemmas. Helpful to tag so they automatically fire in later proofs.
Same pattern as bigstep ∈ love9, and hitchhicker bigStep_assign_Iff and following.
  Just cleaned up everything a ton rather than simp'ing every step ∨ unfold step to open up defs.
and opens up composibility with `exec_cons` & `exec_nil`

Take push: if one does `step (Instr.push exp) stack`, then `Instr.push newExpr, stack`
catches producing: ` => newExpr :: stack`. Thus, the goal `step (Instr.push exp) stack =e :: stack`
goes to `e::stack = e::stack` post reduction, so rfl to unfold . All other instructions follow this pattern.
-/
@[simp] theorem step_push (e : Expr) (stack : List Expr) :
    step (Instr.push e) stack = e :: stack :=
  rfl
@[simp] theorem step_add (a b : Expr) (rest : List Expr) :
    step Instr.add (a :: b :: rest) = Expr.add a b :: rest :=
  rfl
@[simp] theorem step_mul (a b : Expr) (rest : List Expr) :
    step Instr.mul (a :: b :: rest) = Expr.mul a b :: rest :=
  rfl
@[simp] theorem step_dup (a : Expr) (rest : List Expr) :
    step Instr.dup (a :: rest) = a :: a :: rest :=
  rfl
@[simp] theorem step_pop (a : Expr) (rest : List Expr) :
    step Instr.pop (a :: rest) = rest :=
  rfl
@[simp] theorem step_swap (a b : Expr) (rest : List Expr) :
    step Instr.swap (a :: b :: rest) = b :: a :: rest :=
  rfl

/-
`exec` is really just folding left. This can either result in base case, which is
`[]`, or `instru :: rest`.
`exec` is really just leftfolding down the stack, on `[]` reduces to `stack`, acts as base case
`exec_cons` for all else. `exec` is just leftfolding down the stack, foldl on `instr :: rest`
takes the head applies step, and recurses on rest.
-/
@[simp] theorem exec_nil (stack : List Expr) :
    exec [] stack = stack :=
  rfl
@[simp] theorem exec_cons (instr : Instr) (rest : List Instr) (stack : List Expr) :
    exec (instr :: rest) stack = exec rest (step instr stack) :=
  rfl

end ScoobMiniMachine
end LoVe
```
