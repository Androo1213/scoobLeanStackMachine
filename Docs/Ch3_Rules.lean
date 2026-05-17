import VersoManual
import VersoManual.InlineLean
import Docs.Ch2_Equiv

set_option autoImplicit false
set_option tactic.hygienic false
set_option verso.code.warnLineLength 0

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open LoVe.ScoobMiniMachine

#doc (Manual) "Rewrite rules" =>

These are 8 per rule equic theorems, which help for the optimiser (covered next). Each loks through 2/3 instuctions and then shows its equivalent to some different (shorter) for under prev defined ~.

All have arithmetic except `push_pop` which is fine to close which bare simp closes. All others leave an arith identidy which ring
is super convienient for finishing off. `comm_swap` and `mul_zero` have cases for when there's underflow as simp wasn't able push through.

The underflow errors were rather interesting. For example when there were: `(push (lit 0), add) ~ ()` or like
`(push (lit 1), mul) ~ ()`, and `[dup, add] ~ (push (lit 2), mul)` all go to false on the empty stack, so push succeeds leading to add and mul underflowing,
so LHS is left with something akin to `(lit 0)`, but, the RHS will just be empty. So, parameterising each side with `(e : expr)`, and prepending
push e to both sides, made a 3 instr window hold on every stack.

These aren't too complicated to write, it was just trying out intro env stack; simp (eval) and then seeing if it closes, and if not looking to see what identities sit inside, which were often just arithmetic ones, closed by ring. In the case where simp can't progress some underflow-esque goal, openening cases stack adn cecursing into nil and cons branches worked. 

```lean
namespace LoVe
namespace ScoobMiniMachine

/-
'DCE'. But push pop does result in nothing. Detection is in `optimise`, both sides go to `stack.map (eval env)`
ergo simp adquete in closing.
-/
theorem push_pop (e : Expr) : [Instr.push e, Instr.pop] ~ [] := by
  intro env stack
  simp

/-
These optimisations need normalisation to be more interesting than just definitional
reduction. So the prior lemmas unfold both `step`&`exec`, and then simp on `[eval]` which kicks recursion
through `Expr`. From oh: `ring` + `omega`, super nice for closing just arithimic
identities. Go back to hitchikers Normalization Tactics & love13 in the end, nice for seeing this.
Also similar to `simp [add, ih]` with `ring` finishes off isntead of bare simp.

Also, considered linarith from 6, but, think in constant folding say:
`x* y = y*x` is polynomial w/ deg of 2, and ring works even if not linear.

This started as `[push (lit 0),add] ~ []` or `[dup, add] ~ [push (lit 2), mul]`, but I had problems
with these being false on empty staacks. Since `push` is guarenteed to happen, LHS, leaves `lit 0`
on the stack, leading `add` to underflow just leaving `[lit 0]` on the stack, while RHS is `[]`.
Fix was to just add `[push e]` on either side, and with the real operand, any stack will let equiv
hold. Also, looking back, this better matches the optimisers 3 instruction window.
-/

theorem add_zero (e : Expr) :
    [Instr.push e, Instr.push (Expr.lit 0), Instr.add] ~ [Instr.push e] := by --adding zero does nothing
  intro env stack
  simp [eval]

theorem mul_one (e : Expr) :
    [Instr.push e, Instr.push (Expr.lit 1), Instr.mul] ~ [Instr.push e] := by -- multiplying by one is the same as doing nothing
  intro env stack
  simp [eval]

/-
Process for figuring out these is not bad. Take optimisation idea, put it into stack machine language
immedietly go for:
:= by
  intro env stack
  simp [eval]
if goal closed, as above, yay. If not, there were 3 branches.
  - Some arithmetic identity,: then ring can just close out
  - Some case split: then think about base nil cases and cons cases, to get back to `simp [eval]` + `ring`
  - in unfoldable cases for simp, needed to add more lemma names to simp like otherDef.
 -/
theorem add_comm_swap : [Instr.swap, Instr.add] ~ [Instr.add] := by  -- swapping before add is pointless, commutes
  intro env stack
  cases stack with
  | nil => rfl-- both sides underflow, so return []
  | cons top₁ rest₁ =>
    cases rest₁ with
    | nil => rfl -- wiht only one elem on stack both underflow go back up to  [top₁]
    | cons top₂ rest₂ =>
      -- ring closes out `top₂ + top₁ = top₁ + top₂`
      simp [eval]
      ring

theorem strength_reduce (e : Expr) :
    [Instr.push e, Instr.dup, Instr.add] ~ [Instr.push e, Instr.push (Expr.lit 2), Instr.mul] := by
  intro env stack
  -- ring closes out arithmetic identity: `eval e + eval e = 2 * eval e`
  simp [eval]
  ring

theorem const_fold_add (a b : ℤ) :
    [Instr.push (Expr.lit a), Instr.push (Expr.lit b), Instr.add] ~ [Instr.push (Expr.lit (a + b))] := by
  intro env stack
  --LHS has `add b a` (b pushed last, so b on top) while RHS has `a + b`, and ring can close commutativity `b + a = a + b`
  simp [eval]
  ring

theorem const_fold_mul (a b : ℤ) :
    [Instr.push (Expr.lit a), Instr.push (Expr.lit b), Instr.mul] ~ [Instr.push (Expr.lit (a * b))] := by
  intro env stack
  -- same as add but mul version: `b * a =a * b`
  simp [eval]
  ring

/-
Needed `cases stack` since with `[]`, LHS pushes `0`, mul underflows which leaves [lit 0], and
RHS pop underflows so then push 0 leaves `[li 0]`. Since both reduce to [lit 0] `rfl` can close nil case.
On cons, `simp [eval]` reduces step/exec w/ prior lemmas and then simp [eval] just works.
-/
theorem mul_zero :
    [Instr.push (Expr.lit 0), Instr.mul] ~ [Instr.pop, Instr.push (Expr.lit 0)] := by
  intro env stack
  cases stack with
  | nil => rfl
  | cons head tail =>
    simp [eval]

end ScoobMiniMachine
end LoVe
```
