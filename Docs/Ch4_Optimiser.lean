import VersoManual
import VersoManual.InlineLean
import Docs.Ch3_Rules

set_option autoImplicit false
set_option tactic.hygienic false
set_option verso.code.warnLineLength 0

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open LoVe.ScoobMiniMachine

#doc (Manual) "Optimiser" =>

_TODO_

```lean
namespace LoVe
namespace ScoobMiniMachine

/-
It can be apprciated that the proofs are not exceedingly verbose since denotional-style relations
were chosen. Hitchhickers puts why not following love9 was quite nice actually:
    "Notice how the denotational semantics leads to short proofs by rewriting. This
    should not be surprising, given that it is designed to be equational and composi-
    tional. If we had used the big-step semantics as the basis for program equivalence
    instead, these proofs would have been much more complicated."

Originally, I proposed using structural stack equality, though, while the extremely simple equivlance
definition, any sort of neat optimisation fails, and only strucutre preserving ones i,e push_pop would work.
I am glad though not to have used bigstep equivlance even though it'd be nice to copy over `seq_congr`,
but it would've been a pain to a) build a whole separate relational semantics that and prove it agrees with
exec since `exec` is reliant on  `foldl`. I also think instead of `simp [eval]` spamming, prior proofs would
be ardous `cases run` proofs.

Though short, this lemme allows for local rewrites to lift to global rewrites, and really
allows for soundness property instead of some alternative where all programs needed to be (mostly) three
intructions long.

I think too this could've been done as `induction xs generalizing stack with` like in love9, but
simp makes this shorter. Really what this is similar in structure to though is `map_append` from hitchikers
though here `exec` is just `foldl` dressed up, instead of being recursive on primitives like in map.
Anyways, this means that simp can close out instaed of writing induction out.
-/

theorem exec_append (xs ys : List Instr) (stack : List Expr) : -- `xs ++ ys` is the same as running `xs` then `ys` on result
    exec (xs ++ ys) stack = exec ys (exec xs stack) := by
  simp [exec, List.foldl_append]

/-
Since `Equiv` is eval-equivalence, and structural, rewrites (like add_zero)
make stacks which are different structurally and eval to the same value.
So to extend some rewrite which is local into a global context it must be true that whatever comes
after presreves the evaluatory equivalence.

So: if `s₁.map eval =s₂.map eval`, then it must be true that for any well-formed instruction
`instr`, `(step instr s₁).map eval = (step instr s₂).map eval` whcich be induction holds
for `exec` on some program `prog`.

This is was just the congruence properties from hitchhiker's,
and `exec_map_eval_eq` provides the stackmachiney version of the `DenoteEquiv.seq_congr`
denotationatl equivalence rules. Also quite similar to love13 with simp to write through
step & sec since its not just definitional equlality.
-/

theorem step_map_eval_eq (env : Env) (i : Instr) (s₁ s₂ : List Expr)
    (h : s₁.map (eval env) = s₂.map (eval env)) :
    (step i s₁).map (eval env) = (step i s₂).map (eval env) := by
  cases i with
  | push e =>
    simp_all [step, eval]
  | add =>
    -- more than 2 elems needed for these to go, mismatched contradict h, simp all can close reictly
    cases s₁ with
    | nil => cases s₂ <;> simp_all--s₁ =[], only s₂ = [] gets out of h
    | cons _ r₁ =>
      cases s₂ with
      | nil => simp_all -- now s₁ nonempty while s₂ =[] so h false.
      | cons _ r₂ =>
        --both not empty so split tails, land on [a] vs a::b::r cases
        cases r₁ <;> cases r₂ <;> simp_all [step, eval]
  | mul =>
    -- `*` instead of `+` in eval
    cases s₁ with
    | nil => cases s₂ <;> simp_all
    | cons _ r₁ =>
      cases s₂ with
      | nil => simp_all
      | cons _ r₂ => cases r₁ <;> cases r₂ <;> simp_all [step, eval]
  | dup =>
    -- requires more than 1, goes to 4: nil on nil, nil cons, cons nil, cons on cons.
    cases s₁ <;> cases s₂ <;> simp_all [step]
  | pop =>
    cases s₁ <;> cases s₂ <;> simp_all [step]
  | swap =>
    -- similar to add & mul, however only sturucal, no reordering
    cases s₁ with
    | nil => cases s₂ <;> simp_all
    | cons _ r₁ =>
      cases s₂ with
      | nil => simp_all
      | cons _ r₂ => cases r₁ <;> cases r₂ <;> simp_all [step]

/-
Now, whole program can use `step_map_eval_eq` via induction on `p`, and needed for
following congurence lemmas.

quite similar from love5 zip length, generalise effect by introing on `p` before induction
so `s₁ s₂ h` are ∀-quantified in goal.
-/
theorem exec_map_eval_eq (env : Env) :
    ∀ (p : List Instr) (s₁ s₂ : List Expr),
      s₁.map (eval env) = s₂.map (eval env) →
      (exec p s₁).map (eval env) = (exec p s₂).map (eval env) := by
  intro p
  induction p with
  | nil => intros s₁ s₂ h; simpa using h
  | cons i p' ih =>
    intros s₁ s₂ h
    simp_all
    exact ih (step i s₁) (step i s₂) (step_map_eval_eq env i s₁ s₂ h)

/-
Now need to lift ~ into larger context. Sort of like `DenoteEquiv.seq_congr`.
-/

theorem Equiv.append_right {xs ys : List Instr} (rest : List Instr) (h : xs ~ ys) :
    -- rewrite L & RHS via exec_append so goal compares running `rest`  on `exec xs stack` vs `exec ys stack`
    xs ++ rest ~ ys ++ rest := by
  intro env stack
  rw [exec_append, exec_append]
  --`h env stack` -> prefix stacks are equal, exec_map_eval_eq then lifts equality across, running rest on both
  exact exec_map_eval_eq env rest (exec xs stack) (exec ys stack) (h env stack)

theorem Equiv.cons_congr (i : Instr) {xs ys : List Instr} (h : xs ~ ys) :
    i :: xs ~ i :: ys := by
  intro env stack
  --L & RHS start w/ `step i stack` then run xs/ys on same input
  rw [exec_cons, exec_cons]
  exact h env (step i stack)

/-
Soundness helpers. Before, each rewrite theorem had a scope of mostly 3 instructions. So
optimiser carries out that rewrite when one such pattern is detected at head of some `prog`.
Helpers here are convienient for appling `Equiv.append_right` to lift optimisation rewrite
from only detecting scope, to now being able to work with window followed by whatever

Everything here is essnetially completing opt_* from 11.8.

Definitional reduction `[a, b, c] ++ rest` reduces to `a :: b :: c :: rest` so list strucutre
on either side of ~ doesn't need to be rewritten.
-/

theorem opt_push_pop (e : Expr) (rest : List Instr) :
    Instr.push e :: Instr.pop :: rest ~ rest :=
  Equiv.append_right rest (push_pop e)

theorem opt_add_zero (e : Expr) (rest : List Instr) :
    Instr.push e :: Instr.push (Expr.lit 0) :: Instr.add :: rest ~ Instr.push e :: rest :=
  Equiv.append_right rest (add_zero e)

theorem opt_mul_one (e : Expr) (rest : List Instr) :
    Instr.push e :: Instr.push (Expr.lit 1) :: Instr.mul :: rest ~ Instr.push e :: rest :=
  Equiv.append_right rest (mul_one e)

theorem opt_const_fold_add (a b : ℤ) (rest : List Instr) :
    Instr.push (Expr.lit a) :: Instr.push (Expr.lit b) :: Instr.add :: rest ~ Instr.push (Expr.lit (a + b)) :: rest :=
  Equiv.append_right rest (const_fold_add a b)

theorem opt_const_fold_mul (a b : ℤ) (rest : List Instr) :
    Instr.push (Expr.lit a) :: Instr.push (Expr.lit b) :: Instr.mul :: rest ~ Instr.push (Expr.lit (a * b)) :: rest :=
  Equiv.append_right rest (const_fold_mul a b)

/-
Pattens on most specific first, not required as produce same on overlapping inputs.
Essentially pattern matched from love5, but, errored out not showing termination.
Neat that reccomendation of Use `termination_by` to specify a different decreasing measure
fixes, and in retrospect something of this sort obiosuly needed since for every recusrive frame
list length shrinks,, but, strucutrally not necessarily as a new head could be prepended
ahead of recursion.
-/
def optimise : List Instr → List Instr
  | Instr.push (Expr.lit a) :: Instr.push (Expr.lit b) :: Instr.add :: rest =>
      optimise (Instr.push (Expr.lit (a + b)) :: rest)
  | Instr.push (Expr.lit a) :: Instr.push (Expr.lit b) :: Instr.mul :: rest =>
      optimise (Instr.push (Expr.lit (a * b)) :: rest)
  | Instr.push e :: Instr.push (Expr.lit 0) :: Instr.add :: rest =>
      optimise (Instr.push e :: rest)
  | Instr.push e :: Instr.push (Expr.lit 1) :: Instr.mul :: rest =>
      optimise (Instr.push e :: rest)
  | Instr.push _e :: Instr.pop :: rest =>
      optimise rest
  | i :: rest => i :: optimise rest
  | [] => []
termination_by p => p.length

/-
`induction hS using RTC.head_induction_on with | ...`

Eeach case just combines IH w/ each opt helper and are just chained in a bigStepEquiv
style. Lean was kind enought to generate out `optimise.induct` from `induction _ using _`
given the `termination_by` from before.
-/

theorem optimise_sound (prog : List Instr) : optimise prog ~ prog := by
  induction prog using optimise.induct with
  | case1 a b rest ih =>
    --[push x, push y, add] → [push (x+y)]
    simp_all [optimise]
    exact ih.trans (opt_const_fold_add a b rest).symm
  | case2 a b rest ih =>
    --with `*` instead
    simp_all [optimise]
    exact ih.trans (opt_const_fold_mul a b rest).symm
  | case3 e rest _ ih =>
    --add_zero works on any expression, doesn't need literal to fire.
    simp_all [optimise]
    exact ih.trans (opt_add_zero e rest).symm
  | case4 e rest _ ih =>
    --mul_one
    simp_all [optimise]
    exact ih.trans (opt_mul_one e rest).symm
  | case5 e rest ih =>
    -- push_pop: the dead-code-elim rule
    simp_all [optimise]
    exact ih.trans (opt_push_pop e rest).symm
  | case6 i rest _ _ _ _ _ ih =>
    --nothing on head to do, work on tail
    simp_all [optimise]
    exact Equiv.cons_congr i ih
  | case7 =>
    -- nil: optimise [] = []; reflexivity closes
    simp only [optimise]
    exact Equiv.refl

end ScoobMiniMachine
end LoVe
```
