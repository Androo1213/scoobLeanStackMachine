import VersoManual
import VersoManual.InlineLean
import LoVe.LoVelib

set_option verso.code.warnLineLength 0

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Full source" =>

The complete `MiniJvmOptimiser.lean` file, type-checked at build time. Wrapped in a local `Mirror` namespace so it doesn't collide with the canonical declarations the other chapters import.

```lean
namespace Mirror

set_option autoImplicit false
set_option tactic.hygienic false
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
  | add : Expr → Expr →Expr
  | mul : Expr → Expr → Expr
  deriving Repr /-For #eval print expressions-/

/- `Env` just maps string var names to int val Same as AExp
 Note no, mutability, just reading from  env but no writing.-/
def Env : Type := String → ℤ
/-
  `eval env e` interprets symbolic expresions w/ an env to get an int
  (since `programs` can only do the simplest of math)
  Just like love2's eval -/
def eval (env : Env) : Expr →ℤ
  | Expr.lit litValue => litValue
  | Expr.var varName => env varName
  | Expr.add leftExpr rightExpr => eval env leftExpr +eval env rightExpr
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
  | add  :Instr
  | mul  : Instr
  | dup  : Instr
  | pop  : Instr
  | swap: Instr
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
@[simp]theorem step_push (e : Expr) (stack :List Expr) :
    step (Instr.push e) stack =e :: stack :=
  rfl
@[simp] theorem step_add (a b : Expr) (rest :List Expr) :
    step Instr.add (a :: b :: rest) = Expr.add a b :: rest :=
  rfl
@[simp] theorem step_mul (a b : Expr) (rest :List Expr) :
    step Instr.mul (a :: b :: rest) = Expr.mul a b :: rest :=
  rfl
@[simp] theorem step_dup (a : Expr) (rest :List Expr) :
    step Instr.dup (a :: rest) = a :: a :: rest :=
  rfl
@[simp] theorem step_pop (a : Expr) (rest :List Expr) :
    step Instr.pop (a :: rest) = rest :=
  rfl
@[simp] theorem step_swap (a b : Expr) (rest :List Expr) :
    step Instr.swap (a :: b :: rest) = b :: a :: rest :=
  rfl
/-
`exec` is really just folding left. This can either result in base case, which is
`[]`, or `instru :: rest`.
`exec` is really just leftfolding down the stack, on `[]` reduces to `stack`, acts as base case
`exec_cons` for all else. `exec` is just leftfolding down the stack, foldl on `instr :: rest`
takes the head applies step, and recurses on rest.
-/

@[simp] theorem exec_nil (stack:List Expr) :
    exec [] stack = stack :=
  rfl
@[simp] theorem exec_cons(instr : Instr) (rest : List Instr) (stack:List Expr) :
    exec (instr :: rest) stack = exec rest (step instr stack) :=
  rfl

/-
For this universe of programs, equivalence is constrained to being said if, program `p` and
`q` evaluate to the same integer result for every environment and starting stack. Went over doing
this, instead of some sort of tree equivalence so that optimisations like add_zero, mul_one, and
constant folding could be declared true. Expression trees are rewritten into value equal but different
shapes. Similar form to hitchhiker DenoteEquiv and BigStepEquiv's: `∀s t, (S₁, s) ⇓ t ↔ (S₂, s) ⇓ t`,
but = between eval mapped stack instead of `↔` for bigStep judements.

So equiv p q means ∀ env and starting stack, executing p &  q eval pointwise to identicle ints.
`.map` or `eval env` was first meeting feedback that I guesss brought this from more than
just a comparison of expression trees strucurally, but now can (and had to deal with) folding,
strength reduction and the likes
-/
def Equiv (p q : List Instr) : Prop :=
  ∀ (env : Env) (stack : List Expr),
    (exec p stack).map (eval env) = (exec q stack).map (eval env)

infix:50 " ~ " => Equiv

/-
Essentially stolen from love9 exersise sheet
Program equivalence is an equivalence relation, i.e., it is reflexive,
symmetric, and transitive.
-/
theorem Equiv.refl {p :List Instr} :
    p ~ p :=
  fix env : Env
  fix stack : List Expr
  show (exec p stack).map (eval env) = (exec p stack).map (eval env) from
    by rfl

theorem Equiv.symm {p q :List Instr} :
    p ~ q → q ~ p :=
  assume h : p ~ q
  fix env : Env
  fix stack : List Expr
  show (exec q stack).map (eval env) = (exec p stack).map (eval env) from
    Eq.symm (h env stack)

theorem Equiv.trans {p q r :List Instr} (h₁₂ :p ~ q) (h₂₃ :q ~ r) :
    p ~ r :=
  fix env : Env
  fix stack : List Expr
  show (exec p stack).map (eval env) = (exec r stack).map (eval env) from
    Eq.trans (h₁₂ env stack) (h₂₃ env stack)

/-
'DCE'. But push pop does result in nothing. Detection is in `optimise`, both sides go to `stack.map (eval env)`
ergo simp adquete in closing.
-/
theorem push_pop (e : Expr) : [Instr.push e, Instr.pop] ~ [] := by
  intro env stack
  simp

/-
These optimisations need normalisation that is more interesting thatn just definitional
reduction. Prior lemmas unfold both `step`&`exec`, and then simp on `[eval]` kicks recursion
through `Expr`. `ring` + `omega` brought up in check-in, super nice for closing just arithimic
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

theorem add_zero (e  : Expr) :
  [Instr.push e, Instr.push (Expr.lit 0), Instr.add] ~ [Instr.push e] := by --adding zero does nothing
  intro env stack
  simp [eval]

theorem mul_one (e  : Expr) :
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
theorem add_comm_swap :[Instr.swap, Instr.add] ~ [Instr.add] := by  -- swapping before add is pointless, commutes
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

theorem const_fold_add (a b:ℤ) :
    [Instr.push (Expr.lit a), Instr.push (Expr.lit b), Instr.add] ~ [Instr.push (Expr.lit (a + b))] := by
  intro env stack
  --LHS has `add b a` (b pushed last, so b on top) while RHS has `a + b`, and ring can close commutativity `b + a = a + b`
  simp [eval]
  ring

theorem const_fold_mul (a b:ℤ) :
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

theorem exec_append (xs ys:List Instr) (stack:List Expr) : -- `xs ++ ys` is the same as running `xs` then `ys` on result
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
    (h : s₁.map (eval env)= s₂.map (eval env)) :
    (step i s₁).map (eval env) = (step i s₂).map (eval env) :=by
  cases i with
  | push e =>
    simp_all[step, eval]
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
  | nil => intros s₁ s₂  h; simpa using h
  | cons i p' ih=>
    intros s₁ s₂ h
    simp_all
    exact ih (step i s₁) (step i s₂)  (step_map_eval_eq env i s₁ s₂ h)

/-
Now need to lift ~ into larger context. Sort of like `DenoteEquiv.seq_congr`.
-/

theorem Equiv.append_right {xs ys: List Instr} (rest : List Instr) (h: xs ~ ys) :
    -- rewrite L & RHS via exec_append so goal compares running `rest`  on `exec xs stack` vs `exec ys stack`
    xs ++ rest ~ ys ++rest := by
  intro env stack
  rw [exec_append, exec_append]
  --`h env stack` -> prefix stacks are equal, exec_map_eval_eq then lifts equality across, running rest on both
  exact exec_map_eval_eq env rest (exec xs stack) (exec ys stack) (h env stack)

theorem Equiv.cons_congr (i: Instr) {xs ys : List Instr} (h: xs ~ ys) :
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

private theorem opt_push_pop (e :Expr) (rest : List Instr) :
    Instr.push e :: Instr.pop :: rest ~ rest :=
    Equiv.append_right rest (push_pop e)

private theorem opt_add_zero (e :Expr) (rest : List Instr) :
    Instr.push e::Instr.push (Expr.lit 0)::Instr.add::rest ~ Instr.push e::rest :=
    Equiv.append_right rest (add_zero e)

private theorem opt_mul_one (e :Expr) (rest : List Instr) :
    Instr.push e::Instr.push (Expr.lit 1)::Instr.mul::rest ~ Instr.push e::rest :=
    Equiv.append_right rest (mul_one e)

private theorem opt_const_fold_add (a b :ℤ) (rest : List Instr) :
    Instr.push (Expr.lit a)::Instr.push (Expr.lit b)::Instr.add::rest ~ Instr.push (Expr.lit (a + b))::rest :=
    Equiv.append_right rest (const_fold_add a b)

private theorem opt_const_fold_mul (a b : ℤ) (rest : List Instr) :
    Instr.push (Expr.lit a) :: Instr.push (Expr.lit b)::Instr.mul::rest ~ Instr.push (Expr.lit (a * b))::rest :=
    Equiv.append_right rest (const_fold_mul a b)

/-
Pattens on most specific first, not required as produce same on overlapping inputs.
Essentially pattern matched from love5, but, errored out not showing termination.
Neat that reccomendation of Use `termination_by` to specify a different decreasing measure
fixes, and in retrospect something of this sort obiosuly needed since for every recusrive frame
list length shrinks,, but, strucutrally not necessarily as a new head could be prepended
ahead of recursion.
-/
def optimise: List Instr → List Instr
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

--Post `optimise` → `[Instr.push (Expr.lit 5)]`
#eval optimise
  [ Instr.push (Expr.lit 2), Instr.push (Expr.lit 3), Instr.add
  , Instr.push (Expr.lit 0), Instr.add
  , Instr.push (Expr.lit 1), Instr.mul]

/- And running THAT optimised program on `[]` gives the same value
   you'd get by evaluating the unoptimised output under any env:
   `[lit 5]` literally — no symbolic tree, just the constant.
   `optimise_sound` certifies the two `#eval`s above are `~`-equivalent. -/
#eval exec (optimise
  [ Instr.push (Expr.lit 2), Instr.push (Expr.lit 3), Instr.add
  , Instr.push (Expr.lit 0), Instr.add
  , Instr.push (Expr.lit 1), Instr.mul ]) []

/- 'Symbolic' programs With addition of .map (eval env) projection in Equiv,
along with with the ∀ env quantifier in front of it.-/

/-add 0 to any symbol like `[push x, push 0, add]` should boild down to `[push x]`. -/
#eval optimise
  [ Instr.push (Expr.var "x") , Instr.push (Expr.lit 0) , Instr.add ]

-- Similarly, `[push x, push 1, mul]` ought to `[push x]`
#eval optimise
  [ Instr.push (Expr.var "x") ,Instr.push (Expr.lit 1) ,Instr.mul ]

/- push_pop on any literal ought to go to`[]`. -/
#eval optimise [ Instr.push (Expr.lit 7), Instr.pop ]

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


#check @optimise_sound



/- Hummingbird Egg:

The reason I got interested in this project was from `egg`. I think its really
quite fascinating to explore all rewrite paths and then pick ones that garner the best
results. Sea-of-node graphs in the JVM have always been interesting, as has a project (Cornelius)
which looks at using e-graphs in JIT/JVM optimisations. Thus, I thought it'd be pretty cool
to start looking at this and verifying that optimisations sitll hold in equivalance.

Of course, this means that all rewrites must preserve sementics, and have that all theorems and
all optimistaion helpers do. Since each step builds on a proved rule, brute-forcing the optimisation
is sound.

Of course, the obvious limitied syntacitc scope aside, I don't have any dedup, and instead
just have a bounded depth so it doesn't explode.
-/

-- Not needed for  `optimise`, but needed since all rules possible ought to be attempted.
private theorem opt_add_comm_swap (rest :List Instr) :
    Instr.swap ::Instr.add:: rest ~Instr.add :: rest :=
  Equiv.append_right rest add_comm_swap

private theorem opt_strength_reduce (e : Expr) (rest : List Instr) :
    Instr.push e ::Instr.dup ::Instr.add :: rest
      ~ Instr.push e :: Instr.push (Expr.lit 2) :: Instr.mul :: rest :=
  Equiv.append_right rest (strength_reduce e)


/-
Now each rule is thought of as an option returning matcher
`prog`, else `none`. This is the "rule database" we'll search over.
so `tryX prog` returns `some prog'` if X happens at head of prog, and if else none, just sees
what works at each step.
-/

def tryPushPop : List Instr → Option (List Instr)
  | Instr.push _ ::Instr.pop ::restProg => some restProg
  | _ => none

def tryConstFoldAdd :List Instr → Option (List Instr)
  | Instr.push (Expr.lit leftLit) :: Instr.push (Expr.lit rightLit) :: Instr.add :: restProg =>
      some (Instr.push (Expr.lit (leftLit+rightLit)) :: restProg)
  | _ => none

def tryConstFoldMul : List Instr → Option (List Instr)
  | Instr.push (Expr.lit leftLit) :: Instr.push (Expr.lit rightLit) :: Instr.mul :: restProg =>
      some (Instr.push (Expr.lit (leftLit *rightLit)) :: restProg)
  | _ => none

def tryAddZero : List Instr → Option (List Instr)
  | Instr.push pushedExpr :: Instr.push (Expr.lit 0) :: Instr.add :: restProg =>
      some (Instr.push pushedExpr::restProg)
  | _ => none

def tryMulOne : List Instr → Option (List Instr)
  | Instr.push pushedExpr :: Instr.push (Expr.lit 1) :: Instr.mul :: restProg =>
      some (Instr.push pushedExpr ::restProg)
  | _ => none

def tryAddCommSwap : List Instr → Option (List Instr)
  | Instr.swap :: Instr.add :: restProg =>
      some (Instr.add::restProg)
  | _ => none

def tryStrengthReduce : List Instr → Option (List Instr)
  | Instr.push pushedExpr :: Instr.dup::Instr.add :: restProg =>
      some (Instr.push pushedExpr::Instr.push (Expr.lit 2) ::Instr.mul:: restProg)
  | _ => none


/-
In terms of soundness, ∀ `tryX`: if it goes (returns `some prog'`),
then `prog` ought to ` ~ prog`
Simple to case split on `prog` and have pattern use correspondng opt heleprs.
Other cases derive contradiction via `none = some prog'`. -/

theorem tryPushPop_sound (prog prog' : List Instr)
    (h : tryPushPop prog = some prog') : prog' ~ prog := by
  match prog, h with
  | Instr.push pushedExpr :: Instr.pop :: restProg, h =>
    simp [tryPushPop] at h
    --post simp, h: `prog' = restProg`; subst then close w/ opt_push_pop.symm
    subst h
    exact (opt_push_pop pushedExpr restProg).symm

theorem tryConstFoldAdd_sound (prog prog' : List Instr)
    (h : tryConstFoldAdd prog = some prog') : prog' ~ prog := by
  match prog, h with
  | Instr.push (Expr.lit leftLit) :: Instr.push (Expr.lit rightLit) :: Instr.add :: restProg, h =>
    simp [tryConstFoldAdd] at h
    -- h reduces to prog' =push (lit(leftLit + rightLit))::restProg
    subst h
    exact (opt_const_fold_add leftLit rightLit restProg).symm

theorem tryConstFoldMul_sound (prog prog' : List Instr)
    (h : tryConstFoldMul prog = some prog') : prog' ~ prog := by
  match prog, h with
  | Instr.push (Expr.lit leftLit) ::Instr.push (Expr.lit rightLit) :: Instr.mul :: restProg, h =>
    simp [tryConstFoldMul] at h
    --baseically add case: prog' becomes folded product pushed nto restProg
    subst h
    exact (opt_const_fold_mul leftLit rightLit restProg).symm

theorem tryAddZero_sound (prog prog' : List Instr)
    (h : tryAddZero prog = some prog') : prog' ~ prog := by
  match prog, h with
  | Instr.push pushedExpr :: Instr.push (Expr.lit 0) :: Instr.add :: restProg, h =>
    simp [tryAddZero] at h
    --h reduces to prog' =push pushedExpr:: restProg(`push 0; add` gone)
    subst h
    exact (opt_add_zero pushedExpr restProg).symm

theorem tryMulOne_sound (prog prog' : List Instr)
    (h : tryMulOne prog = some prog') : prog' ~ prog := by
  match prog, h with
  | Instr.push pushedExpr :: Instr.push (Expr.lit 1) :: Instr.mul :: restProg, h =>
    simp [tryMulOne] at h
    --h reduces to prog' =push pushedExpr:: restProg(`push 1; mul` gone)
    subst h
    exact (opt_mul_one pushedExpr restProg).symm

theorem tryAddCommSwap_sound (prog prog' : List Instr)
    (h : tryAddCommSwap prog = some prog') : prog' ~ prog := by
  match prog, h with
  | Instr.swap :: Instr.add :: restProg, h =>
    simp [tryAddCommSwap] at h
    --h reduces to prog'= add:: restProg (swap taken by add's commutativity)
    subst h
    exact (opt_add_comm_swap restProg).symm

theorem tryStrengthReduce_sound (prog prog' : List Instr)
    (h : tryStrengthReduce prog = some prog') : prog' ~ prog := by
  match prog, h with
  | Instr.push pushedExpr :: Instr.dup :: Instr.add :: restProg, h =>
    simp [tryStrengthReduce] at h
    --h reduces to:
    --prog'= push pushedExpr :: push (lit 2) :: mul :: restProg(a+a →2*a)
    subst h
    exact (opt_strength_reduce pushedExpr restProg).symm

/-
`headRewrites prog` gives list of all programs obtainable via doing any of the 7 rules at
pos 0 of `prog`. Multiple rules get carried out fire
  Take:const_fold_add && add_zero both match `[push (lit 5), push (lit 0), add]`) and both returned.
-/
def headRewrites (prog : List Instr) : List (List Instr) :=
  [tryPushPop prog, tryConstFoldAdd prog, tryConstFoldMul prog,
   tryAddZero prog, tryMulOne prog, tryAddCommSwap prog,
   tryStrengthReduce prog].filterMap id

/--/ I fear that this was a crappy way to write this, but, after
`simp [headRewrites, List.mem_filterMap] at h` h is a 7 way disjunction,
so need to peel one layer per rule. Perhaps there is a tactic for this, but, yeah not sure.-/
theorem headRewrites_sound (prog prog' : List Instr)
    (h : prog' ∈ headRewrites prog) : prog' ~ prog := by
  simp [headRewrites, List.mem_filterMap] at h
  cases h with
  | inl hFromPushPop =>
    exact tryPushPop_sound prog prog' hFromPushPop.symm
  | inr hRest1 => cases hRest1 with
    | inl hFromConstFoldAdd =>
      exact tryConstFoldAdd_sound prog prog' hFromConstFoldAdd.symm
    | inr hRest2 => cases hRest2 with
      | inl hFromConstFoldMul =>
        exact tryConstFoldMul_sound prog prog' hFromConstFoldMul.symm
      | inr hRest3 => cases hRest3 with
        | inl hFromAddZero =>
          exact tryAddZero_sound prog prog' hFromAddZero.symm
        | inr hRest4 => cases hRest4 with
          | inl hFromMulOne =>
            exact tryMulOne_sound prog prog' hFromMulOne.symm
          | inr hRest5 => cases hRest5 with
            | inl hFromAddCommSwap =>
              exact tryAddCommSwap_sound prog prog' hFromAddCommSwap.symm
            | inr hFromStrengthReduce =>
              exact tryStrengthReduce_sound prog prog' hFromStrengthReduce.symm
/-
`allRewrites prog` give any program obtainable by carrying out one rule at one position in `prog`, and
is recursive: either the rewrite is at
  head, covered by `headRewrites`, or someplace in tail, case garners head preconcated to tail-rewrite
-/
def allRewrites : List Instr → List (List Instr)
  | [] => []
  | headInstr :: restProg =>
    headRewrites (headInstr::restProg)
      ++ (allRewrites restProg).map (fun tailRewrite => headInstr :: tailRewrite)

theorem allRewrites_sound :
    ∀ (prog prog' : List Instr), prog' ∈ allRewrites prog → prog' ~ prog := by
  intro prog
  induction prog with
  | nil => intro prog' h; simp [allRewrites] at h
  | cons headInstr restProg ih =>
    intro prog' h
    simp [allRewrites, List.mem_append, List.mem_map] at h
    cases h with
    | inl hHeadRewrite =>
      exact headRewrites_sound (headInstr :: restProg) prog' hHeadRewrite
    | inr hTailRewrite =>
      obtain ⟨tailRewrite, hTailMem, hPrependEq⟩ := hTailRewrite
      subst hPrependEq
      exact Equiv.cons_congr headInstr (ih tailRewrite hTailMem)

/-
This just replaces the idea of dedup. DeDup would need some sort of DecidableEq,
and was too complicated to figure out, but, returns all progs reachable from n rewrite steps.
This does mean duplicates show up often, any time when multiple paths reach the same prog,
and this isnt' really a problem for the small inputs I've been looking at. Howeverr, a real e-graph
would share these reprs.-/
def reachable : List Instr → Nat→ List (List Instr)
  | prog, 0 => [prog]
  | prog,depth + 1 =>
    let previousLayer := reachable prog depth
    previousLayer ++previousLayer.flatMap allRewrites

/-
Basically a computable depth version of relational rtc version from BigStep_of_RTC_SmallStep
Anyhow soundness then able to anything reachable for program reachable in any number
of steps is equiv the original by induction on `depth`.
-/
theorem reachable_sound :
    ∀ (prog : List Instr) (depth : Nat) (prog' : List Instr),
      prog' ∈ reachable prog depth → prog' ~ prog := by
  intro prog depth
  induction depth with
  | zero =>
    intro prog' h
    simp [reachable] at h
    subst h
    exact Equiv.refl
  | succ priorDepth ih =>
    intro prog' h
    simp [reachable, List.mem_append, List.mem_flatMap] at h
    cases h with
    | inl hAlreadyReachable => exact ih prog' hAlreadyReachable
    | inr hOneMoreStep =>
      obtain ⟨intermediateProg, hIntermediateReachable, hStepFromIntermediate⟩ := hOneMoreStep
      exact (allRewrites_sound intermediateProg prog' hStepFromIntermediate).trans
        (ih intermediateProg hIntermediateReachable)


/-
Hueristic for best sequence of optimisations is size of expresion trees on the final stack.

Easiest to see by example but picks the but `[push 2, push 3, add]`
  `[add (lit 2) (lit 3)]` which is of size 3
  `[push 5]` ends with `[lit 5]` which is of tree size 1
  Of coures, equivlanet progs always are eval-equal in final stacks or the (same
  values under `eval env`,  but different structurally
-/
def Expr.size : Expr → Nat
  | Expr.lit _ =>1
  | Expr.var _ =>1
  | Expr.add leftSubExpr rightSubExpr => 1 +leftSubExpr.size + rightSubExpr.size
  | Expr.mul leftSubExpr rightSubExpr => 1 +leftSubExpr.size + rightSubExpr.size

def stackTreeSize (prog : List Instr) : Nat :=
  (exec prog []).foldr (fun exprOnStack accumSize => Expr.size exprOnStack + accumSize) 0

def bestPath (prog : List Instr) (depth : Nat) : List Instr :=
  (reachable prog depth).foldl
    (fun bestSoFar candidateProg =>
      if stackTreeSize candidateProg < stackTreeSize bestSoFar
      then candidateProg
      else bestSoFar)
    prog

/-
 soundess of `bestPath`. Anything returned must be equivalent the input. `foldl` keeps
 accumulator either is `prog` ∨ one of the candidates. All candidates are also equivalent programs
 or soundly reachable. Soundness too is symmetric in the if-branches.
-/
theorem bestPath_sound (prog : List Instr) (depth : Nat) :
    bestPath prog depth ~ prog := by
  unfold bestPath
  --generalised helper as foldl preserves "~ prog" invariance.
  have foldlPreservesEquiv :
      ∀ (bestAcc : List Instr) (remainingCandidates : List (List Instr)),
      bestAcc ~ prog →
      (∀ someCandidate ∈remainingCandidates, someCandidate ~prog) →
        remainingCandidates.foldl
          (fun bestSoFar candidateProg =>
              if stackTreeSize candidateProg < stackTreeSize bestSoFar
              then candidateProg
              else bestSoFar)
          bestAcc ~prog := by
    intro bestAcc remainingCandidates
    induction remainingCandidates generalizing bestAcc with
    | nil => intro hBestAccEquiv _;  exact hBestAccEquiv
    | cons currentCandidate restCandidates ih =>
      intro hBestAccEquiv hAllRestEquiv
      simp only [List.foldl]
      by_cases hCheaper :stackTreeSize currentCandidate< stackTreeSize bestAcc
      · -- accumulator now curCandidate b/c smaller tree size
        simp [hCheaper]
        apply ih currentCandidate (hAllRestEquiv currentCandidate (by simp))
        intro laterCandidate hLaterMem
        exact hAllRestEquiv laterCandidate (List.mem_cons_of_mem currentCandidate hLaterMem)
      · -- accumulator stays as bestAcc
        simp [hCheaper]
        apply ih bestAcc  hBestAccEquiv
        intro laterCandidate hLaterMem
        exact hAllRestEquiv laterCandidate (List.mem_cons_of_mem currentCandidate hLaterMem)
  -- Apply w/ initial accumulator =prog equivalent, refl
  exact foldlPreservesEquiv prog (reachable prog depth) Equiv.refl
    (fun candidateProg hCandidateReachable =>
      reachable_sound prog depth candidateProg hCandidateReachable)

/-
Easily seen example is with two constant fols opportunites at different positions.
  Example with TWO independent const-fold opportunities at different
  positions. Either can fire first; both paths converge.
  Program: `[push 2, push 3, add, push 4, push 5, add]`
  In one step:
    - left fold first: `[push 5, push 4, push 5, add]`
    - right right first: `[push 2, push 3, add, push 9]`
  At two is just the same `[push 5, push 9]`
-/

#eval allRewrites
  [Instr.push (Expr.lit 2), Instr.push (Expr.lit 3), Instr.add, Instr.push (Expr.lit 4),
  Instr.push (Expr.lit 5), Instr.add]


--# of reachable programs at increasing depth (with duplicates):
#eval (reachable
  [Instr.push (Expr.lit 2), Instr.push (Expr.lit 3), Instr.add, Instr.push (Expr.lit 4),
   Instr.push (Expr.lit 5), Instr.add] 1).length

#eval (reachable
  [Instr.push (Expr.lit 2), Instr.push (Expr.lit 3), Instr.add, Instr.push (Expr.lit 4),
   Instr.push (Expr.lit 5), Instr.add] 3).length


-- by third should find `[push 5, push 9]` len of 2.
#eval bestPath
  [Instr.push (Expr.lit 2), Instr.push (Expr.lit 3), Instr.add, Instr.push (Expr.lit 4),
  Instr.push (Expr.lit 5), Instr.add] 3

/-
`strength_reduce` isn't ∈ `optimise`, but in brute force, adn
can find get result than `optimise`:
So say prog is `[push 5, dup, add]`
  `optimise` result is just `[push 5, dup, add]` as dup w/ add doesn't trigger anything
  `bestPath` @ depth two `[push 10]` (strength_reduce, then const_fold_mul)
-/

#eval optimise [Instr.push (Expr.lit 5), Instr.dup, Instr.add]

#eval bestPath [Instr.push (Expr.lit 5), Instr.dup, Instr.add] 2


#check @allRewrites_sound
#check @reachable_sound

end ScoobMiniMachine
end LoVe

end Mirror
```
