import VersoManual
import VersoManual.InlineLean
import Docs.Ch4_Optimiser

set_option autoImplicit false
set_option tactic.hygienic false
set_option verso.code.warnLineLength 0

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open LoVe.ScoobMiniMachine

#doc (Manual) "Brute-force equality saturation" =>

_TODO_

```lean
namespace LoVe
namespace ScoobMiniMachine

/-

-/

-- Not needed for  `optimise`, but needed since all rules possible ought to be attempted.
private theorem opt_add_comm_swap (rest : List Instr) :
    Instr.swap :: Instr.add :: rest ~ Instr.add :: rest :=
  Equiv.append_right rest add_comm_swap

private theorem opt_strength_reduce (e : Expr) (rest : List Instr) :
    Instr.push e :: Instr.dup :: Instr.add :: rest
      ~ Instr.push e :: Instr.push (Expr.lit 2) :: Instr.mul :: rest :=
  Equiv.append_right rest (strength_reduce e)

/-
Now each rule is thought of as an option returning matcher
`prog`, else `none`. This is the "rule database" we'll search over.
so `tryX prog` returns `some prog'` if X happens at head of prog, and if else none, just sees
what works at each step.
-/

def tryPushPop : List Instr → Option (List Instr)
  | Instr.push _ :: Instr.pop :: restProg => some restProg
  | _ => none

def tryConstFoldAdd : List Instr → Option (List Instr)
  | Instr.push (Expr.lit leftLit) :: Instr.push (Expr.lit rightLit) :: Instr.add :: restProg =>
      some (Instr.push (Expr.lit (leftLit + rightLit)) :: restProg)
  | _ => none

def tryConstFoldMul : List Instr → Option (List Instr)
  | Instr.push (Expr.lit leftLit) :: Instr.push (Expr.lit rightLit) :: Instr.mul :: restProg =>
      some (Instr.push (Expr.lit (leftLit * rightLit)) :: restProg)
  | _ => none

def tryAddZero : List Instr → Option (List Instr)
  | Instr.push pushedExpr :: Instr.push (Expr.lit 0) :: Instr.add :: restProg =>
      some (Instr.push pushedExpr :: restProg)
  | _ => none

def tryMulOne : List Instr → Option (List Instr)
  | Instr.push pushedExpr :: Instr.push (Expr.lit 1) :: Instr.mul :: restProg =>
      some (Instr.push pushedExpr :: restProg)
  | _ => none

def tryAddCommSwap : List Instr → Option (List Instr)
  | Instr.swap :: Instr.add :: restProg =>
      some (Instr.add :: restProg)
  | _ => none

def tryStrengthReduce : List Instr → Option (List Instr)
  | Instr.push pushedExpr :: Instr.dup :: Instr.add :: restProg =>
      some (Instr.push pushedExpr :: Instr.push (Expr.lit 2) :: Instr.mul :: restProg)
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
  | Instr.push (Expr.lit leftLit) :: Instr.push (Expr.lit rightLit) :: Instr.mul :: restProg, h =>
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
so need to peel one layer per rule. Perhaps there is a tactic? TODO,come back and rewrite later.-/
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
    headRewrites (headInstr :: restProg)
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
def reachable : List Instr → Nat → List (List Instr)
  | prog, 0 => [prog]
  | prog, depth + 1 =>
    let previousLayer := reachable prog depth
    previousLayer ++ previousLayer.flatMap allRewrites

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
Hueristic for best sequence of optimisations just is size of expresion trees on the final stack.

Easiest to see by example but picks the but `[push 2, push 3, add]`
  `[add (lit 2) (lit 3)]` which is of size 3
  `[push 5]` ends with `[lit 5]` which is of tree size 1
  Of coures, equivlanet progs always are eval-equal in final stacks or the (same
  values under `eval env`,  but different structurally
-/
def Expr.size : Expr → Nat
  | Expr.lit _ => 1
  | Expr.var _ => 1
  | Expr.add leftSubExpr rightSubExpr => 1 + leftSubExpr.size + rightSubExpr.size
  | Expr.mul leftSubExpr rightSubExpr => 1 + leftSubExpr.size + rightSubExpr.size

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
      (∀ someCandidate ∈ remainingCandidates, someCandidate ~ prog) →
        remainingCandidates.foldl
          (fun bestSoFar candidateProg =>
              if stackTreeSize candidateProg < stackTreeSize bestSoFar
              then candidateProg
              else bestSoFar)
          bestAcc ~ prog := by
    intro bestAcc remainingCandidates
    induction remainingCandidates generalizing bestAcc with
    | nil => intro hBestAccEquiv _; exact hBestAccEquiv
    | cons currentCandidate restCandidates ih =>
      intro hBestAccEquiv hAllRestEquiv
      simp only [List.foldl]
      by_cases hCheaper : stackTreeSize currentCandidate < stackTreeSize bestAcc
      · -- accumulator now curCandidate b/c smaller tree size
        simp [hCheaper]
        apply ih currentCandidate (hAllRestEquiv currentCandidate (by simp))
        intro laterCandidate hLaterMem
        exact hAllRestEquiv laterCandidate (List.mem_cons_of_mem currentCandidate hLaterMem)
      · -- accumulator stays as bestAcc
        simp [hCheaper]
        apply ih bestAcc hBestAccEquiv
        intro laterCandidate hLaterMem
        exact hAllRestEquiv laterCandidate (List.mem_cons_of_mem currentCandidate hLaterMem)
  -- Apply w/ initial accumulator =prog equivalent, refl
  exact foldlPreservesEquiv prog (reachable prog depth) Equiv.refl
    (fun candidateProg hCandidateReachable =>
      reachable_sound prog depth candidateProg hCandidateReachable)

end ScoobMiniMachine
end LoVe
```

```lean
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
```
