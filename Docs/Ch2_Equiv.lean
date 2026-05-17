import VersoManual
import VersoManual.InlineLean
import Docs.Ch1_Types

set_option autoImplicit false
set_option tactic.hygienic false
set_option verso.code.warnLineLength 0

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open LoVe.ScoobMiniMachine

#doc (Manual) "Equivalence" =>

For this universe of programs, equivalence is constrained to being said if, program `p` and
`q` evaluate to the same integer result for every environment and starting stack. Went over doing
this, instead of some sort of tree equivalence so that optimisations like add_zero, mul_one, and
constant folding could be declared true. Expression trees are rewritten into value equal but different
shapes. Similar form to hitchhiker DenoteEquiv and BigStepEquiv's: `∀s t, (S₁, s) ⇓ t ↔ (S₂, s) ⇓ t`,
but = between eval mapped stack instead of `↔` for bigStep judements.

.map (env eval) provides this ability as now, equivalence can posited, or proven really, with symbolic expressions, rather than simple
structural comparison between Expr trees. Most rewrites would have either not worked or been trivial without this enhancement.


This really comes from the notion of DenoteEquiv, or that: equivalence = meanings agree, which hitchikers advocated for,
 and was a good middle ground of how much could be asserted and expressed without going to a bigStep ∨ smallStep operational equivalence, which would've been an enchament as it'd allow step-by-step execution structure
(intermediate states, the order rewrites visit, that kind of thing), but would've made proofs with optimisations much more ardous. Take like


(push 1, push 1, add) and (push 2) are equivalent when nder denoteEquiv, however, they have differetn IRs go through different intermediate stacks, for exmaple const_fold_add would stop being
 a sound rewrite if traces were considred. denoteEquiv I guess can be tought to balanc information instead of tractability, as it give up caring about how programs run, but get to prove that what they compute is the same.



```lean
namespace LoVe
namespace ScoobMiniMachine

/-
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
theorem Equiv.refl {p : List Instr} :
    p ~ p :=
  fix env : Env
  fix stack : List Expr
  show (exec p stack).map (eval env) = (exec p stack).map (eval env) from
    by rfl

theorem Equiv.symm {p q : List Instr} :
    p ~ q → q ~ p :=
  assume h : p ~ q
  fix env : Env
  fix stack : List Expr
  show (exec q stack).map (eval env) = (exec p stack).map (eval env) from
    Eq.symm (h env stack)

theorem Equiv.trans {p q r : List Instr} (h₁₂ : p ~ q) (h₂₃ : q ~ r) :
    p ~ r :=
  fix env : Env
  fix stack : List Expr
  show (exec p stack).map (eval env) = (exec r stack).map (eval env) from
    Eq.trans (h₁₂ env stack) (h₂₃ env stack)

end ScoobMiniMachine
end LoVe
```
