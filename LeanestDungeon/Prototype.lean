import Lean
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.Sort

-- A linear logic proposition, with atoms folded in to avoid the extra constructor around them
-- (could be revisited).
inductive LLProp where
  -- Inlining atoms to make it easier on the user
  | Candy
  | Coin
  | Cookie
  | Crown
  | Victory
  -- Actual linear logic constructors
  | Negate : LLProp → LLProp
  | MulConj : LLProp → LLProp → LLProp
  | MulDisj : LLProp → LLProp → LLProp
  | MulConjUnit
  | MulDisjUnit
  | AddConj : LLProp → LLProp → LLProp
  | AddDisj : LLProp → LLProp → LLProp
  | AddConjUnit
  | AddDisjUnit
  | Exclamation
  | Question
  deriving BEq, DecidableEq

infix:67 " ⊗ " => LLProp.MulConj
-- infix:67 " ⅋ " => LLProp.MulDisj
macro l:term:10 " ⅋ " r:term:11 : term => `(LLProp.MulDisj $l $r)
infix:67 " & " => LLProp.AddConj
-- infix:67 " ⊕ " => LLProp.AddDisj
macro l:term:10 " ⊕ " r:term:11 : term => `(LLProp.AddDisj $l $r)

notation "~" => LLProp.Negate
notation "𝟙" => LLProp.MulConjUnit
notation "⊥" => LLProp.MulDisjUnit
notation "𝟘" => LLProp.AddDisjUnit
notation "!" => LLProp.Exclamation
notation "?" => LLProp.Question

-- not sure how to hide the pre-existing notation, so being cheeky and using it instead
instance : Top LLProp where
  top := .AddConjUnit

-- This is to let one use a notation while defining the inductive for that notation
section
set_option hygiene false
local infix:40 " ⊢ " => LL

-- Writing the rules in the most readable way, then adding smarter constructors that can be applied
-- more liberally by deferring structural equalities as propositional equalities.
inductive LL : Multiset LLProp → Multiset LLProp → Prop where

  | Init :
    -----
    A ⊢ A

  | Cut :
    Γ₁ ⊢ A + Δ₁ →     A + Γ₂ ⊢ Δ₂ →
    -------------------------------
            Γ₁ + Γ2 ⊢ Δ₁ + Δ₂

  -- no exchange rule, not because it does not hold, but because we are using multisets which
  -- already allow "exchange" (as they are quotiented by reorderings)

  -- no weakening, no contraction: this is a substructural (linear) logic!

  | MulConjIntro :
    Γ = Γ₁ + Γ₂ →           Δ = Δ₁ + Δ₂ →
    Γ₁ ⊢ {A₁} + Δ₁ →     Γ₂ ⊢ {A₂} + Δ₂ →
    -------------------------------------
              Γ ⊢ {A₁ ⊗ A₂} + Δ

  | MulDisjIntroL :
      Γ = Γ₁ + Γ₂ →       Δ = Δ₁ + Δ₂ →
    {A} + Γ₁ ⊢ Δ₁ →     {B} + Γ₂ ⊢ Δ₂ →
    -----------------------------------
              {A ⅋ B} + Γ ⊢ Δ

  -- | MulDisjIntroR :
  --   Δ ⊢ {A, B} + Γ →
  --   ----------------
  --   Δ ⊢ {A ⅋ B} + Γ

  -- | MulConjUnitIntro :
  --     Γ ⊢ Δ →
  --   ----------
  --   Γ ⊢ 𝟙 :: Δ

  | AddConjElimL :
    Γ ⊢ {A & B} →
    -------------
      Γ ⊢ {A}

  | AddConjElimR :
    Γ ⊢ {A & B} →
    -------------
      Γ ⊢ {B}

  | NegationIntroL :
    Γ ⊢ {B} + Δ →
    -------------
    {~ B} + Γ ⊢ Δ

  | NegationIntroR :
    {B} + Γ ⊢ Δ →
    -------------
    Γ ⊢ {~ B} + Δ

  -- TODO: the other rules...

end

infix:40 " ⊢ " => LL

def lollipop A B := (~ A) ⅋ B
infix:50 " ⊸ " => lollipop

-- Easy to apply "Cut" wrapper
def cut :
    Δ = Δ₁ + Δ₂ →     Γ = Γ₁ + Γ₂ →     Δ₁ ⊢ A + Γ₁ →     A + Δ₂ ⊢ Γ₂ →
    -------------------------------------------------------------------
                                    Δ ⊢ Γ
  := by
    intros H1 H2
    rw [H1, H2]
    apply LL.Cut

-- There's gotta be an easier way to do this in general...
lemma flipMultiset2 : ({A, B} : Multiset LLProp) = {B, A} := by
  rw [Multiset.ext]
  intros a
  simp
  rw [Multiset.count_cons]
  rw [Multiset.count_cons]
  aesop

-- This rule is useful but derivable.
def LollipopElim :
  Δ = {A, A ⊸ B} →
  ----------------
      Δ ⊢ {B}
  := by
    have Flip : ({A, A ⊸ B} : Multiset LLProp) = {A ⊸ B, A} := by
      rw [flipMultiset2]
    rw [Flip]
    intros H
    rw [H]
    rw [lollipop]
    apply LL.MulDisjIntroL (A := ~ A) (B := B) (Γ := {A}) (Δ := {B})
      (Γ₁ := {A}) (Γ₂ := {}) (Δ₁ := {}) (Δ₂ := {B})
    rfl
    rfl
    apply LL.NegationIntroL
    apply LL.Init
    apply LL.Init

def lollipopElim :
  Δ = {A, A ⊸ B} + Δ₁ →     {B} + Δ₁ ⊢ Γ →
  ----------------------------------------
                  Δ ⊢ Γ
  := by
    intros H₁ H₂
    rw [H₁]
    apply cut (A := {B}) (Δ₁ := {A, A ⊸ B}) (Δ₂ := Δ₁) (Γ₁ := {}) (Γ₂ := Γ)
    rfl
    simp
    apply LollipopElim (A := A)
    rfl
    apply H₂

def chooseLeft :
  Δ = {A & B} + Δ₁ →     {A} + Δ₁ ⊢ Γ →
  -------------------------------------
                  Δ ⊢ Γ
  := by
    intros H
    subst H
    apply cut (A := {A}) (Δ₁ := {A & B}) (Δ₂ := Δ₁) (Γ₁ := {}) (Γ₂ := Γ); try simp
    simp
    apply LL.AddConjElimL
    apply LL.Init

def chooseRight :
  Δ = {A & B} + Δ₁ →     {B} + Δ₁ ⊢ Γ →
  -------------------------------------
                  Δ ⊢ Γ
  := by
    intros H
    subst H
    apply cut (A := {B}) (Δ₁ := {A & B}) (Δ₂ := Δ₁) (Γ₁ := {}) (Γ₂ := Γ); try simp
    simp
    apply LL.AddConjElimR
    apply LL.Init

open Lean Elab Tactic Meta Quote Term

elab "chooseLeft" : tactic => do
  evalTactic (← `(tactic| apply chooseLeft; try rfl))

elab "chooseRight" : tactic => do
  evalTactic (← `(tactic| apply chooseRight; try rfl))

elab "victory" : tactic => do
  evalTactic (← `(tactic| apply LL.Init))

def is⅋ x := ∃ lhs rhs, x = lhs ⅋ rhs

instance : DecidablePred is⅋ := by
  unfold is⅋
  intros x
  cases x <;> try (left; simp; done)
  right
  simp

def isLollipopWithLHS lhs p := ∃ rhs, p = (~ lhs) ⅋ rhs
instance : DecidablePred (isLollipopWithLHS lhs) := by
  unfold isLollipopWithLHS
  intros x
  simp
  cases x with
  | MulDisj a b =>
    if a = ~ lhs
    then right; exists b; simp; assumption
    else left; intros E; cases E; sorry
  | _ => left; simp

-- Finds a lollipop with the given LHS (i.e. a `lhs ⊸ _`) within a multiset, returning the whole
-- lollipop.
def findLollipop (lhs : LLProp) (ctx : Multiset LLProp) : Option LLProp :=
  if decide (h := Multiset.decidableExistsMultiset) (∃ x ∈ ctx, is⅋ x)
  then some lhs
  else none

elab "spend" spent:term : tactic => unsafe do
  let goal ← Lean.Elab.Tactic.getMainTarget
  match goal with
  | Expr.app (Expr.app (Expr.const ``LL _) ctx) _ =>
    let ctx' ← evalExpr (Multiset LLProp) (mkApp (mkConst `Multiset) (mkConst `LLProp)) ctx
    match findLollipop LLProp.Coin ctx' with
    | some s => logInfo s!"yes"
    | none => logInfo "nope"
  | _ => logInfo "no"
    -- evalTactic (← `(tactic| apply lollipopElim (A := $spent)))

-- If you start with a coin, and you reach a store that sells a candie or a cookie, and having a
-- cookie leads to victory, prove you can win!
def game1
  : { .Coin
    , .Coin ⊸ (.Candy & .Cookie)
    , .Cookie ⊸ .Victory
    } ⊢ {.Victory}
  :=
  by
  -- Not sure why `; try rfl` doesn't solve the second subgoal here
  spend .Coin

  apply lollipopElim (A := .Coin) (B := .Candy & .Cookie) (Δ₁ := {.Cookie ⊸ .Victory}); try rfl
  chooseRight
  apply lollipopElim (A := .Cookie) (B := .Victory) (Δ₁ := {}); try rfl
  victory
