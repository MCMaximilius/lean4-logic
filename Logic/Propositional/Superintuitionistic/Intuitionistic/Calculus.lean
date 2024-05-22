import Logic.Logic.Calculus

namespace LO.Propositional

class LogicSymbol (α : Sort _)
  extends Bot α, Arrow α

class TwoSidedᵢ (F : Type u) where
  Derivation : List F → F → Type u

infix: 45 " ⊢ᵢ " => TwoSidedᵢ.Derivation

class Gentzenᵢ (F : Type u) [LogicSymbol F] extends TwoSidedᵢ F where
  ax (p : F)                              : [p] ⊢ᵢ p
  falsum (p : F)                          : [⊥] ⊢ᵢ p
  -- andLeft {p q r : F} {Γ : List F}         : p :: q :: Γ ⊢³ r → p ⋏ q :: Γ ⊢³ r
  -- andRight {p q : F} {Γ : List F}          : Γ ⊢³ p → Γ ⊢³ q → Γ ⊢³ p ⋏ q
  -- orLeft {p q : F} {Γ : List F}            : p :: Γ ⊢³ r → q :: Γ ⊢³ r → p ⋎ q :: Γ ⊢³ r
  -- orRightL {p : F} (q : F) {Γ : List F}    : Γ ⊢³ p → Γ ⊢³ p ⋎ q
  -- orRightR (p : F) {q : F} {Γ : List F}    : Γ ⊢³ q → Γ ⊢³ p ⋎ q
  implyLeft {Γ : List F} {p q r : F}      : Γ ⊢ᵢ p → q :: Γ ⊢ᵢ r → (p ⟶ q) :: Γ ⊢ᵢ r
  implyRight {Γ : List F} {p q : F}       : p :: Γ ⊢ᵢ q → Γ ⊢ᵢ (p ⟶ q)
  wk {Γ Γ' : List F} {p : F}              : Γ ⊢ᵢ p → Γ ⊆ Γ' → Γ' ⊢ᵢ p
  cut {Γ : List F} {p q : F}              : Γ ⊢ᵢ p → p :: Γ ⊢ᵢ q → Γ ⊢ᵢ q

inductive Formula : Type where
  | var : ℕ → Formula
  | falsum
  | imply : Formula → Formula → Formula

def complexity : Formula → ℕ
  | Formula.var _ => 0
  | Formula.falsum => 0
  | Formula.imply p q => max (complexity p) (complexity q) + 1

instance : LogicSymbol Formula where
  arrow := Formula.imply
  bot := Formula.falsum

inductive Derivation' : List Formula → Formula → Type where
  | ax (p) :  Derivation' [p] p
  | falsum (p) : Derivation' [⊥] p
  | implyLeft {Γ p q r} : Derivation' Γ p → Derivation' (q :: Γ) r → Derivation' ((p ⟶ q) :: Γ) r
  | implyRight {Γ p q} : Derivation' (p :: Γ) q → Derivation' Γ (p ⟶ q)
  | wk {Γ Γ' p} : Derivation' Γ p → Γ ⊆ Γ' → Derivation' Γ' p
  | cut {Γ p q} : Derivation' Γ p → Derivation' (p :: Γ) q → Derivation' Γ q

instance : TwoSidedᵢ Formula where
  Derivation := Derivation'

instance : Gentzenᵢ Formula where
  ax := Derivation'.ax
  falsum := Derivation'.falsum
  implyLeft := Derivation'.implyLeft
  implyRight := Derivation'.implyRight
  wk := Derivation'.wk
  cut := Derivation'.cut

end LO.Propositional
