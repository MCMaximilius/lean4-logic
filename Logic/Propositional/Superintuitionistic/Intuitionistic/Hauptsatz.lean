import Logic.Propositional.Superintuitionistic.Intuitionistic.Calculus

namespace LO.Propositional

inductive CutRestricted (C : Set Formula) : {Γ : List Formula} → {A : Formula} → Γ ⊢ᵢ A → Prop
  | ax (p) : CutRestricted C (Gentzenᵢ.ax p)
  | falsum (p) : CutRestricted C (Gentzenᵢ.falsum p)
  | implyLeft {Γ p q r} (d₁ : Γ ⊢ᵢ p) (d₂ : q :: Γ ⊢ᵢ r) : CutRestricted C d₁ → CutRestricted C d₂ → CutRestricted C (Gentzenᵢ.implyLeft d₁ d₂)
  | implyRight {Γ p q} (d : p :: Γ ⊢ᵢ q) : CutRestricted C d → CutRestricted C (Gentzenᵢ.implyRight d)
  | wk {Γ Γ' p} (d : Γ ⊢ᵢ p) (ss : Γ ⊆ Γ') : CutRestricted C d → CutRestricted C (Gentzenᵢ.wk d ss)
  | cut {Γ p q} (d₁ : Γ ⊢ᵢ p) (d₂ : p :: Γ ⊢ᵢ q) : CutRestricted C d₁ → CutRestricted C d₂ → p ∈ C → CutRestricted C (Gentzenᵢ.cut d₁ d₂)

def CutFree {Γ : List Formula} {p : Formula} (d : Γ ⊢ᵢ p) : Prop := CutRestricted ∅ d

abbrev Restricted (C : Set Formula) (Γ : List Formula) (p : Formula) := {d : Γ ⊢ᵢ p // CutRestricted C d}

scoped notation :45 Γ:45 " ⊢ᵢ[" C "] " p:45 => Restricted C Γ p

abbrev RestrictedComplexity (c : ℕ) (Γ : List Formula) (p : Formula) := Γ ⊢ᵢ[{p | complexity p < c}] p

scoped notation :45 Γ:45 "⊢ᵢ[< " c "] " p:45 => RestrictedComplexity c Γ p

-- lemma of_subset (d : Γ ⊢ᵢ p) (ss : C ⊆ C') : CutRestricted C d → CutRestricted C' d := by
--   sorry

-- @[simp]
-- lemma cutRestricted (d : Γ ⊢ᵢ[C] p) : CutRestricted C (d : Γ ⊢ᵢ p) := d.prop

-- def ofSubset {C C' : Set Formula} {Γ p} (h : C ⊆ C') (d : Γ ⊢ᵢ[C] p) : Γ ⊢ᵢ[C'] p := ⟨d, d.cutRestricted.of_subset h⟩

-- def RestrictedComplexity.ofLe {i j : ℕ} (hij : i ≤ j) (d : Γ ⊢ᵢ[< i] p) : Γ ⊢ᵢ[< j] Δ := d.ofSubset (by simp; intro _ h; exact lt_of_lt_of_le h hij)

-- def implyInversion : {C} → {Γ} → {p} → (Γ ⊢ᵢ[C] p ⟶ q) → (p :: Γ ⊢ᵢ[C] p)
--   | _ _ _ ⟨ax p, _⟩ => sorry

end LO.Propositional
