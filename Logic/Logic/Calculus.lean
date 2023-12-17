import Logic.Logic.System

namespace LO

class OneSided (F : Type u) where
  Derivation : List F → Type u

class TwoSided (F : Type u) where
  Derivation : List F → List F → Type u

prefix: 45 " ⊢¹ " => OneSided.Derivation

infix: 45 " ⊢² " => TwoSided.Derivation

abbrev OneSided.Derivable [OneSided F] (Δ : List F) : Prop := Nonempty (⊢¹ Δ)

abbrev TwoSided.Derivable [TwoSided F] (Γ Δ : List F) : Prop := Nonempty (Γ ⊢² Δ)

prefix: 45 " ⊢¹! " => OneSided.Derivation

infix: 45 " ⊢²! " => TwoSided.Derivable

class Tait (F : Type u) [LogicSymbol F] extends OneSided F where
  verum (Δ : List F)         : ⊢¹ ⊤ :: Δ
  and {p q : F} {Δ : List F} : ⊢¹ p :: Δ → ⊢¹ q :: Δ → ⊢¹ p ⋏ q :: Δ
  or {p q : F} {Δ : List F}  : ⊢¹ p :: q :: Δ → ⊢¹ p ⋎ q :: Δ
  wk {Δ Δ' : List F}         : ⊢¹ Δ → Δ ⊆ Δ' → ⊢¹ Δ'
  em {p} {Δ : List F}        : p ∈ Δ → ~p ∈ Δ → ⊢¹ Δ

class Tait.Cut (F : Type u) [LogicSymbol F] [Tait F] where
  cut {Δ : List F} {p} : ⊢¹ p :: Δ → ⊢¹ ~p :: Δ → ⊢¹ Δ

class Gentzen (F : Type u) [LogicSymbol F] extends TwoSided F where
  verum (Γ Δ : List F)                : Γ ⊢² ⊤ :: Δ
  falsum (Γ Δ : List F)               : ⊥ :: Γ ⊢² Δ
  negLeft {p : F} {Γ Δ : List F}      : Γ ⊢² p :: Δ → ~p :: Γ ⊢² Δ
  negRight {p : F} {Γ Δ : List F}     : p :: Γ ⊢² Δ → Γ ⊢² ~p :: Δ
  andLeft {p q : F} {Γ Δ : List F}    : p :: q :: Γ ⊢² Δ → p ⋏ q :: Γ ⊢² Δ
  andRight {p q : F} {Γ Δ : List F}   : Γ ⊢² p :: Δ → Γ ⊢² q :: Δ → Γ ⊢² p ⋏ q :: Δ
  orLeft {p q : F} {Γ Δ : List F}     : p :: Γ ⊢² Δ → q :: Γ ⊢² Δ → p ⋎ q :: Γ ⊢² Δ
  orRight {p q : F} {Γ Δ : List F}    : Γ ⊢² p :: q :: Δ → Γ ⊢² p ⋎ q :: Δ
  implyLeft {p q : F} {Γ Δ : List F}  : Γ ⊢² p :: Δ → q :: Γ ⊢² Δ → (p ⟶ q) :: Γ ⊢² Δ
  implyRight {p q : F} {Γ Δ : List F} : p :: Γ ⊢² q :: Δ → Γ ⊢² (p ⟶ q) :: Δ
  wk {Γ Γ' Δ Δ' : List F}             : Γ ⊢² Δ → Γ ⊆ Γ' → Δ ⊆ Δ' → Γ' ⊢² Δ'
  em {p} {Γ Δ : List F}               : p ∈ Γ → p ∈ Δ → Γ ⊢² Δ

class Gentzen.Cut (F : Type u) [LogicSymbol F] [Gentzen F] where
  cut {Γ Δ : List F} {p} : Γ ⊢² p :: Δ → p :: Γ ⊢² Δ → Γ ⊢² Δ

class LawfulGentzen (F : Type u) [LogicSymbol F] [System F] extends Gentzen F where
  toProof₁ {Γ} {T : Set F} {p : F} : Γ ⊢² [p] → (∀ q ∈ Γ, T ⊢ q) → T ⊢ p

variable {F : Type*} [LogicSymbol F]

namespace OneSided

variable [OneSided F] {Γ Δ : List F}

protected abbrev cast (d : ⊢¹ Δ) (e : Δ = Γ) : ⊢¹ Γ := cast (congrArg _ e) d

end OneSided

namespace Tait

variable [DeMorgan F] [Tait F]

variable {Γ Δ : List F}

instance : TwoSided F where
  Derivation := fun Γ Δ => ⊢¹ Γ.map (~·) ++ Δ

def ofConsLeft {p : F} {Γ Δ : List F} (b : p :: Γ ⊢² Δ) :
    ⊢¹ ~p :: (Γ.map (~·) ++ Δ) := wk b (by simp)

def ofConsRight {p : F} {Γ Δ : List F} (b : Γ ⊢² p :: Δ) :
    ⊢¹ p :: (Γ.map (~·) ++ Δ) :=
  wk b (by
    simp
    exact ⟨List.subset_cons_of_subset _ (List.subset_append_left _ _),
      List.subset_cons_of_subset _ (List.subset_append_right _ _)⟩)

def ofConsRight₂ {p q : F} {Γ Δ : List F} (b : Γ ⊢² p :: q :: Δ) :
    ⊢¹ p :: q :: (Γ.map (~·) ++ Δ) :=
  wk b (by
    simp
    exact ⟨List.subset_cons_of_subset _ $ List.subset_cons_of_subset _ $ List.subset_append_left _ _,
      List.subset_cons_of_subset _ $ List.subset_cons_of_subset _ $ List.subset_append_right _ _⟩)

def ofConsLeftRight {p q : F} {Γ Δ : List F} (b : p :: Γ ⊢² q :: Δ) :
    ⊢¹ ~p :: q :: (Γ.map (~·) ++ Δ) :=
  wk b (by
    simp
    exact ⟨List.subset_cons_of_subset _ $ List.subset_cons_of_subset _ $ List.subset_append_left _ _,
      List.subset_cons_of_subset _ $ List.subset_cons_of_subset _ $ List.subset_append_right _ _⟩)

def toConsLeft {p : F} {Γ Δ : List F}
    (b : ⊢¹ ~p :: (Γ.map (~·) ++ Δ)) :
    p :: Γ ⊢² Δ := wk b (by simp)

def toConsRight {p : F} {Γ Δ : List F}
    (b : ⊢¹ p :: (Γ.map (~·) ++ Δ)) :
    Γ ⊢² p :: Δ :=
  wk b (by
    simp
    exact List.subset_append_of_subset_right _ (List.subset_cons _ _))

instance : Gentzen F where
  verum := fun _ _ => toConsRight (verum _)
  falsum := fun _ _ => toConsLeft (by simpa using verum _)
  negLeft := fun b => toConsLeft (OneSided.cast (ofConsRight b) (by simp))
  negRight := fun b => toConsRight (OneSided.cast (ofConsLeft b) (by simp))
  andLeft := fun b => OneSided.cast (or b) (by simp)
  andRight := fun bp bq =>
    toConsRight (OneSided.cast (and (ofConsRight bp) (ofConsRight bq)) (by simp))
  orLeft := fun bp bq =>
    toConsLeft (OneSided.cast (and (ofConsLeft bp) (ofConsLeft bq)) (by simp))
  orRight := fun b => toConsRight (OneSided.cast (or $ ofConsRight₂ b) (by simp))
  implyLeft := fun bp bq =>
    toConsLeft (OneSided.cast (and (ofConsRight bp) (ofConsLeft bq)) (by simp[DeMorgan.imply]))
  implyRight := fun b =>
    toConsRight (OneSided.cast (or $ ofConsLeftRight b) (by simp[DeMorgan.imply]))
  wk := fun b hΓ hΔ => wk b (by
    simp
    exact ⟨List.subset_append_of_subset_left _ $ List.map_subset _ hΓ,
      List.subset_append_of_subset_right _ $ hΔ⟩)
  em := fun {p} _ _ hΓ hΔ => em (p := p)
    (List.mem_append.mpr $ .inr $ hΔ)
    (List.mem_append.mpr $ .inl $ List.mem_map_of_mem (~·) hΓ)

variable [Tait.Cut F]

instance : Gentzen.Cut F := ⟨fun d d' => Cut.cut (ofConsRight d) (ofConsLeft d')⟩

end Tait

namespace Gentzen

variable [Gentzen F] [Gentzen.Cut F] {Γ Δ E : List F}


def wkLeft {Γ Γ' Δ : List F} (d : Γ ⊢² Δ) (ss : Γ ⊆ Γ') : Γ' ⊢² Δ := wk d ss (by simp)

def wkRight {Γ Δ Δ' : List F} (d : Γ ⊢² Δ) (ss : Δ ⊆ Δ') : Γ ⊢² Δ' := wk d (by simp) ss

def ofNegLeft {p} (b : ~p :: Γ ⊢² Δ) : Γ ⊢² p :: Δ :=
  let d : p :: Γ ⊢² p :: Δ :=
    Gentzen.wk (show [p] ⊢² [p] from em (List.mem_singleton.mpr rfl) (List.mem_singleton.mpr rfl))
      (by simp) (by simp)
  Cut.cut (negRight d) (wkRight b (by simp))

def ofNegRight {p} (b : Γ ⊢² ~p :: Δ) : p :: Γ ⊢² Δ :=
  let d : p :: Γ ⊢² p :: Δ :=
    Gentzen.wk (show [p] ⊢² [p] from em (List.mem_singleton.mpr rfl) (List.mem_singleton.mpr rfl))
      (by simp) (by simp)
  Cut.cut (wkLeft b (by simp)) (negLeft d)

structure DerivationM (T : Set F) (Γ : List F) where
  antecedent : List F
  antecedent_ss : ∀ p ∈ antecedent, p ∈ T
  bew : antecedent ⊢² Γ

infix: 45 " ⊢²' " => DerivationM

variable {T : Set F}

def DerivationMEquivDerivation :
    T ⊢²' Γ ≃ (Δ : {Δ : List F // ∀ π ∈ Δ, π ∈ T}) × Δ ⊢² Γ where
  toFun := fun b => ⟨⟨b.antecedent, b.antecedent_ss⟩, b.bew⟩
  invFun := fun p => ⟨p.1, p.1.prop, p.2⟩
  left_inv := fun b => by simp
  right_inv := fun b => by simp

def DerivationM.weakening {T U : Set F} {Γ : List F} (b : T ⊢²' Γ) (h : T ⊆ U) : U ⊢²' Γ where
  antecedent := b.antecedent
  antecedent_ss := fun p hp => h (b.antecedent_ss p hp)
  bew := b.bew

def toDerivationM {Γ Δ} (d : Γ ⊢² Δ) (ss : ∀ p ∈ Γ, p ∈ T) : T ⊢²' Δ where
  antecedent := Γ
  antecedent_ss := ss
  bew := d

def Cut.cut' {Γ₁ Γ₂ Δ₁ Δ₂ : List F} (d₁ : Γ₁ ⊢² p :: Δ₁) (d₂ : p :: Γ₂ ⊢² Δ₂) : Γ₁ ++ Γ₂ ⊢² Δ₁ ++ Δ₂ :=
  let d₁ : Γ₁ ++ Γ₂ ⊢² p :: (Δ₁ ++ Δ₂) := wk d₁ (by simp) (List.cons_subset_cons _ $ by simp)
  let d₂ : p :: (Γ₁ ++ Γ₂) ⊢² Δ₁ ++ Δ₂ := wk d₂ (List.cons_subset_cons _ $ by simp) (by simp)
  Cut.cut d₁ d₂

namespace DerivationM

def wk (b : T ⊢²' Γ) (ss : Γ ⊆ Γ') : T ⊢²' Γ' where
  antecedent := b.antecedent
  antecedent_ss := b.antecedent_ss
  bew := wkRight b.bew ss

def cut (b : T ⊢²' p :: Γ) (b' : T ⊢²' ~p :: Γ) : T ⊢²' Γ where
  antecedent := b.antecedent ++ b'.antecedent
  antecedent_ss := by
    simp
    rintro p (hp | hp)
    · exact b.antecedent_ss _ hp
    · exact b'.antecedent_ss _ hp
  bew :=
    let d : b.antecedent ++ b'.antecedent ⊢² p :: Γ := wkLeft b.bew (by simp)
    let d' : b.antecedent ++ b'.antecedent ⊢² ~p :: Γ := wkLeft b'.bew (by simp)
    Cut.cut d' (negLeft d)

def cut' (b : T ⊢²' p :: Γ) (b' : T ⊢²' ~p :: Δ) : T ⊢²' Γ ++ Δ where
  antecedent := b.antecedent ++ b'.antecedent
  antecedent_ss := by
    simp
    rintro p (hp | hp)
    · exact b.antecedent_ss _ hp
    · exact b'.antecedent_ss _ hp
  bew := by
    let d : b.antecedent ++ b'.antecedent ⊢² p :: Γ := wkLeft b.bew (by simp)
    let d' : b.antecedent ++ b'.antecedent ⊢² ~p :: Δ := wkLeft b'.bew (by simp)
    exact Gentzen.wk (Cut.cut' d' (negLeft d)) (by simp) (by simp)

def verum (Γ : List F) : T ⊢²' ⊤ :: Γ := ⟨[], by simp, Gentzen.verum _ _⟩

def deduction [DecidableEq F] {p} (b : insert p T ⊢²' Δ) : T ⊢²' ~p :: Δ where
  antecedent := b.antecedent.filter (· ≠ p)
  antecedent_ss := by
    simp[List.mem_filter]
    intro q hq ne
    simpa[ne] using b.antecedent_ss q hq
  bew := negRight (wkLeft b.bew $ by
    intro q hq
    by_cases e : q = p <;> simp[List.mem_filter, hq, e])

def deductionNeg [DecidableEq F] {p} (b : insert (~p) T ⊢²' Δ) : T ⊢²' p :: Δ where
  antecedent := b.antecedent.filter (· ≠ ~p)
  antecedent_ss := by
    simp[List.mem_filter]
    intro q hq ne
    simpa[ne] using b.antecedent_ss q hq
  bew := ofNegLeft (wkLeft b.bew $ by
    intro q hq
    by_cases e : q = ~p <;> simp[List.mem_filter, hq, e])

end DerivationM

variable (F)

instance : System F where
  Bew := fun T p => T ⊢²' [p]
  axm := fun {T p} h =>
    ⟨[p], by simpa,
      em (List.mem_singleton.mpr rfl) (List.mem_singleton.mpr rfl)⟩
  weakening' := fun ss b => b.weakening ss

variable {F}

def toProof :
    {Γ Δ : List F} → Γ ⊢² Δ → (∀ q ∈ Γ, T ⊢ q) → T ⊢²' Δ
  | [],     _, d, _ => toDerivationM d (by simp)
  | q :: Γ, Δ, d, h =>
    let bn : T ⊢²' ~q :: Δ := toProof (negRight d) (fun q hq => h q (by simp[hq]))
    let b : T ⊢²' [q] := h q (by simp)
    b.cut' bn

instance : LawfulGentzen F := ⟨toProof⟩

def proofEquivDerivation {p : F} :
    T ⊢ p ≃ (Δ : {Δ : List F // ∀ π ∈ Δ, π ∈ T}) × Δ ⊢² [p] :=
  DerivationMEquivDerivation

lemma provable_iff {p : F} :
    T ⊢! p ↔ ∃ Δ : List F, (∀ π ∈ Δ, π ∈ T) ∧ Δ ⊢²! [p] :=
  ⟨by rintro ⟨b⟩; rcases proofEquivDerivation b with ⟨Δ, d⟩; exact ⟨Δ, Δ.prop, ⟨d⟩⟩,
   by rintro ⟨Δ, h, ⟨d⟩⟩; exact ⟨proofEquivDerivation.symm ⟨⟨Δ, h⟩, d⟩⟩⟩

theorem compact :
    System.Consistent T ↔ ∀ T' : Finset F, ↑T' ⊆ T → System.Consistent (T' : Set F) :=
  ⟨fun c u hu => c.of_subset hu,
   fun h => ⟨by
    letI := Classical.typeDecidableEq F
    rintro ⟨Δ, hΔ, d⟩
    exact (System.unprovable_iff_not_provable.mp $
      System.consistemt_iff_unprovable.mp $ h Δ.toFinset (by intro p; simpa using hΔ p))
      (provable_iff.mpr $ ⟨Δ, by simp, ⟨d⟩⟩)⟩⟩

lemma consistent_iff_empty_sequent :
    System.Consistent T ↔ IsEmpty (T ⊢²' []) :=
  ⟨by contrapose; simp[System.Consistent]; intro b; exact ⟨b.wk (by simp)⟩,
   by contrapose; simp[System.Consistent]
      rintro ⟨Δ, h, d⟩
      have : Δ ⊢² [] := Cut.cut d (falsum _ _)
      exact ⟨toDerivationM this h⟩⟩

lemma provable_iff_inConsistent {p} :
    T ⊢! p ↔ ¬System.Consistent (insert (~p) T) :=
  ⟨by rintro ⟨⟨Δ, h, d⟩⟩
      simp[consistent_iff_empty_sequent]
      exact ⟨⟨~p :: Δ, by simp; intro q hq; right; exact h q hq, negLeft d⟩⟩,
   by letI := Classical.typeDecidableEq F
      simp[consistent_iff_empty_sequent]
      intro b
      exact ⟨b.deductionNeg⟩⟩

lemma inconsistent_of_provable_and_refutable {p}
    (bp : T ⊢ p) (br : T ⊢ ~p) : ¬System.Consistent T := fun A => by
  have : T ⊢²' [] := DerivationM.cut bp br
  exact (consistent_iff_empty_sequent.mp A).false this

lemma inconsistent_of_provable_and_refutable' {p}
    (bp : T ⊢! p) (br : T ⊢! ~p) : ¬System.Consistent T := by
  rcases bp with ⟨bp⟩; rcases br with ⟨br⟩
  exact inconsistent_of_provable_and_refutable bp br

end Gentzen

namespace LawfulGentzen

variable [System F] [LawfulGentzen F]

def toProofOfNil {p : F} (b : [] ⊢² [p]) (T : Set F) : T ⊢ p :=
  toProof₁ b (by intro q h; exact False.elim ((List.mem_nil_iff q).mp h))

lemma toProof₁! {Γ} {T : Set F} {p : F} (b : Γ ⊢² [p]) (H : ∀ q ∈ Γ, T ⊢! q) : T ⊢! p :=
  ⟨toProof₁ b (fun q hq => (H q hq).toProof)⟩

end LawfulGentzen

end LO