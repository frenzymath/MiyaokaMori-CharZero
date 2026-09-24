import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafHasextInstance
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLes
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafHPrimeOneOfSurjective

/-! # Sections and `H'` along a short exact sequence

Let `0 → F → G → R → 0` be a short exact sequence of `O_X`-modules and `V ⊆ X` open.
(a) If `H^1(V, F) = 0`, then `G(V) → R(V)` is surjective;
(b) if `H^p(V, G) = 0` and `H^{p+1}(V, F) = 0`, then `H^p(V, R) = 0`.

Proof: `H^p(V, −) = Ext^p(ℤ_V, −)` (Mathlib's `Sheaf.H'`, with `ℤ_V` the free abelian sheaf on the
representable presheaf), and the long exact `Ext` sequence in the second variable
(`Ext.covariant_sequence_exact₃`): (a) `t ∈ R(V)` corresponds to `φ : ℤ_V → R`, whose connecting
image lies in `Ext^1(ℤ_V, F) = 0`, so `φ = ψ ≫ g` and the section corresponding to `ψ` is a
preimage; (b) the connecting image of `x ∈ Ext^p(ℤ_V, R)` lies in `Ext^{p+1}(ℤ_V, F) = 0`, so `x`
comes from `Ext^p(ℤ_V, G) = 0`.

Source: step 2 of the proof of Hartshorne III.4.5 ("we therefore have an exact sequence
`0 → F(U_σ) → G(U_σ) → R(U_σ) → 0` … by (3.5)") and the long exact sequence of III.1.1A.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace SheafHPrimeAux

open CategoryTheory.Abelian

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}]

/-- Converse of `exists_lift_of_surjective`: if every `ℤ_U → H` lifts along `g`, then `g` is
surjective on sections over `U`. -/
theorem surjective_of_exists_lift (U : C) {G H : Sheaf J AddCommGrpCat.{u}} (g : G ⟶ H)
    (hlift : ∀ φ : (presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ H,
      ∃ ψ : (presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ G,
        ψ ≫ g = φ) :
    Function.Surjective (g.hom.app (op U)) := by
  intro t
  let adj := sheafificationAdjunction J AddCommGrpCat.{u}
  let adj2 := AddCommGrpCat.adj.{u}.whiskerRight Cᵒᵖ
  let t'' : yoneda.obj U ⟶ H.obj ⋙ forget AddCommGrpCat := yonedaEquiv.symm t
  obtain ⟨ψ, hψ⟩ := hlift ((adj.homEquiv _ _).symm ((adj2.homEquiv _ _).symm t''))
  refine ⟨yonedaEquiv (adj2.homEquiv _ _ (adj.homEquiv _ _ ψ)), ?_⟩
  have h1 := congrArg (adj.homEquiv _ _) hψ
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply] at h1
  have h2 := congrArg (adj2.homEquiv _ _) h1
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply] at h2
  have h3 := congrArg yonedaEquiv h2
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply] at h3
  exact h3

/-- Abstract step: `Ext¹(A, X₁) = 0` ⇒ every `A → X₃` lifts along `g`. -/
theorem exists_lift_of_ext_one_subsingleton {D : Type*} [Category D] [Abelian D] [HasExt D]
    {T : ShortComplex D} (hT : T.ShortExact) (A : D) (h1 : Subsingleton (Ext A T.X₁ 1))
    (φ : A ⟶ T.X₃) : ∃ ψ : A ⟶ T.X₂, ψ ≫ T.g = φ := by
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ A hT (Ext.mk₀ φ) (zero_add 1)
    (Subsingleton.elim _ _)
  obtain ⟨ψ, rfl⟩ := (Ext.mk₀_bijective _ _).2 x₂
  rw [Ext.mk₀_comp_mk₀] at hx₂
  exact ⟨ψ, (Ext.mk₀_bijective _ _).1 hx₂⟩

/-- One step of the long exact sequence: `Ext^p(A, X₂) = 0` and `Ext^{p+1}(A, X₁) = 0` ⇒
`Ext^p(A, X₃) = 0`. -/
theorem ext_quotient {D : Type*} [Category D] [Abelian D] [HasExt D] {T : ShortComplex D}
    (hT : T.ShortExact) (A : D) (p : ℕ) (h2 : Subsingleton (Ext A T.X₂ p))
    (h1 : Subsingleton (Ext A T.X₁ (p + 1))) : Subsingleton (Ext A T.X₃ p) := by
  refine ⟨fun a b => ?_⟩
  have key : ∀ x : Ext A T.X₃ p, x = 0 := by
    intro x
    obtain ⟨x₂, rfl⟩ := Ext.covariant_sequence_exact₃ A hT x rfl (Subsingleton.elim _ _)
    rw [Subsingleton.elim x₂ 0, Ext.zero_comp]
  rw [key a, key b]

end SheafHPrimeAux

/-- (a) `H^1(V, F) = 0` ⇒ `G(V) → R(V)` is surjective. -/
theorem AlgebraicGeometry.Scheme.Modules.surjective_sections_of_hPrime_one
    {X : AlgebraicGeometry.Scheme.{u}} (S : CategoryTheory.ShortComplex X.Modules)
    (hS : S.ShortExact) (V : X.Opens)
    (h1 : Subsingleton (S.X₁.toAddCommGrpSheaf.H' 1 V)) :
    Function.Surjective (S.g.app V) := by
  have hT := bridge_shortExact_toSheaf
    (ShortComplex.mk (C := SheafOfModules.{u} X.ringCatSheaf) S.f S.g S.zero) hS
  exact SheafHPrimeAux.surjective_of_exists_lift V _
    (fun φ => SheafHPrimeAux.exists_lift_of_ext_one_subsingleton hT _ h1 φ)

/-- (b) `H^p(V, G) = 0` and `H^{p+1}(V, F) = 0` ⇒ `H^p(V, R) = 0`. -/
theorem AlgebraicGeometry.Scheme.Modules.hPrime_subsingleton_quotient
    {X : AlgebraicGeometry.Scheme.{u}} (S : CategoryTheory.ShortComplex X.Modules)
    (hS : S.ShortExact) (V : X.Opens) (p : ℕ)
    (h2 : Subsingleton (S.X₂.toAddCommGrpSheaf.H' p V))
    (h1 : Subsingleton (S.X₁.toAddCommGrpSheaf.H' (p + 1) V)) :
    Subsingleton (S.X₃.toAddCommGrpSheaf.H' p V) := by
  have hT := bridge_shortExact_toSheaf
    (ShortComplex.mk (C := SheafOfModules.{u} X.ringCatSheaf) S.f S.g S.zero) hS
  exact SheafHPrimeAux.ext_quotient hT _ p h2 h1

end
