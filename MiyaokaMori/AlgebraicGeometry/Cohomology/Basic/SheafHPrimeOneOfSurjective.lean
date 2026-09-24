import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafHasextInstance
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLes

/-! # Vanishing of `H'^1` from surjectivity on sections

Let `0 → F → G → H → 0` be a short exact sequence of `O_X`-modules and `U ⊆ X` open. If
`G(U) → H(U)` is surjective and `H'^1(U, G) = 0`, then `H'^1(U, F) = 0` (`H'` is Mathlib's
`Sheaf.H'` of the underlying abelian sheaves).

Proof sketch:
1. Let `A = ℤ[h_U]^#` (the sheafification of the free abelian presheaf on the representable
   presheaf `h_U`); then `H'^p(U, −) = Ext^p(A, −)`. The underlying short complex of abelian sheaves
   is still short exact (`bridge_shortExact_toSheaf`).
2. Let `x ∈ Ext^1(A, F)`. Then `x ∘ f ∈ Ext^1(A, G) = 0`, so by
   `Abelian.Ext.covariant_sequence_exact₁`, `x = x₃ ∘ δ` with `x₃ ∈ Ext^0(A, H) = Hom(A, H)`.
3. `Hom(A, −) ≅ Γ(U, −)` naturally in the sheaf: sheafification adjunction, free abelian group
   adjunction and the Yoneda lemma. Only the lifting statement is needed: `φ : ℤ[h_U]^# → H`
   corresponds to `q ∈ H(U)`; a preimage `i ∈ G(U)` corresponds back to `ψ` with `ψ ≫ g = φ`
   (`exists_lift_of_surjective`, valid on any site). Since `G(U) → H(U)` is surjective,
   `x₃ = x₂ ∘ g`, hence `x = x₂ ∘ (g ∘ δ) = 0` (`ShortExact.comp_extClass`).

Source: the first step of the proof of Stacks 01EW (the `H^1` case); Stacks 01E0 (long exact
sequence).
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

/-- A morphism from the free abelian sheaf on a representable presheaf lifts along any morphism
that is surjective on sections over `U`. -/
theorem exists_lift_of_surjective (U : C) {G H : Sheaf J AddCommGrpCat.{u}} (g : G ⟶ H)
    (hsurj : Function.Surjective (g.hom.app (op U)))
    (φ : (presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ H) :
    ∃ ψ : (presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ G,
      ψ ≫ g = φ := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{u}
  let adj2 := AddCommGrpCat.adj.{u}.whiskerRight Cᵒᵖ
  let φ' := adj.homEquiv _ _ φ
  let φ'' := adj2.homEquiv (yoneda.obj U) H.obj φ'
  obtain ⟨i, hi⟩ := hsurj (yonedaEquiv φ'')
  let ψ'' : yoneda.obj U ⟶ G.obj ⋙ forget AddCommGrpCat := yonedaEquiv.symm i
  refine ⟨(adj.homEquiv _ _).symm ((adj2.homEquiv _ _).symm ψ''), ?_⟩
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply (adj2.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact hi

/-- Abstract step: `Hom(A, X₂) → Hom(A, X₃)` surjective and `Ext¹(A, X₂) = 0` ⇒ `Ext¹(A, X₁) = 0`. -/
theorem ext_one_subsingleton {D : Type*} [Category D] [Abelian D] [HasExt D] {T : ShortComplex D}
    (hT : T.ShortExact) (A : D) (hlift : ∀ φ : A ⟶ T.X₃, ∃ ψ : A ⟶ T.X₂, ψ ≫ T.g = φ)
    (h2 : Subsingleton (Ext A T.X₂ 1)) : Subsingleton (Ext A T.X₁ 1) := by
  refine ⟨fun a b => ?_⟩
  have key : ∀ x : Ext A T.X₁ 1, x = 0 := by
    intro x
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ A hT x (Subsingleton.elim _ _) (zero_add 1)
    obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective _ _).2 x₃
    obtain ⟨ψ, rfl⟩ := hlift φ
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero, hT.comp_extClass, Ext.comp_zero]
  rw [key a, key b]

/-- One step of the long exact sequence: `Ext^{p+1}(A, X₂) = 0` and `Ext^p(A, X₃) = 0` ⇒
`Ext^{p+1}(A, X₁) = 0`. -/
theorem ext_succ {D : Type*} [Category D] [Abelian D] [HasExt D] {T : ShortComplex D}
    (hT : T.ShortExact) (A : D) (p : ℕ) (h2 : Subsingleton (Ext A T.X₂ (p + 1)))
    (h3 : Subsingleton (Ext A T.X₃ p)) : Subsingleton (Ext A T.X₁ (p + 1)) := by
  refine ⟨fun a b => ?_⟩
  have key : ∀ x : Ext A T.X₁ (p + 1), x = 0 := by
    intro x
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ A hT x (Subsingleton.elim _ _) rfl
    rw [Subsingleton.elim x₃ 0, Ext.zero_comp]
  rw [key a, key b]

end SheafHPrimeAux

theorem AlgebraicGeometry.Scheme.Modules.hPrime_one_subsingleton_of_surjective
    {X : AlgebraicGeometry.Scheme.{u}} (S : CategoryTheory.ShortComplex X.Modules)
    (hS : S.ShortExact) (U : X.Opens) (hsurj : Function.Surjective (S.g.app U))
    (h2 : Subsingleton (S.X₂.toAddCommGrpSheaf.H' 1 U)) :
    Subsingleton (S.X₁.toAddCommGrpSheaf.H' 1 U) := by
  have hT := bridge_shortExact_toSheaf
    (ShortComplex.mk (C := SheafOfModules.{u} X.ringCatSheaf) S.f S.g S.zero) hS
  exact SheafHPrimeAux.ext_one_subsingleton hT
    ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free))
    (fun φ => SheafHPrimeAux.exists_lift_of_surjective U _ hsurj φ) h2

end
