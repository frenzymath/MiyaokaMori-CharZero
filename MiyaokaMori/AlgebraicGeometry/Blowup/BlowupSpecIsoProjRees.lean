import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.ReesAlgebraSheafAffineSections
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks01og
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceGradedRingIsos

/-! # The blowup of an affine scheme is the Proj of the Rees algebra, over the base

Stacks 0804 for a **whole affine scheme** `X = Spec A`, **with compatibility of the structure
morphisms**: the blowup `Bl_J Spec A` of an ideal `J ⊆ A` is isomorphic to the Proj of the Rees
algebra `⊕ₙ Jⁿ`, and the isomorphism turns the structure morphism of the blowup into
`Proj.toSpecZero ≫ Spec.map (algebraMap A (Rees J)₀)`.

Source: Stacks 0804 (Divisors, Lemma "lemma-blowing-up-affine") and Stacks 01NQ (the relative Proj
over an affine open is a Proj); used for Stacks 0AGQ (1).

Relation to `blowup_preimage_affine` (Stacks 0804): that statement only gives
`Nonempty (b⁻¹(U) ≅ Proj(Rees))`, **without** compatibility of the structure morphisms, whereas the
computation of the closed fibre in 0AGQ (base change along `Spec A → Spec κ`) needs the isomorphism
over `Spec A`; the present statement is the strengthened version for `U = ⊤`, `X = Spec A`.

Route (see the docstring of the theorem): the chart `projChart ⊤ : Proj S(⊤) → Bl_I Spec A` of the
relative Proj is an isomorphism (its image is `π⁻¹(⊤) = ⊤`), `S(⊤) ≅ _root_.reesAlgebra J` as graded
rings compatibly with the structure maps (`exists_reesAlgebra_sectionsRing_equiv_of_ringEquiv`, via
`ΓSpecIso A`), and `Proj.isoOfGradedRingEquiv` is compatible with `toSpecZero`. The needed statement
`Γ(U, Iⁿ) = I(U)^n` comes from `mem_powSubmodule_affine_iff`, directly from Mathlib's
`IdealSheafData.map_ideal`. Stacks 01NQ (`relativeProj.affineIso`) is not used; the chart
`projChart ⊤` being an isomorphism replaces it.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData)

/-- `⊤` as an affine open of an affine scheme. -/
abbrev topAffineOpen (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine X] :
    X.affineOpens := ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩

/-- The chart `Proj S(⊤) → Proj_X S` of a relative Proj over an affine scheme is an isomorphism:
it is an open immersion with image `π⁻¹(⊤) = ⊤`. -/
theorem isIso_projChart_top (S : X.GradedAffineAlgebra) [AlgebraicGeometry.IsAffine X] :
    IsIso (S.projChart (AlgebraicGeometry.Scheme.affineSite (topAffineOpen X))) := by
  refine AlgebraicGeometry.isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
  rw [← S.proj_preimage_eq_opensRange]
  exact AlgebraicGeometry.Scheme.Hom.preimage_top _

/-- **Blowup of an affine scheme along an ideal sheaf, generic form.** For an affine scheme `X`,
a ring model `ψ : Γ(X, ⊤) ≃+* A` of its global sections and an ideal `J ⊆ A` corresponding to
`I(⊤)`, the blowup `Bl_I X = Proj_X (⊕ Iⁿ)` is `Proj (⊕ Jⁿ)` compatibly with the structure maps to
`Spec A` (`X → Spec Γ(X, ⊤) → Spec A` via `X.isoSpec` and `ψ⁻¹`).

Proof: the chart `projChart ⊤ : Proj S(⊤) → Bl_I X` is an isomorphism (`isIso_projChart_top`) with
`projChart ⊤ ≫ π = projToOpen ⊤ ≫ ⊤.ι` (`projChart_hom`) and
`projToOpen ⊤ = toSpecZero S(⊤) ≫ Spec.map (unitZero ⊤) ≫ isoSpec.inv`; `S(⊤) ≅ _root_.reesAlgebra J` as graded
rings with `sectionsUnitHom ⊤ r ↦ algebraMap A _ (ψ r)` (`exists_reesAlgebra_sectionsRing_equiv_of_ringEquiv`),
and `Proj.isoOfGradedRingEquiv` is compatible with `toSpecZero` (`isoOfGradedRingEquiv_hom_toSpecZero`);
the two ring maps `A → S(⊤)₀` (`(φ⁻¹)₀ ∘ algebraMap` and `unitZero ⊤ ∘ ψ⁻¹`) agree by the unit
compatibility, and `isoSpec.inv ≫ ⊤.ι = fromSpec ⊤ = X.isoSpec.inv` (`fromSpec_top`). -/
theorem blowup_iso_proj_reesGrading_of_isAffine [AlgebraicGeometry.IsAffine X] {A : Type u} [CommRing A]
    (i : Γ(X, ⊤) ≅ CommRingCat.of A) (J : Ideal A)
    (hJ : ∀ x, x ∈ I.ideal (topAffineOpen X) ↔ i.hom.hom x ∈ J) :
    ∃ e : (AlgebraicGeometry.Scheme.blowup I).left ≅ AlgebraicGeometry.Proj (Ideal.reesGrading J),
      e.hom ≫ AlgebraicGeometry.Proj.toSpecZero (Ideal.reesGrading J) ≫
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A (Ideal.reesGrading J 0))) =
        (AlgebraicGeometry.Scheme.blowup I).hom ≫ X.isoSpec.hom ≫ AlgebraicGeometry.Spec.map i.inv := by
  obtain ⟨φ, he, hunit⟩ : ∃ φ : I.reesAlgebra.sectionsRing ⊤ ≃+* _root_.reesAlgebra J,
      (∀ (m : ℕ) (x : I.reesAlgebra.sectionsRing ⊤),
        x ∈ I.reesAlgebra.sectionsGrading ⊤ m ↔ φ x ∈ Ideal.reesGrading J m) ∧
      ∀ r : Γ(X, ⊤), φ (I.reesAlgebra.sectionsUnitHom ⊤ r) = algebraMap A (_root_.reesAlgebra J) (i.hom.hom r) :=
    I.exists_reesAlgebra_sectionsRing_equiv_of_ringEquiv (topAffineOpen X)
      i.commRingCatIsoToRingEquiv J hJ
  -- Proj of the graded ring isomorphism
  obtain ⟨e₂, h₂⟩ : ∃ e₂ : AlgebraicGeometry.Proj (I.reesAlgebra.sectionsGrading ⊤) ≅
      AlgebraicGeometry.Proj (Ideal.reesGrading J),
      e₂.hom ≫ AlgebraicGeometry.Proj.toSpecZero (Ideal.reesGrading J) =
        AlgebraicGeometry.Proj.toSpecZero (I.reesAlgebra.sectionsGrading ⊤) ≫
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (AlgebraicGeometry.Proj.gradedRingHomOfRingEquivSymm φ he).gradedZeroRingHom) :=
    ⟨_, AlgebraicGeometry.Proj.isoOfGradedRingEquiv_hom_toSpecZero φ he⟩
  -- the chart at `⊤`, restated with the grading spelled `I.reesAlgebra.sectionsGrading ⊤` throughout
  have hiso := AlgebraicGeometry.Scheme.IdealSheafData.isIso_projChart_top I.reesAlgebra.toGradedAffineAlgebra
  let u₀ : Γ(X, ⊤) →+* I.reesAlgebra.sectionsGrading ⊤ 0 :=
    I.reesAlgebra.toGradedAffineAlgebra.unitZero (AlgebraicGeometry.Scheme.affineSite (topAffineOpen X))
  have hchart : I.reesAlgebra.toGradedAffineAlgebra.projChart
        (AlgebraicGeometry.Scheme.affineSite (topAffineOpen X)) ≫ (AlgebraicGeometry.Scheme.blowup I).hom =
      (AlgebraicGeometry.Proj.toSpecZero (I.reesAlgebra.sectionsGrading ⊤) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom u₀) ≫
        (AlgebraicGeometry.isAffineOpen_top X).isoSpec.inv) ≫ (⊤ : X.Opens).ι :=
    I.reesAlgebra.toGradedAffineAlgebra.projChart_hom _
  obtain ⟨e₁, h₁⟩ : ∃ e₁ : (AlgebraicGeometry.Scheme.blowup I).left ≅
      AlgebraicGeometry.Proj (I.reesAlgebra.sectionsGrading ⊤),
      e₁.hom ≫ ((AlgebraicGeometry.Proj.toSpecZero (I.reesAlgebra.sectionsGrading ⊤) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom u₀) ≫
        (AlgebraicGeometry.isAffineOpen_top X).isoSpec.inv) ≫ (⊤ : X.Opens).ι) =
        (AlgebraicGeometry.Scheme.blowup I).hom :=
    ⟨(asIso (I.reesAlgebra.toGradedAffineAlgebra.projChart
      (AlgebraicGeometry.Scheme.affineSite (topAffineOpen X)))).symm,
      (congrArg (fun m => (asIso (I.reesAlgebra.toGradedAffineAlgebra.projChart
        (AlgebraicGeometry.Scheme.affineSite (topAffineOpen X)))).inv ≫ m) hchart).symm.trans
        (Iso.inv_hom_id_assoc (asIso (I.reesAlgebra.toGradedAffineAlgebra.projChart
          (AlgebraicGeometry.Scheme.affineSite (topAffineOpen X)))) (AlgebraicGeometry.Scheme.blowup I).hom)⟩
  -- the base: `isoSpec.inv ≫ ⊤.ι ≫ X.isoSpec.hom = 𝟙`
  have hbase : (AlgebraicGeometry.isAffineOpen_top X).isoSpec.inv ≫ (⊤ : X.Opens).ι ≫
      X.isoSpec.hom ≫ AlgebraicGeometry.Spec.map i.inv = AlgebraicGeometry.Spec.map i.inv := by
    rw [← Category.assoc, AlgebraicGeometry.IsAffineOpen.isoSpec_inv_ι,
      AlgebraicGeometry.IsAffineOpen.fromSpec_top, Iso.inv_hom_id_assoc]
  -- the two ring maps `A → S(⊤)₀` agree, at the level of `Spec`
  have hmaps : AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (AlgebraicGeometry.Proj.gradedRingHomOfRingEquivSymm φ he).gradedZeroRingHom :
          CommRingCat.of (Ideal.reesGrading J 0) ⟶ CommRingCat.of (I.reesAlgebra.sectionsGrading ⊤ 0)) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A (Ideal.reesGrading J 0)) :
          CommRingCat.of A ⟶ CommRingCat.of (Ideal.reesGrading J 0)) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom u₀ :
          Γ(X, ⊤) ⟶ CommRingCat.of (I.reesAlgebra.sectionsGrading ⊤ 0)) ≫
        AlgebraicGeometry.Spec.map i.inv := by
    rw [← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_comp]
    refine congrArg AlgebraicGeometry.Spec.map ?_
    apply CommRingCat.hom_ext
    refine RingHom.ext fun a => ?_
    apply Subtype.ext
    change φ.symm (algebraMap A (_root_.reesAlgebra J) a) =
      I.reesAlgebra.sectionsUnitHom ⊤ (i.inv.hom a)
    rw [φ.symm_apply_eq, hunit]
    exact congrArg (algebraMap A (_root_.reesAlgebra J))
      (congrArg (fun f => f.hom a) i.inv_hom_id).symm
  -- assemble
  refine ⟨e₁ ≪≫ e₂, ?_⟩
  rw [Iso.trans_hom, Category.assoc, ← Category.assoc e₂.hom, h₂, Category.assoc, ← h₁]
  simp only [Category.assoc]
  rw [hbase]
  exact congrArg (fun f => e₁.hom ≫ AlgebraicGeometry.Proj.toSpecZero (I.reesAlgebra.sectionsGrading ⊤) ≫ f)
    hmaps

end AlgebraicGeometry.Scheme.IdealSheafData

/-- **Stacks 0804 over `Spec A`, with the structure morphisms.** For a commutative ring `A` and an
ideal `J ⊆ A`, let `I := ofIdealTop (J.map ΓSpecIso.inv)` be the corresponding ideal sheaf on `Spec A`.
Then `Bl_I Spec A` is isomorphic, as a scheme over `Spec A`, to `Proj(⊕ₙ Jⁿ)` (`Ideal.reesGrading J`,
whose degree-`0` part is the image of `A`):
`∃ e : (blowup I).left ≅ Proj (reesGrading J)` with
`e.hom ≫ toSpecZero ≫ Spec.map (algebraMap A (Rees J)₀) = (blowup I).hom`.

**Proof.** Special case `X = Spec A`, `ψ = ΓSpecIso A` of the generic
`blowup_iso_proj_reesGrading_of_isAffine` above (whose docstring gives the argument: the chart at `⊤` is an
isomorphism, `S(⊤) ≅ _root_.reesAlgebra J` as graded rings via `ψ`, `Proj.isoOfGradedRingEquiv` compatible with
`toSpecZero`). Here `I(⊤) = (J.map ψ⁻¹).map (res_{⊤≤⊤}) = J.map ψ⁻¹` (`ofIdealTop_ideal`, `Ideal.map_id`),
and the base map `X.isoSpec.hom ≫ Spec.map ψ⁻¹ = Spec.map (ΓSpecIso A).hom ≫ Spec.map (ΓSpecIso A).inv = 𝟙`
(`isoSpec_Spec_hom`, `Spec.map_comp`, `Iso.inv_hom_id`).

Edge cases: for `J = ⊤` the Rees algebra is `A[X]`, `Proj = Spec A`, the blowup is the identity, and
the statement holds; for `J = ⊥` the Rees algebra is `A` (in degree `0`), `Proj = ∅`, and
`Bl_⊥ Spec A = ∅` (as in Stacks 0804), so the statement holds; for the zero ring `A` both sides are
the empty scheme. No Noetherian hypothesis is needed. -/
theorem AlgebraicGeometry.Scheme.blowup_spec_iso_proj_reesGrading_over (A : Type u) [CommRing A]
    (J : Ideal A) :
    ∃ e : (AlgebraicGeometry.Scheme.blowup
        (AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
          (J.map (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))).left ≅
        AlgebraicGeometry.Proj (Ideal.reesGrading J),
      e.hom ≫ AlgebraicGeometry.Proj.toSpecZero (Ideal.reesGrading J) ≫
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A (Ideal.reesGrading J 0))) =
        (AlgebraicGeometry.Scheme.blowup
          (AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
            (J.map (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))).hom := by
  have hJ : ∀ x, x ∈ (AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
      (J.map (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).ideal
        (AlgebraicGeometry.Scheme.IdealSheafData.topAffineOpen (AlgebraicGeometry.Spec (CommRingCat.of A))) ↔
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom x ∈ J := by
    intro x
    have h1 : (AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
        (J.map (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).ideal
          (AlgebraicGeometry.Scheme.IdealSheafData.topAffineOpen (AlgebraicGeometry.Spec (CommRingCat.of A))) =
        J.map (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := by
      change (J.map (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).map
        ((AlgebraicGeometry.Spec (CommRingCat.of A)).presheaf.map
          (homOfLE (le_top : (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of A)).Opens) ≤ ⊤)).op).hom = _
      have e : (homOfLE (le_top : (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of A)).Opens) ≤ ⊤)).op =
          𝟙 (op (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of A)).Opens)) := rfl
      rw [e, (AlgebraicGeometry.Spec (CommRingCat.of A)).presheaf.map_id, CommRingCat.hom_id,
        Ideal.map_id]
    rw [h1]
    constructor
    · intro hx
      have hle : J.map (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ≤
          J.comap (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom := by
        rw [Ideal.map_le_iff_le_comap]
        intro y hy
        rw [Ideal.mem_comap, Ideal.mem_comap]
        have hy' : (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
            ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom y) = y :=
          congrArg (fun f => f.hom y) (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id
        rwa [hy']
      exact hle hx
    · intro hx
      have hx' : (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
          ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom x) = x :=
        congrArg (fun f => f.hom x) (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id
      rw [← hx']
      exact Ideal.mem_map_of_mem _ hx
  obtain ⟨e, he⟩ := AlgebraicGeometry.Scheme.IdealSheafData.blowup_iso_proj_reesGrading_of_isAffine
    (AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
      (J.map (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)) J hJ
  refine ⟨e, he.trans ?_⟩
  rw [AlgebraicGeometry.Scheme.isoSpec_Spec_hom, ← AlgebraicGeometry.Spec.map_comp, Iso.inv_hom_id,
    AlgebraicGeometry.Spec.map_id, Category.comp_id]

end
