import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLine
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOver
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceChartPolynomial

/-! # The standard chart of the projective line

The standard chart of `P¹_k`: the affine line `A¹_k = Spec k[t]` is isomorphic to the open subset
`D₊(x₀)` of `P¹` via `t ↦ [1 : t]`, and a univariate polynomial `p ∈ k[t]` is regarded as a
function on an open subset `O` of `A¹` (`polynomialSection O p`, a section of the structure sheaf).
This is the chart in which the fibre coordinate is homogenized in Theorem 4.2 of the
paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The chart uses the standard grading of `k[x₀, x₁]` (given by `letI` in the definition of
   `ProjectiveSpace`); it is made a local instance in this file. -/

attribute [local instance] MvPolynomial.gradedAlgebra

/- The chart ring homomorphism `ψ : k[x₀,x₁]_(x₀)` (degree-zero homogeneous localization)
   `→ k[t] = MvPolynomial (ULift (Fin 1)) k`: send `x₀ ↦ 1`, `x₁ ↦ t` (the image of `x₀` is a unit),
   extend along `k[x₀,x₁] → k[x₀,x₁]_{x₀}` by the universal property of the localization, and
   compose with the inclusion `HomogeneousLocalization → Localization`; i.e. `a/x₀^n ↦ a(1, t)`. -/

noncomputable def ProjectiveLine.stdChartRingHom (k : Type u) [Field k] :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k) (MvPolynomial.X 0) →+*
      MvPolynomial (ULift.{u} (Fin 1)) k :=
  (IsLocalization.Away.lift (MvPolynomial.X 0 : MvPolynomial (Fin (1 + 1)) k)
      (g := (MvPolynomial.aeval (R := k) ![1, MvPolynomial.X ⟨0⟩]).toRingHom)
      (by simp)).comp
    (algebraMap _ (Localization.Away (MvPolynomial.X 0 : MvPolynomial (Fin (1 + 1)) k)))

namespace ProjectiveLine

variable (k : Type u) [Field k]

/-- The index equivalence `{j : Fin 2 // j ≠ 0} ≃ ULift (Fin 1)` (both sides are singletons). -/
def chartIndexEquiv : {j : Fin (1 + 1) // j ≠ 0} ≃ ULift.{u} (Fin 1) where
  toFun _ := ⟨0⟩
  invFun _ := ⟨1, by decide⟩
  left_inv := fun ⟨j, hj⟩ => Subtype.ext (by fin_cases j <;> first | rfl | exact (hj rfl).elim)
  right_inv := fun _ => Subsingleton.elim _ _

/-- The value of `stdChartRingHom` on the fraction `a / x₀^n` is `a(1, t)`. -/
lemma stdChartRingHom_mk (n : ℕ) (a : MvPolynomial (Fin (1 + 1)) k)
    (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k (n • 1)) :
    stdChartRingHom k (HomogeneousLocalization.Away.mk _ (ProjectiveSpace.X_mem 1 k 0) n a ha) =
      MvPolynomial.aeval ![1, MvPolynomial.X ⟨0⟩] a := by
  unfold stdChartRingHom IsLocalization.Away.lift
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'_apply, IsLocalization.lift_mk'_spec]
  simp

lemma rename_dehomogenize (a : MvPolynomial (Fin (1 + 1)) k) :
    MvPolynomial.rename (chartIndexEquiv) (ProjectiveSpace.dehomogenize 1 k 0 a) =
      MvPolynomial.aeval ![1, MvPolynomial.X ⟨0⟩] a := by
  have h : (MvPolynomial.rename (R := k) chartIndexEquiv).comp
      (ProjectiveSpace.dehomogenize 1 k 0) = MvPolynomial.aeval ![1, MvPolynomial.X ⟨0⟩] := by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j
    · simp [ProjectiveSpace.dehomogenize]
    · simp [ProjectiveSpace.dehomogenize, chartIndexEquiv]
  exact AlgHom.congr_fun h a

/-- The chart ring isomorphism `k[x₀,x₁]_(x₀) ≃+* k[t]`: `chartRingEquiv` composed with the
renaming of indices. -/
noncomputable def stdChartRingEquiv :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k)
        (MvPolynomial.X 0) ≃+*
      MvPolynomial (ULift.{u} (Fin 1)) k :=
  (ProjectiveSpace.chartRingEquiv 1 k 0).trans
    (MvPolynomial.renameEquiv k chartIndexEquiv).toRingEquiv

lemma stdChartRingHom_eq : stdChartRingHom k = (stdChartRingEquiv k : _ →+* _) := by
  refine RingHom.ext fun x => ?_
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective _ (ProjectiveSpace.X_mem 1 k 0) x
  rw [stdChartRingHom_mk]
  show _ = MvPolynomial.renameEquiv k chartIndexEquiv (ProjectiveSpace.chartToPoly 1 k 0 _)
  rw [ProjectiveSpace.chartToPoly_mk, MvPolynomial.renameEquiv_apply, rename_dehomogenize]

end ProjectiveLine

/- `A¹_k ≅ Spec k[t]` (Mathlib `AffineSpace.SpecIso`) `→ Spec k[x₀,x₁]_(x₀)` (`Spec ψ`) `→ P¹`
   (`Proj.awayι`, the open immersion of `D₊(x₀)`). -/

noncomputable def ProjectiveLine.stdChart (k : Type u) [Field k] :
    AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ⟶ ProjectiveLine k :=
  (AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)).hom ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (ProjectiveLine.stdChartRingHom k)) ≫
    AlgebraicGeometry.Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k) (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X k 0)) Nat.one_pos

/- Open immersion: isomorphism `≫ Spec ψ ≫` open immersion; `Spec ψ` is an isomorphism because
   `ψ = stdChartRingEquiv` is a ring isomorphism (`stdChartRingHom_eq`, obtained from
   `ProjectiveSpace.chartRingEquiv` composed with the renaming of indices). -/

instance ProjectiveLine.stdChart_isOpenImmersion (k : Type u) [Field k] :
    AlgebraicGeometry.IsOpenImmersion (ProjectiveLine.stdChart k) := by
  haveI : CategoryTheory.IsIso (CommRingCat.ofHom (ProjectiveLine.stdChartRingHom k)) := by
    rw [ProjectiveLine.stdChartRingHom_eq]
    exact (ProjectiveLine.stdChartRingEquiv k).toCommRingCatIso.isIso_hom
  haveI : CategoryTheory.IsIso
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (ProjectiveLine.stdChartRingHom k))) :=
    inferInstance
  haveI h1 : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (ProjectiveLine.stdChartRingHom k)) ≫
        AlgebraicGeometry.Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k) (MvPolynomial.X 0)
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X k 0)) Nat.one_pos) :=
    inferInstance
  haveI h0 : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)).hom := inferInstance
  exact @AlgebraicGeometry.IsOpenImmersion.comp _ _ _ _ _ h0 h1

/- A univariate polynomial `p` as a function on an open subset `O` of `A¹` (a section of the
   structure sheaf regarded as a module over itself): `p ↦ p(t) ∈ k[t] = Γ(Spec k[t])`, transported
   to `Γ(A¹, ⊤)` along `A¹ ≅ Spec k[t]`, then restricted along the open immersion of `O` to `Γ(O, ⊤)`. -/

noncomputable def polynomialSection {k : Type u} [Field k]
    (O : (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).Opens)
    (p : Polynomial k) :
    ((SheafOfModules.unit O.toScheme.ringCatSheaf).val.obj (Opposite.op ⊤) : Type u) :=
  O.ι.appTop.hom
    ((AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)).hom.appTop.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) k))).inv.hom
        (Polynomial.aeval (MvPolynomial.X ⟨0⟩ : MvPolynomial (ULift.{u} (Fin 1)) k) p)))

end
