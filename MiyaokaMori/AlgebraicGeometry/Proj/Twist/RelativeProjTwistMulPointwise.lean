import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMultiplicationChartSections
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistPiApp

/-! # Pointwise lemmas on the charts of a relative Proj

Small lemmas used to prove the associativity of `twistMul` on sections through the chart projections
`twistπ n U : O(n) ⟶ (c_U)_* O_U(n)` (Stacks 01LI): the chart image contains `π⁻¹U`, so `twistπ` is injective on
sections over `V ≤ π⁻¹U` (`bijective_twistπ_app`); `twistπ` commutes with the index transport `eqToHom`; sections of
`O_U(n)` are functions on points (`sectionsSubmodule`), restriction is restriction of functions, and the pointwise
value of `twistSectionMul` is the product of values.

Source: Stacks 01LI, 01MO. Used for the associativity of `twistMul` on sections (`RelativeProjTwistMulAssoc`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Restriction of a section of `O(n)` on `Proj 𝒜` is restriction of the underlying function. -/
theorem AlgebraicGeometry.Proj.twist_presheaf_map_val {σ A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (n : ℤ) {W W' : (AlgebraicGeometry.Proj 𝒜).Opens}
    (i : W ⟶ W') (s : Γ(AlgebraicGeometry.Proj.twist 𝒜 n, W')) (p : W) :
    Subtype.val ((AlgebraicGeometry.Proj.twist 𝒜 n).presheaf.map i.op s :
        MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 n W) p =
      Subtype.val (s : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 n W') ⟨p.1, leOfHom i p.2⟩ := rfl

/-- The value of `twistSectionMul s t` at a point is the product of the values (Stacks 01MO). -/
theorem AlgebraicGeometry.Proj.twistSectionMul_val {σ A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (a b : ℤ) (W : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : Γ(AlgebraicGeometry.Proj.twist 𝒜 a, W)) (t : Γ(AlgebraicGeometry.Proj.twist 𝒜 b, W)) (p : W) :
    Subtype.val (AlgebraicGeometry.Proj.twistSectionMul 𝒜 a b W s t :
        MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 (a + b) W) p =
      Subtype.val (s : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 a W) p *
        Subtype.val (t : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 b W) p := rfl

/-- Sections of an `O_X`-module commute with restriction (element form, restriction on the outside). -/
theorem AlgebraicGeometry.Scheme.Modules.Hom.map_app_eq_app_map {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) {W W' : X.Opens} (h : W' ≤ W) (x : Γ(M, W)) :
    N.presheaf.map (homOfLE h).op (φ.app W x) = φ.app W' (M.presheaf.map (homOfLE h).op x) :=
  (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x).symm

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- Restriction of a section of the pushed-forward chart twist `(c_{W'})_* O_{W'}(m)` is restriction of the
underlying function (`pushforward_twist_presheaf_map_apply` in the spelling used here). -/
theorem pushforward_twist_map_val (W' : X.AffineZariskiSite) (m : ℤ)
    {Ω Ω₀ : (relativeProj S).left.Opens} (j : Ω ≤ Ω₀)
    (y : Γ((AlgebraicGeometry.Scheme.Modules.pushforward (S.toGradedAffineAlgebra.projChart W')).obj
      (AlgebraicGeometry.Proj.twist (S.toGradedAffineAlgebra.grading W') m), Ω₀))
    (p : (S.toGradedAffineAlgebra.projChart W' ⁻¹ᵁ Ω :
      (AlgebraicGeometry.Proj (S.toGradedAffineAlgebra.grading W')).Opens)) :
    Subtype.val (((AlgebraicGeometry.Scheme.Modules.pushforward (S.toGradedAffineAlgebra.projChart W')).obj
        (AlgebraicGeometry.Proj.twist (S.toGradedAffineAlgebra.grading W') m)).presheaf.map (homOfLE j).op y :
        MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (S.toGradedAffineAlgebra.grading W') m
          (S.toGradedAffineAlgebra.projChart W' ⁻¹ᵁ Ω)) p =
      Subtype.val (y : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (S.toGradedAffineAlgebra.grading W') m
          (S.toGradedAffineAlgebra.projChart W' ⁻¹ᵁ Ω₀))
        ⟨p.1, (S.toGradedAffineAlgebra.projChart W').preimage_mono j p.2⟩ := rfl

/-- `π⁻¹U` is contained in the image of the chart `c_U = projChart (affineSite U)` (`ι_U = e_U ≫ c_U`). -/
theorem preimage_le_opensRange_projChart (U : X.affineOpens) :
    (relativeProj S).hom ⁻¹ᵁ U.1 ≤
      (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U)).opensRange := by
  intro x hx
  refine ⟨(affineIso S U).hom.base ⟨x, hx⟩, ?_⟩
  change ((affineIso S U).hom ≫ chartMap S U).base ⟨x, hx⟩ = x
  rw [← ι_eq_affineIso_comp_chartMap]
  rfl

/-- **Stacks 01LI on sections**: `twistπ m U` is injective on sections over `V ≤ π⁻¹U`. -/
theorem twistπ_app_injective (m : ℤ) (U : X.affineOpens) (V : (relativeProj S).left.Opens)
    (hV : V ≤ (relativeProj S).hom ⁻¹ᵁ U.1) :
    Function.Injective ((S.toGradedAffineAlgebra.twistπ m (AlgebraicGeometry.Scheme.affineSite U)).app V) :=
  (S.toGradedAffineAlgebra.bijective_twistπ_app m (AlgebraicGeometry.Scheme.affineSite U) V
    (hV.trans (preimage_le_opensRange_projChart S U))).1

/-- `twistπ` commutes with the index transport `eqToHom (congrArg (twist S) h)`. -/
theorem twistπ_app_eqToHom_app (U : X.AffineZariskiSite) {n m : ℤ} (h : n = m)
    (V : (relativeProj S).left.Opens) (w : Γ(twist S n, V)) :
    (S.toGradedAffineAlgebra.twistπ m U).app V ((eqToHom (congrArg (twist S) h)).app V w) =
      (eqToHom (congrArg (fun k => (AlgebraicGeometry.Scheme.Modules.pushforward (S.toGradedAffineAlgebra.projChart U)).obj
        (AlgebraicGeometry.Proj.twist (S.toGradedAffineAlgebra.grading U) k)) h)).app V
        ((S.toGradedAffineAlgebra.twistπ n U).app V w) := by
  subst h
  simp only [eqToHom_refl, AlgebraicGeometry.Scheme.Modules.Hom.id_app]
  rfl

/-- The index transport on the pushed-forward chart twist does not change the underlying function. -/
theorem eqToHom_pushforward_twist_app_val (U : X.AffineZariskiSite) {n m : ℤ} (h : n = m)
    (V : (relativeProj S).left.Opens)
    (w : Γ((AlgebraicGeometry.Scheme.Modules.pushforward (S.toGradedAffineAlgebra.projChart U)).obj
      (AlgebraicGeometry.Proj.twist (S.toGradedAffineAlgebra.grading U) n), V))
    (p : (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ V : (AlgebraicGeometry.Proj (S.toGradedAffineAlgebra.grading U)).Opens)) :
    Subtype.val ((eqToHom (congrArg (fun k => (AlgebraicGeometry.Scheme.Modules.pushforward
        (S.toGradedAffineAlgebra.projChart U)).obj
        (AlgebraicGeometry.Proj.twist (S.toGradedAffineAlgebra.grading U) k)) h)).app V w :
        MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (S.toGradedAffineAlgebra.grading U) m
          (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ V)) p =
      Subtype.val (w : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (S.toGradedAffineAlgebra.grading U) n
          (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ V)) p := by
  subst h
  rfl

/-- `e_U ''ᵁ A = c_U ⁻¹ᵁ (ι_U ''ᵁ A)` with the chart spelled `projChart (affineSite U)`
(`affineIso_image_eq_chartMap_preimage`). -/
theorem affineIso_image_eq_projChart_preimage (U : X.affineOpens)
    (A : ((relativeProj S).hom ⁻¹ᵁ U.1).toScheme.Opens) :
    (affineIso S U).hom ''ᵁ A =
      S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U) ⁻¹ᵁ
        (((relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A) :=
  affineIso_image_eq_chartMap_preimage S U A

end AlgebraicGeometry.Scheme.relativeProj

end
