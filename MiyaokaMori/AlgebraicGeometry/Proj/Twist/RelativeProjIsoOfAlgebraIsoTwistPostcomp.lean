import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistPushTransition

/-! # General lemmas for the twist comparison of a relative Proj isomorphism

Three small general facts used by `RelativeProjIsoOfAlgebraIsoTwist` to glue the chart-level
comparison maps of the twisting sheaves along the limit defining `O_{Proj_X S}(d)`:

* `Proj.twistPushTransition_postcomp`: the comparison map `T(f)` (Stacks 01MX/01NP) along charts
  `ιA ≫ g`, `ιB ≫ g` is the pushforward by `g` of the comparison map along `ιA`, `ιB`, up to the
  canonical identifications `pushforwardComp` (all identities on sections). Proved pointwise from
  `twistPushTransition_app_apply`, exactly like `twistPushTransition_comp`.
* `Proj.twistPushTransition_congr`: `T(f)` depends only on `f` (as a graded ring homomorphism).
* `CategoryTheory.comp₂_eq_comp₂_of_heq_bridge`: the four-morphism version of the bridge lemma (a twin of
  `comp_eq_comp_of_heq_bridge` in `VeroneseTwistPullback`, with implicit objects)
  `comp_eq_of_heq_bridge` of `RelativeProjTwistComp`, used to transport an equation
  `f ≫ g = f₂ ≫ g₂` between two spellings whose objects and morphisms agree only up to
  definitional unfolding (each `HEq` is checked by the kernel at the top level, where it is cheap).

This module deliberately does **not** make `Proj.twist` irreducible: the pointwise proof of
`twistPushTransition_postcomp` has to see the sections of `O(n)` as `sectionsSubmodule`.

Source: Stacks 01MX, 01NP.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj

variable {σ τ A B : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- Post-composing the charts with `g : Y ⟶ Z`: `T(f)` along `ιA ≫ g`, `ιB ≫ g` is `g_*` of `T(f)`
along `ιA`, `ιB`, conjugated by `pushforwardComp` (identities on sections). -/
theorem twistPushTransition_postcomp (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) (n : ℤ)
    {Y Z : AlgebraicGeometry.Scheme.{u}} (ιA : AlgebraicGeometry.Proj 𝒜 ⟶ Y)
    (ιB : AlgebraicGeometry.Proj ℬ ⟶ Y) (w : AlgebraicGeometry.Proj.map f hf ≫ ιA = ιB)
    (g : Y ⟶ Z) (w' : AlgebraicGeometry.Proj.map f hf ≫ (ιA ≫ g) = ιB ≫ g) :
    twistPushTransition f hf n (ιA ≫ g) (ιB ≫ g) w' =
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp ιA g).inv.app
          (AlgebraicGeometry.Proj.twist 𝒜 n) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward g).map (twistPushTransition f hf n ιA ιB w) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardComp ιB g).hom.app
          (AlgebraicGeometry.Proj.twist ℬ n) := by
  subst w
  refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ fun U => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => ?_)
  refine Subtype.ext (funext fun y => ?_)
  have hy : ProjectiveSpectrum.comap f hf y.1 ∈
      ((ιA ≫ g) ⁻¹ᵁ U : (AlgebraicGeometry.Proj 𝒜).Opens) := y.2
  refine (twistPushTransition_app_apply f hf n (ιA ≫ g) _ w' U s y hy).trans ?_
  exact (twistPushTransition_app_apply f hf n ιA _ rfl (g ⁻¹ᵁ U) s y hy).symm

/-- `T(f)` depends only on the graded ring homomorphism `f`. -/
theorem twistPushTransition_congr {f g : 𝒜 →+*ᵍ ℬ} (e : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) (n : ℤ)
    {Y : AlgebraicGeometry.Scheme.{u}} (ιA : AlgebraicGeometry.Proj 𝒜 ⟶ Y)
    (ιB : AlgebraicGeometry.Proj ℬ ⟶ Y) (wf : AlgebraicGeometry.Proj.map f hf ≫ ιA = ιB)
    (wg : AlgebraicGeometry.Proj.map g hg ≫ ιA = ιB) :
    twistPushTransition f hf n ιA ιB wf = twistPushTransition g hg n ιA ιB wg := by
  subst e; rfl

end AlgebraicGeometry.Proj

/-- Bridge lemma (four morphisms): `f ≫ g = f₂ ≫ g₂` in one spelling gives `f' ≫ g' = f₂' ≫ g₂'` in
another; objects and morphisms are variables here, the concrete spellings are identified by top-level
`rfl` / `HEq.rfl` at the call site (see `RelativeProjTwistComp`). Same content as
`CategoryTheory.comp_eq_comp_of_heq_bridge` in `VeroneseTwistPullback` (which
takes the four objects explicitly); duplicated here with implicit objects to avoid importing the
Veronese module — the two should eventually live together next to `comp_eq_of_heq_bridge`. -/
theorem CategoryTheory.comp₂_eq_comp₂_of_heq_bridge {C : Type*} [Category C]
    {A B D B₂ A' B' D' B₂' : C} {f : A ⟶ B} {g : B ⟶ D} {f₂ : A ⟶ B₂} {g₂ : B₂ ⟶ D}
    (h : f ≫ g = f₂ ≫ g₂) (f' : A' ⟶ B') (g' : B' ⟶ D') (f₂' : A' ⟶ B₂') (g₂' : B₂' ⟶ D')
    (hA : A' = A) (hB : B' = B) (hD : D' = D) (hB₂ : B₂' = B₂)
    (hf : HEq f' f) (hg : HEq g' g) (hf₂ : HEq f₂' f₂) (hg₂ : HEq g₂' g₂) : f' ≫ g' = f₂' ≫ g₂' := by
  subst hA; subst hB; subst hD; subst hB₂
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hf₂
  obtain rfl := eq_of_heq hg₂
  exact h


end
