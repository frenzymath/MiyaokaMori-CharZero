import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSectionInPunctured
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackNotZeroAt

/-! # Points of the zero section give vanishing sections

Pointwise zero-section criterion, forward direction: if an `X`-morphism `m : S → Tot(V)` (over `f : S → X`)
sends a point `p` into the image of the zero section, then the section of `f^*V` corresponding to `m`
(`totalSpaceHomEquiv`) is zero at `p` (`IsZeroAt`). Contrapositive: a nowhere-zero section gives a morphism
into the punctured total space `Tot(V)^×`.

References: Hartshorne II Ex. 5.18 (total space of a vector bundle); in the paper, "a nowhere-zero section
of `L` is a morphism to `Tot(L)` avoiding the zero section".
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `Over.homMk` form: `ml : S → Tot(V)` with `ml ≫ p = f`; if `ml(p) = σ₀(c)` for some `c`, then the section
`totalSpaceHomEquiv V (Over.mk f) (Over.homMk ml hml) ∈ Γ(S, f^*V)` is zero at `p`.

Proof: after `subst`, `totalSpaceHomEquiv_naturality` (with the identity of `Tot(V)`) writes the section as
`pullbackComp.hom (ml^* ξ)`, `ξ` the tautological section of `p^*V`. `ξ` vanishes along the zero section
(`sectionPullbackAlong_zeroSection_tautological`: `σ₀^* ξ = 0`), hence `IsZeroAt ξ (σ₀ c)`
(`isZeroAt_of_sectionPullbackAlong_eq_zero`); pulling back along `ml` preserves `IsZeroAt`
(`isZeroAt_sectionPullbackAlong_of_isZeroAt`), and so does the module map `pullbackComp.hom` (`isZeroAt_map`). -/
theorem AlgebraicGeometry.Scheme.isZeroAt_totalSpaceHomEquiv_homMk_of_mem_range_zeroSection
    {X S : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (f : S ⟶ X) (ml : S ⟶ (AlgebraicGeometry.Scheme.totalSpace V).left)
    (hml : ml ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom = f) (p : S)
    (h : ml.base p ∈ Set.range (AlgebraicGeometry.Scheme.zeroSection V).base) :
    IsZeroAt (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk f)
      (CategoryTheory.Over.homMk ml hml)) p := by
  subst hml
  obtain ⟨c, hc⟩ := h
  have hn := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality V
    (AlgebraicGeometry.Scheme.totalSpace V) ml (𝟙 _)
  rw [Category.comp_id] at hn
  rw [hn]
  apply isZeroAt_map
  apply isZeroAt_sectionPullbackAlong_of_isZeroAt
  rw [← hc]
  exact isZeroAt_of_sectionPullbackAlong_eq_zero (AlgebraicGeometry.Scheme.zeroSection V) _ _ c
    (AlgebraicGeometry.Scheme.sectionPullbackAlong_zeroSection_tautological V)

/-- **Pointwise zero-section criterion (forward direction).** For `m : Over.mk f ⟶ Tot(V)` over `X` and a point
`p` with `m.left p ∈ σ₀(X)`, the corresponding section `totalSpaceHomEquiv V (Over.mk f) m` is zero at `p`.
(`m = Over.homMk m.left (Over.w m)` by `Over.OverMorphism.ext`, then the `homMk` version.) -/
theorem AlgebraicGeometry.Scheme.isZeroAt_totalSpaceHomEquiv_of_mem_range_zeroSection
    {X S : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (f : S ⟶ X) (m : CategoryTheory.Over.mk f ⟶ AlgebraicGeometry.Scheme.totalSpace V) (p : S)
    (h : m.left.base p ∈ Set.range (AlgebraicGeometry.Scheme.zeroSection V).base) :
    IsZeroAt (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk f) m) p := by
  have hm : m = CategoryTheory.Over.homMk m.left (CategoryTheory.Over.w m) :=
    CategoryTheory.Over.OverMorphism.ext rfl
  rw [hm]
  exact AlgebraicGeometry.Scheme.isZeroAt_totalSpaceHomEquiv_homMk_of_mem_range_zeroSection V f m.left
    (CategoryTheory.Over.w m) p h

end
