import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceCoordinate
import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistIsLineBundle
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOfNowhereZeroTuple
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01mw
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveChartRingHomExt
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechPullbackMap
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveCoordinateRatio
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModuleChartPullback
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.WeightedProjCoordinateFormula
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleGenericFiber
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulePullbackStalkTensor

/-! # The universal property of projective space (Stacks 01NE)

Stacks 01NE (the universal property of projective space): morphisms to `P^N` correspond to pairs
(an invertible sheaf `L`, `N+1` global sections generating `L`) up to isomorphism. In particular, if
two pairs `(L, s_i)` and `(L', s'_i)` are related by an isomorphism `L ≅ L'` sending `s_i` to `s'_i`,
they define the same morphism, and a morphism `φ` corresponds to `(φ^*O(1), φ^*x_i)`.

This is the functor-of-points form of "a nonzero vector determines a point of `X`" in §2 of the paper.

Route (following the uniqueness argument of Stacks 01NA, reading off the morphism on the standard
charts; the lemmas live in the namespace `Stacks01ne`):
1. `chart_le_preimage_basicOpen`: `V_ℓ = {P_ℓ ≠ 0} ⊆ φ⁻¹(D_+(x_ℓ))` (Stacks 01MW, and pullbacks /
   module homomorphisms preserve `IsZeroAt`);
2. lift `V_ℓ.ι ≫ φ` through the open immersion to `ψ : V_ℓ → D_+(x_ℓ)` (`IsOpenImmersion.lift`);
   `chartMap_ι` gives `projectivizationChartMorphism = chartMap ≫ ι`;
3. after `D_+(x_ℓ) ≅ Spec A⁰_{x_ℓ}`, the Γ–Spec adjunction (`hom_to_Spec_ext`) reduces the claim to an
   equality of ring homomorphisms `A⁰_{x_ℓ} → Γ(V_ℓ, O)`; by `chartRingHom_ext` it suffices to compare
   them on `k` (`appTop_fromZero_of_comp_over`, since `φ` is a `k`-morphism) and on the ratios `x_i/x_ℓ`
   (`appTop_ratioSection_eq_chartEval`: `x_i = (x_i/x_ℓ)·x_ℓ` holds in `O(1)`; pulling back and applying
   `θ` gives `P_i = φ^♯(x_i/x_ℓ)·P_ℓ`, and `projectivizationRatio_unique` gives
   `φ^♯(x_i/x_ℓ) = P_i/P_ℓ`);
4. uniqueness of morphisms on a cover (`Cover.hom_ext`) glues the charts.
The 01MW step is `AlgebraicGeometry.Proj.not_isZeroAt_twistSection_iff_of_iSup_eq_top`, with the
covering hypothesis `projectiveSpace_iSup_basicOpen_X`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks01ne

/-- Γ–Spec: a morphism to an affine scheme is determined by its ring homomorphism on global sections
(`toSpecΓ_naturality` + `SpecMap_ΓSpecIso_hom`). -/
theorem hom_to_Spec_eq {T : AlgebraicGeometry.Scheme.{u}} {R : CommRingCat.{u}}
    (χ : T ⟶ AlgebraicGeometry.Spec R) :
    χ = T.toSpecΓ ≫
      AlgebraicGeometry.Spec.map ((AlgebraicGeometry.Scheme.ΓSpecIso R).inv ≫ χ.appTop) := by
  have h1 : χ ≫ AlgebraicGeometry.Spec.map (AlgebraicGeometry.Scheme.ΓSpecIso R).hom =
      T.toSpecΓ ≫ AlgebraicGeometry.Spec.map χ.appTop := by
    rw [AlgebraicGeometry.SpecMap_ΓSpecIso_hom]
    exact AlgebraicGeometry.Scheme.toSpecΓ_naturality χ
  calc χ = χ ≫ (AlgebraicGeometry.Spec.map (AlgebraicGeometry.Scheme.ΓSpecIso R).hom ≫
        AlgebraicGeometry.Spec.map (AlgebraicGeometry.Scheme.ΓSpecIso R).inv) := by
        rw [← AlgebraicGeometry.Spec.map_comp, Iso.inv_hom_id, AlgebraicGeometry.Spec.map_id,
          Category.comp_id]
    _ = _ := by
        rw [← Category.assoc, h1, Category.assoc, ← AlgebraicGeometry.Spec.map_comp]

theorem hom_to_Spec_ext {T : AlgebraicGeometry.Scheme.{u}} {R : CommRingCat.{u}}
    (χ₁ χ₂ : T ⟶ AlgebraicGeometry.Spec R) (h : χ₁.appTop = χ₂.appTop) : χ₁ = χ₂ := by
  rw [hom_to_Spec_eq χ₁, hom_to_Spec_eq χ₂, h]

/-- A homomorphism of sheaves of modules preserves "vanishing at `x`" (a copy of
`SeedSectionInPunctured.isZeroAt_map`, which cannot be imported here because that module imports this
one through `HomogeneousCoordinateSections`). -/
theorem isZeroAt_map_hom {X : AlgebraicGeometry.Scheme.{u}} {M M' : X.Modules} (φ : M ⟶ M')
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) (x : X) (h : IsZeroAt s x) :
    IsZeroAt ((φ.val.app (Opposite.op ⊤)).hom s) x := by
  have hgerm : (M'.presheaf.germ ⊤ x trivial).hom ((φ.val.app (Opposite.op ⊤)).hom s) =
      AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x φ ((M.presheaf.germ ⊤ x trivial).hom s) :=
    (AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ X x φ ⊤ trivial s).symm
  have h' : (M.presheaf.germ ⊤ x trivial).hom s ∈
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) (M.presheaf.stalk x)) := h
  have hle : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) (M.presheaf.stalk x)) ≤
      Submodule.comap (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x φ)
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x) (M'.presheaf.stalk x))) := by
    refine Submodule.smul_le.2 (fun r hr n _ => ?_)
    rw [Submodule.mem_comap, LinearMap.map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  have hfin : (M'.presheaf.germ ⊤ x trivial).hom ((φ.val.app (Opposite.op ⊤)).hom s) ∈
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) (M'.presheaf.stalk x)) := by
    rw [hgerm]
    exact hle h'
  exact hfin

/-- If a section vanishes at `g(x)`, its pullback vanishes at `x` (a copy of
`SeedSectionInPunctured.isZeroAt_sectionPullbackAlong_of_isZeroAt`, for the same reason). -/
theorem isZeroAt_pullback {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) (s : (M.val.obj (Opposite.op ⊤) : Type u)) (x : X)
    (h : IsZeroAt s (g.base x)) : IsZeroAt (sectionPullbackAlong g s) x := by
  have hgerm :
      (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).presheaf.germ ⊤ x trivial).hom
          (sectionPullbackAlong g s) =
        AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit g M x
          ((M.presheaf.germ ⊤ (g.base x) trivial).hom s) :=
    (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom_germ g M x ⊤ trivial s).symm
  have h' : (M.presheaf.germ ⊤ (g.base x) trivial).hom s ∈
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (g.base x))) •
        (⊤ : Submodule (Y.presheaf.stalk (g.base x)) (M.presheaf.stalk (g.base x))) := h
  have hle : (IsLocalRing.maximalIdeal (Y.presheaf.stalk (g.base x))) •
        (⊤ : Submodule (Y.presheaf.stalk (g.base x)) (M.presheaf.stalk (g.base x))) ≤
      Submodule.comap (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit g M x)
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x) (AlgebraicGeometry.Scheme.Modules.modulePullbackStalk g M x))) := by
    refine Submodule.smul_le.2 (fun r hr n _ => ?_)
    rw [Submodule.mem_comap, LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem_smul (map_nonunit _ r hr) Submodule.mem_top
  have hfin :
      (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).presheaf.germ ⊤ x trivial).hom
          (sectionPullbackAlong g s) ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x) (AlgebraicGeometry.Scheme.Modules.modulePullbackStalk g M x)) := by
    rw [hgerm]
    exact hle h'
  exact hfin

/-- Step 2: the chart `V_ℓ = {P_ℓ ≠ 0}` lies in `φ⁻¹(D_+(x_ℓ))`. If `φ(t) ∉ D_+(x_ℓ)`, then `x_ℓ`
vanishes at `φ(t)` (Stacks 01MW), so `φ^*x_ℓ` vanishes at `t`, and through `θ` so does `P_ℓ`,
contradicting `t ∈ V_ℓ`. -/
theorem chart_le_preimage_basicOpen {k : Type u} [Field k] {T : AlgebraicGeometry.Scheme.{u}}
    {N : ℕ} (φ : T ⟶ ProjectiveSpace N k)
    (M : T.Modules) [M.IsLineBundle]
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (θ : (AlgebraicGeometry.Scheme.Modules.pullback φ).obj (projectiveSpaceTwist k N 1) ≅ M)
    (hθ : ∀ i, (θ.hom.app ⊤).hom
        (sectionPullbackAlong φ (projectiveSpaceCoordinate k N i)) = P i) (ℓ : Fin (N + 1)) :
    projectivizationChart P ℓ ≤
      φ ⁻¹ᵁ (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N)
        (MvPolynomial.X ℓ) : (ProjectiveSpace N k).Opens) := by
  intro t ht
  by_contra hD
  have h1 : IsZeroAt (projectiveSpaceCoordinate k N ℓ) (φ.base t) := by
    by_contra hz
    exact hD ((AlgebraicGeometry.Proj.not_isZeroAt_twistSection_iff_of_iSup_eq_top
      (AlgebraicGeometry.Proj.projectiveGrading k N) MvPolynomial.X
      (fun j => (MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X k j))
      (projectiveSpace_iSup_basicOpen_X k N) (MvPolynomial.X ℓ)
      ((MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X k ℓ))
      (φ.base t)).1 hz)
  have h2 := isZeroAt_pullback φ (projectiveSpaceTwist k N 1) (projectiveSpaceCoordinate k N ℓ) t h1
  have h3 := isZeroAt_map_hom θ.hom _ t h2
  have h4 : IsZeroAt (P ℓ) t := by
    rw [← hθ ℓ]
    exact h3
  exact ht h4

/-- Bookkeeping of sections on an open subscheme: if `ψ ≫ D.ι = g`, then `ψ^♯(u|_D)` is the `appLE`
of `g` from `D` to `⊤`. -/
theorem appTop_topIso_inv_eq_appLE {T Y : AlgebraicGeometry.Scheme.{u}} (D : Y.Opens)
    (ψ : T ⟶ D.toScheme) (g : T ⟶ Y) (hψ : ψ ≫ D.ι = g) (u : Γ(Y, D)) (e : ⊤ ≤ g ⁻¹ᵁ D) :
    ψ.appTop (D.topIso.inv u) = g.appLE D ⊤ e u := by
  subst hψ
  have h := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE ψ D.ι D ⊤ ⊤
    D.ι_preimage_self.ge (le_rfl : (⊤ : T.Opens) ≤ ψ ⁻¹ᵁ ⊤)
  rw [← h, CommRingCat.comp_apply]
  have h1 : D.ι.appLE D ⊤ D.ι_preimage_self.ge u = D.topIso.inv u := by
    rw [AlgebraicGeometry.Scheme.Opens.ι_appLE, AlgebraicGeometry.Scheme.Opens.topIso_inv]
    rfl
  have h2 : ψ.appLE ⊤ ⊤ (le_rfl : (⊤ : T.Opens) ≤ ψ ⁻¹ᵁ ⊤) = ψ.appTop := by
    rw [AlgebraicGeometry.Scheme.Hom.appLE]
    change ψ.app ⊤ ≫ T.presheaf.map (𝟙 _) = ψ.app ⊤
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [h1, h2]

/-- The `appLE` to `⊤` along the open immersion `W.ι` followed by `φ` is, through `topIso`, the
restriction of `φ^♯(u)` to `W`. -/
theorem topIso_hom_comp_ι_appLE {T Y : AlgebraicGeometry.Scheme.{u}} (W : T.Opens)
    (φ : T ⟶ Y) (D : Y.Opens) (hW : W ≤ φ ⁻¹ᵁ D) (e : ⊤ ≤ (W.ι ≫ φ) ⁻¹ᵁ D) (u : Γ(Y, D)) :
    W.topIso.hom ((W.ι ≫ φ).appLE D ⊤ e u) = T.presheaf.map (homOfLE hW).op (φ.app D u) := by
  rw [AlgebraicGeometry.Scheme.Hom.comp_appLE, CommRingCat.comp_apply,
    AlgebraicGeometry.Scheme.Opens.ι_appLE, AlgebraicGeometry.Scheme.Opens.topIso_hom,
    ← CommRingCat.comp_apply, ← CategoryTheory.Functor.map_comp]
  rfl


/-- The standard open `D_+(x_ℓ)` as an open of `ProjectiveSpace N k` (a reducible abbreviation, only to
shorten statements). -/
abbrev coordBasicOpen (k : Type u) [Field k] (N : ℕ) (ℓ : Fin (N + 1)) : (ProjectiveSpace N k).Opens :=
  AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X ℓ)

/-- `D_+(x_ℓ) ≅ Spec (k[x]_{(x_ℓ)})₀` (an abbreviation of Mathlib's `Proj.basicOpenIsoSpec`). -/
abbrev coordBasicOpenIsoSpec (k : Type u) [Field k] (N : ℕ) (ℓ : Fin (N + 1)) :
    (coordBasicOpen k N ℓ).toScheme ≅
      AlgebraicGeometry.Spec (CommRingCat.of
        (HomogeneousLocalization.Away (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X ℓ))) :=
  AlgebraicGeometry.Proj.basicOpenIsoSpec (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X ℓ)
    (MvPolynomial.isHomogeneous_X k ℓ) Nat.one_pos

/-- The core of step 1 (an identity in `O(1)`): on `D_+(x_ℓ)` we have `x_i = (x_i/x_ℓ)·x_ℓ`, where
`x_i/x_ℓ` is the `ratioSection` (viewed through `topIso` as an element of `Γ(P^N, D_+(x_ℓ))`). On
`D_+(x_ℓ)` the section `x_ℓ` is a frame of `O(1)` (`isFrame_homogeneousSection`) with coordinate
`divideSection` (`coord_homogeneousSection`); `divide_coordinate_eq_ratioElement` and
`awayToSection_ratioElement_eq_ratioSection` identify it with the ratio. -/
theorem coordinate_res_eq_ratioSection_smul (k : Type u) [Field k] (N : ℕ) (i ℓ : Fin (N + 1)) :
    (projectiveSpaceTwist k N 1).res (le_top : coordBasicOpen k N ℓ ≤ ⊤)
        (projectiveSpaceCoordinate k N i) =
      (coordBasicOpen k N ℓ).topIso.hom (ProjectiveSpaceOverChart.ratioSection N i ℓ) •
      (projectiveSpaceTwist k N 1).res le_top (projectiveSpaceCoordinate k N ℓ) := by
  have hℓ : (MvPolynomial.X ℓ : MvPolynomial (Fin (N + 1)) k) ∈ AlgebraicGeometry.Proj.projectiveGrading k N 1 :=
    (MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X k ℓ)
  have hi : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ AlgebraicGeometry.Proj.projectiveGrading k N 1 :=
    (MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X k i)
  have hfr := MiyaokaMori.WeightedJets.ProjTwisting.isFrame_homogeneousSection
    (AlgebraicGeometry.Proj.projectiveGrading k N) 1 (MvPolynomial.X ℓ) hℓ
    (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X ℓ))
    (fun x => (ProjectiveSpectrum.mem_basicOpen _ _ _).1 x.2)
  have h1 := hfr.coord_smul_frame le_rfl
    (MiyaokaMori.WeightedJets.ProjTwisting.homogeneousSection (AlgebraicGeometry.Proj.projectiveGrading k N) 1
      (MvPolynomial.X i) hi
      (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X ℓ)))
  rw [AlgebraicGeometry.Scheme.Modules.res_self,
    MiyaokaMori.WeightedJets.ProjTwisting.coord_homogeneousSection (AlgebraicGeometry.Proj.projectiveGrading k N) 1
      (MvPolynomial.X ℓ) hℓ _ (fun x => (ProjectiveSpectrum.mem_basicOpen _ _ _).1 x.2),
    ProjectiveSpaceOverChart.divide_coordinate_eq_ratioElement] at h1
  have h2 : AlgebraicGeometry.Proj.awayToSection (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X ℓ)
      (ProjectiveSpaceOverChart.ratioElement N i ℓ) =
      (coordBasicOpen k N ℓ).topIso.hom (ProjectiveSpaceOverChart.ratioSection N i ℓ) := by
    have h3 := ProjectiveSpaceOverChart.awayToSection_ratioElement_eq_ratioSection
      (R := k) N ℓ i
    rw [AlgebraicGeometry.Scheme.Opens.ι_appIso] at h3
    rw [← h3]
    change _ = (coordBasicOpen k N ℓ).topIso.hom ((coordBasicOpen k N ℓ).topIso.inv _)
    rw [Iso.inv_hom_id_apply]
  rw [← h2]
  exact h1.symm

/-- Ratios of pulled-back sections: if `s' = u • s` on an open `D` of `Y` (both restricted to `D`), then
on `W ⊆ φ⁻¹D` we have `(φ^*s')| = φ^♯(u)| • (φ^*s)|`. Uses the semilinearity of the adjunction unit
(`pullbackUnitHom_smul`) and its compatibility with restriction. -/
theorem pullback_res_eq_smul_of_res_eq_smul {T Y : AlgebraicGeometry.Scheme.{u}} (φ : T ⟶ Y)
    (M : Y.Modules) (D : Y.Opens) (u : Γ(Y, D)) (s s' : Γ(M, ⊤))
    (h : M.res (le_top : D ≤ ⊤) s' = u • M.res le_top s)
    (W : T.Opens) (hW : W ≤ φ ⁻¹ᵁ D) :
    ((AlgebraicGeometry.Scheme.Modules.pullback φ).obj M).res (le_top : W ≤ ⊤)
        (sectionPullbackAlong φ s') =
      T.presheaf.map (homOfLE hW).op (φ.app D u) •
        ((AlgebraicGeometry.Scheme.Modules.pullback φ).obj M).res le_top
          (sectionPullbackAlong φ s) := by
  have key : ∀ x : Γ(M, ⊤),
      ((AlgebraicGeometry.Scheme.Modules.pullback φ).obj M).res (le_top : W ≤ ⊤)
        (sectionPullbackAlong φ x) =
      ((AlgebraicGeometry.Scheme.Modules.pullback φ).obj M).res hW
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom φ M D (M.res le_top x)) := by
    intro x
    rw [AlgebraicGeometry.Scheme.Modules.pullbackUnitHom_restrict]
    exact (AlgebraicGeometry.Scheme.Modules.res_res _ hW _ _).symm
  rw [key, key, h, AlgebraicGeometry.Scheme.Modules.pullbackUnitHom_smul,
    AlgebraicGeometry.Scheme.Modules.res_smul]

/-- The key computation of step 3: if `ψ : V_ℓ → D_+(x_ℓ)` is the lift of `V_ℓ.ι ≫ φ`, then
`ψ^♯(x_i/x_ℓ) = P_i/P_ℓ` (the latter is `projectivizationChartEval P ℓ (X i)`). Proof: through `topIso`,
`ψ^♯(x_i/x_ℓ)` equals `φ^♯(x_i/x_ℓ)|_{V_ℓ}` (`appTop_topIso_inv_eq_appLE`, `topIso_hom_comp_ι_appLE`);
pulling back `x_i = (x_i/x_ℓ)·x_ℓ` gives `φ^*x_i| = φ^♯(x_i/x_ℓ)| • φ^*x_ℓ|`, and through the module
isomorphism `θ`, `P_i| = φ^♯(x_i/x_ℓ)| • P_ℓ|`; conclude by uniqueness of the ratio
(`projectivizationRatio_unique`). -/
theorem appTop_ratioSection_eq_chartEval {k : Type u} [Field k]
    {T : AlgebraicGeometry.Scheme.{u}} [T.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    {N : ℕ} (φ : T ⟶ ProjectiveSpace N k)
    (M : T.Modules) [M.IsLineBundle]
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (θ : (AlgebraicGeometry.Scheme.Modules.pullback φ).obj (projectiveSpaceTwist k N 1) ≅ M)
    (hθ : ∀ i, (θ.hom.app ⊤).hom
        (sectionPullbackAlong φ (projectiveSpaceCoordinate k N i)) = P i) (ℓ i : Fin (N + 1))
    (ψ : (projectivizationChart P ℓ).toScheme ⟶ (coordBasicOpen k N ℓ).toScheme)
    (hψ : ψ ≫ (coordBasicOpen k N ℓ).ι = (projectivizationChart P ℓ).ι ≫ φ) :
    ψ.appTop (ProjectiveSpaceOverChart.ratioSection N i ℓ) =
      projectivizationChartEval (k := k) P ℓ (MvPolynomial.X i) := by
  have hle : projectivizationChart P ℓ ≤ φ ⁻¹ᵁ coordBasicOpen k N ℓ :=
    chart_le_preimage_basicOpen φ M P θ hθ ℓ
  have e : ⊤ ≤ ((projectivizationChart P ℓ).ι ≫ φ) ⁻¹ᵁ coordBasicOpen k N ℓ :=
    fun x _ => hle x.2
  have hclaim1 : (projectivizationChart P ℓ).topIso.hom
      (ψ.appTop (ProjectiveSpaceOverChart.ratioSection N i ℓ)) =
      T.presheaf.map (homOfLE hle).op (φ.app (coordBasicOpen k N ℓ)
        ((coordBasicOpen k N ℓ).topIso.hom
          (ProjectiveSpaceOverChart.ratioSection N i ℓ))) := by
    have h1 : ψ.appTop (ProjectiveSpaceOverChart.ratioSection N i ℓ) =
        ((projectivizationChart P ℓ).ι ≫ φ).appLE (coordBasicOpen k N ℓ) ⊤ e
          ((coordBasicOpen k N ℓ).topIso.hom
            (ProjectiveSpaceOverChart.ratioSection N i ℓ)) := by
      rw [← appTop_topIso_inv_eq_appLE (coordBasicOpen k N ℓ) ψ _ hψ _ e]
      congr 1
    rw [h1]
    exact topIso_hom_comp_ι_appLE (projectivizationChart P ℓ) φ (coordBasicOpen k N ℓ) hle e _
  have hnat : ∀ x : Γ((AlgebraicGeometry.Scheme.Modules.pullback φ).obj
      (projectiveSpaceTwist k N 1), ⊤),
      M.res (le_top : projectivizationChart P ℓ ≤ ⊤) (θ.hom.app ⊤ x) =
        θ.hom.app (projectivizationChart P ℓ)
          (((AlgebraicGeometry.Scheme.Modules.pullback φ).obj
            (projectiveSpaceTwist k N 1)).res le_top x) :=
    fun x => (AlgebraicGeometry.Scheme.Modules.app_map θ.hom le_top x).symm
  have hi' : M.res (le_top : projectivizationChart P ℓ ≤ ⊤) (P i) =
      θ.hom.app (projectivizationChart P ℓ)
        (((AlgebraicGeometry.Scheme.Modules.pullback φ).obj (projectiveSpaceTwist k N 1)).res
          le_top (sectionPullbackAlong φ (projectiveSpaceCoordinate k N i))) := by
    rw [← hθ i]
    exact hnat _
  have hℓ' : M.res (le_top : projectivizationChart P ℓ ≤ ⊤) (P ℓ) =
      θ.hom.app (projectivizationChart P ℓ)
        (((AlgebraicGeometry.Scheme.Modules.pullback φ).obj (projectiveSpaceTwist k N 1)).res
          le_top (sectionPullbackAlong φ (projectiveSpaceCoordinate k N ℓ))) := by
    rw [← hθ ℓ]
    exact hnat _
  have hclaim2 : M.res (le_top : projectivizationChart P ℓ ≤ ⊤) (P i) =
      T.presheaf.map (homOfLE hle).op (φ.app (coordBasicOpen k N ℓ)
        ((coordBasicOpen k N ℓ).topIso.hom
          (ProjectiveSpaceOverChart.ratioSection N i ℓ))) •
        M.res le_top (P ℓ) := by
    rw [hi', hℓ', ← AlgebraicGeometry.Scheme.Modules.Hom.app_smul]
    exact congrArg _ (pullback_res_eq_smul_of_res_eq_smul φ (projectiveSpaceTwist k N 1)
      (coordBasicOpen k N ℓ) _ (projectiveSpaceCoordinate k N ℓ) (projectiveSpaceCoordinate k N i)
      (coordinate_res_eq_ratioSection_smul k N i ℓ) (projectivizationChart P ℓ) hle)
  have hratio : projectivizationRatio P ℓ i =
      T.presheaf.map (homOfLE hle).op (φ.app (coordBasicOpen k N ℓ)
        ((coordBasicOpen k N ℓ).topIso.hom
          (ProjectiveSpaceOverChart.ratioSection N i ℓ))) :=
    projectivizationRatio_unique P ℓ i _ (by
      rw [AlgebraicGeometry.Scheme.Modules.res_self]
      exact hclaim2.symm)
  rw [projectivizationChartEval, projectivizationChartEvalOver, MvPolynomial.eval₂Hom_X', hratio, ← hclaim1]
  change _ = (projectivizationChart P ℓ).topIso.inv ((projectivizationChart P ℓ).topIso.hom _)
  rw [Iso.hom_inv_id_apply]

/-- The `k`-part: if `χ' : V_ℓ → D_+(x_ℓ)` is compatible with the structure morphisms, then the value
of `χ'` composed with `D_+(x_ℓ) ≅ Spec A⁰` on a constant `c ∈ k` (through `𝒜₀ → A⁰_{x_ℓ}`) is the value
of `V_ℓ → Spec k` on `c`. Uses `awayι_toSpecZero` and `ΓSpecIso_inv_naturality`. -/
theorem appTop_fromZero_of_comp_over {k : Type u} [Field k]
    {T : AlgebraicGeometry.Scheme.{u}} [T.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    {N : ℕ} (W : T.Opens) (ℓ : Fin (N + 1))
    (χ' : W.toScheme ⟶ (coordBasicOpen k N ℓ).toScheme)
    (h : χ' ≫ (coordBasicOpen k N ℓ).ι ≫
        (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      W.ι ≫ (T ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) (c : k) :
    (χ' ≫ (coordBasicOpenIsoSpec k N ℓ).hom).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of
          (HomogeneousLocalization.Away (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X ℓ)))).inv
          (HomogeneousLocalization.fromZeroRingHom (AlgebraicGeometry.Proj.projectiveGrading k N) _
            (algebraMap k ((AlgebraicGeometry.Proj.projectiveGrading k N) 0) c))) =
      (W.ι ≫ (T ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
  let ρ₀ : k →+* HomogeneousLocalization.Away (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X ℓ) :=
    (HomogeneousLocalization.fromZeroRingHom (AlgebraicGeometry.Proj.projectiveGrading k N)
      (Submonoid.powers (MvPolynomial.X ℓ))).comp (algebraMap k ((AlgebraicGeometry.Proj.projectiveGrading k N) 0))
  have hS : (coordBasicOpenIsoSpec k N ℓ).hom ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom ρ₀) =
      (coordBasicOpen k N ℓ).ι ≫ (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    change (coordBasicOpenIsoSpec k N ℓ).hom ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom ρ₀) =
      (coordBasicOpen k N ℓ).ι ≫ (AlgebraicGeometry.Proj.toSpecZero (AlgebraicGeometry.Proj.projectiveGrading k N) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k ((AlgebraicGeometry.Proj.projectiveGrading k N) 0))))
    have h1 : (coordBasicOpen k N ℓ).ι = (coordBasicOpenIsoSpec k N ℓ).hom ≫
        AlgebraicGeometry.Proj.awayι (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X ℓ)
          (MvPolynomial.isHomogeneous_X k ℓ) Nat.one_pos := by
      rw [← AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
    rw [h1, Category.assoc, AlgebraicGeometry.Proj.awayι_toSpecZero_assoc,
      ← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h2 : (χ' ≫ (coordBasicOpenIsoSpec k N ℓ).hom) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom ρ₀) =
      W.ι ≫ (T ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    rw [Category.assoc, hS, h]
  have h4 := AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ₀)
  have h5 : (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of
      (HomogeneousLocalization.Away (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X ℓ)))).inv (ρ₀ c) =
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ρ₀)).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
    exact congrArg (fun f => f c) h4
  change (χ' ≫ (coordBasicOpenIsoSpec k N ℓ).hom).appTop
    ((AlgebraicGeometry.Scheme.ΓSpecIso _).inv (ρ₀ c)) = _
  rw [h5, ← CommRingCat.comp_apply, ← AlgebraicGeometry.Scheme.Hom.comp_appTop, h2]

/-- The identity on each chart: `V_ℓ.ι ≫ φ = projectivizationChartMorphism P ℓ`.
(B) `V_ℓ.ι ≫ φ` lands in `D_+(x_ℓ)` and lifts to `ψ : V_ℓ → D_+(x_ℓ)`; (C) the chart morphism is
`chartMap ≫ ι` (`chartMap_ι`); (D) after `D_+(x_ℓ) ≅ Spec A⁰_{x_ℓ}` both are morphisms to an affine
scheme, so Γ–Spec reduces the claim to an equality of ring homomorphisms `A⁰_{x_ℓ} → Γ(V_ℓ, O)`; by
`chartRingHom_ext`, agreement on `k` comes from `φ` being a `k`-morphism, and agreement on the ratios
`x_i/x_ℓ` is `appTop_ratioSection_eq_chartEval` with `chartMap_appTop_ratio`. -/
theorem restrict_eq_chartMorphism {k : Type u} [Field k]
    {T : AlgebraicGeometry.Scheme.{u}} [T.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    {N : ℕ} (φ : T ⟶ ProjectiveSpace N k) [φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : T.Modules) [M.IsLineBundle]
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (hP : ∀ t : T, ∃ ℓ, ¬ IsZeroAt (P ℓ) t)
    (θ : (AlgebraicGeometry.Scheme.Modules.pullback φ).obj (projectiveSpaceTwist k N 1) ≅ M)
    (hθ : ∀ i, (θ.hom.app ⊤).hom
        (sectionPullbackAlong φ (projectiveSpaceCoordinate k N i)) = P i) (ℓ : Fin (N + 1)) :
    (projectivizationChart P ℓ).ι ≫ φ = projectivizationChartMorphism (k := k) P ℓ := by
  have hunit : IsUnit (projectivizationChartEval (k := k) P ℓ (MvPolynomial.X ℓ)) := by
    rw [projectivizationChartEval_X_self]
    exact isUnit_one
  have hchart : projectivizationChartMorphism (k := k) P ℓ =
      ProjectiveSpaceOverChart.chartMap (projectivizationChart P ℓ).toScheme N
        (projectivizationChartEval (k := k) P ℓ) ℓ hunit ≫ (coordBasicOpen k N ℓ).ι :=
    (ProjectiveSpaceOverChart.chartMap_ι (projectivizationChart P ℓ).toScheme N
      (projectivizationChartEval (k := k) P ℓ)
      (projectivizationChartEval_irrelevant_map_eq_top (k := k) P ℓ) ℓ hunit).symm
  have hle : projectivizationChart P ℓ ≤ φ ⁻¹ᵁ coordBasicOpen k N ℓ :=
    chart_le_preimage_basicOpen φ M P θ hθ ℓ
  have hrange : Set.range ((projectivizationChart P ℓ).ι ≫ φ).base ⊆
      Set.range (coordBasicOpen k N ℓ).ι.base := by
    rintro _ ⟨t, rfl⟩
    exact ⟨⟨_, hle t.2⟩, rfl⟩
  have hψ : AlgebraicGeometry.IsOpenImmersion.lift (coordBasicOpen k N ℓ).ι
      ((projectivizationChart P ℓ).ι ≫ φ) hrange ≫ (coordBasicOpen k N ℓ).ι =
      (projectivizationChart P ℓ).ι ≫ φ := AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  have hover : AlgebraicGeometry.IsOpenImmersion.lift (coordBasicOpen k N ℓ).ι
      ((projectivizationChart P ℓ).ι ≫ φ) hrange ≫ (coordBasicOpen k N ℓ).ι ≫
      (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (projectivizationChart P ℓ).ι ≫ (T ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    rw [← Category.assoc, hψ, Category.assoc, comp_over φ]
  have hover' : ProjectiveSpaceOverChart.chartMap (projectivizationChart P ℓ).toScheme N
      (projectivizationChartEval (k := k) P ℓ) ℓ hunit ≫ (coordBasicOpen k N ℓ).ι ≫
      (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (projectivizationChart P ℓ).ι ≫ (T ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    rw [← Category.assoc, ← hchart, ← projectivizationMorphism_restrict (k := k) M P hP ℓ,
      Category.assoc, projectivizationMorphism_comp_over]
  have hmain : AlgebraicGeometry.IsOpenImmersion.lift (coordBasicOpen k N ℓ).ι
      ((projectivizationChart P ℓ).ι ≫ φ) hrange ≫ (coordBasicOpenIsoSpec k N ℓ).hom =
      ProjectiveSpaceOverChart.chartMap (projectivizationChart P ℓ).toScheme N
        (projectivizationChartEval (k := k) P ℓ) ℓ hunit ≫ (coordBasicOpenIsoSpec k N ℓ).hom := by
    apply hom_to_Spec_ext
    have hρ : ((AlgebraicGeometry.Scheme.ΓSpecIso _).inv ≫
        (AlgebraicGeometry.IsOpenImmersion.lift (coordBasicOpen k N ℓ).ι
          ((projectivizationChart P ℓ).ι ≫ φ) hrange ≫ (coordBasicOpenIsoSpec k N ℓ).hom).appTop).hom =
        ((AlgebraicGeometry.Scheme.ΓSpecIso _).inv ≫
          (ProjectiveSpaceOverChart.chartMap (projectivizationChart P ℓ).toScheme N
            (projectivizationChartEval (k := k) P ℓ) ℓ hunit ≫
              (coordBasicOpenIsoSpec k N ℓ).hom).appTop).hom := by
      refine ProjectiveSpace.chartRingHom_ext ℓ _ _ ?_ ?_
      · intro c
        exact (appTop_fromZero_of_comp_over (projectivizationChart P ℓ) ℓ _ hover c).trans
          (appTop_fromZero_of_comp_over (projectivizationChart P ℓ) ℓ _ hover' c).symm
      · intro i
        change (AlgebraicGeometry.IsOpenImmersion.lift (coordBasicOpen k N ℓ).ι
            ((projectivizationChart P ℓ).ι ≫ φ) hrange).appTop
            (ProjectiveSpaceOverChart.ratioSection N i ℓ) =
          (ProjectiveSpaceOverChart.chartMap (projectivizationChart P ℓ).toScheme N
            (projectivizationChartEval (k := k) P ℓ) ℓ hunit).appTop
            (ProjectiveSpaceOverChart.ratioSection N i ℓ)
        rw [ProjectiveSpaceOverChart.chartMap_appTop_ratio,
          appTop_ratioSection_eq_chartEval φ M P θ hθ ℓ i _ hψ]
        have h := ProjectiveSpaceOverChart.chartEvaluation_ratio_mul N
          (projectivizationChartEval (k := k) P ℓ) ℓ hunit i
        rw [projectivizationChartEval_X_self, mul_one] at h
        exact h.symm
    have hρ' := CommRingCat.hom_ext hρ
    exact (cancel_epi (AlgebraicGeometry.Scheme.ΓSpecIso _).inv).1 hρ'
  have hψeq : AlgebraicGeometry.IsOpenImmersion.lift (coordBasicOpen k N ℓ).ι
      ((projectivizationChart P ℓ).ι ≫ φ) hrange =
      ProjectiveSpaceOverChart.chartMap (projectivizationChart P ℓ).toScheme N
        (projectivizationChartEval (k := k) P ℓ) ℓ hunit :=
    (cancel_mono (coordBasicOpenIsoSpec k N ℓ).hom).1 hmain
  rw [← hψ, hψeq, hchart]

end Stacks01ne

theorem projectiveSpace_hom_ext_of_sections {k : Type u} [Field k] {T : AlgebraicGeometry.Scheme.{u}}
    [T.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (φ : T ⟶ ProjectiveSpace N k) [φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : T.Modules) [M.IsLineBundle]
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (hP : ∀ t : T, ∃ ℓ, ¬ IsZeroAt (P ℓ) t)
    (θ : (AlgebraicGeometry.Scheme.Modules.pullback φ).obj (projectiveSpaceTwist k N 1) ≅ M)
    (hθ : ∀ i, (θ.hom.app ⊤).hom
        (sectionPullbackAlong φ (projectiveSpaceCoordinate k N i)) = P i) :
    φ = projectivizationMorphism M P hP := by
  apply (projectivizationCover (k := k) M P hP).hom_ext
  intro ℓ
  change Fin (N + 1) at ℓ
  change (projectivizationChart P ℓ).ι ≫ φ =
    (projectivizationChart P ℓ).ι ≫ projectivizationMorphism (k := k) M P hP
  rw [projectivizationMorphism_restrict]
  exact Stacks01ne.restrict_eq_chartMorphism φ M P hP θ hθ ℓ

end
