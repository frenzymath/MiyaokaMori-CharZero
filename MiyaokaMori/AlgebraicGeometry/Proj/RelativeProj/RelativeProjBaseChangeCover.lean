import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjBaseChangeLocal
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC

/-! # The locally directed chart cover for the base change of a relative Proj

Statement: the **cover of `Proj_{S'}(g^*𝒜)` by small charts** used to glue the base change
comparison map (Stacks 01O3). Index type `BaseChangeChartIndex g`: pairs `(U, V)` of affine opens
`U ⊆ S`, `V ⊆ S'` (elements of the small affine Zariski sites) with `V ≤ g⁻¹U`, ordered
componentwise. The cover `baseChangeChartCover g 𝒜` has pieces the charts
`Proj((g^*𝒜)(V)) ⟶ Proj_{S'}(g^*𝒜)` (`GradedAffineAlgebra.projChart`, open immersions), and it is
**locally directed** (Mathlib `Scheme.Cover.LocallyDirected`) with transition maps
`projFunctor.map` (= `Proj.map` of the restriction `(g^*𝒜)(V) → (g^*𝒜)(V')`), so morphisms out of
`Proj_{S'}(g^*𝒜)` can be glued from morphisms on the small charts compatible with the transition
maps only (`Scheme.Cover.glueMorphismsOfLocallyDirected`), no abstract fibre products needed.

Two Prop obligations are named theorems: `baseChangeChart_covers` (the small charts cover) and
`baseChangeChart_directed` (the local directedness).

Source: Stacks 01O3 (first paragraph of the proof: it suffices to work over affines `V ⊆ S'`
mapping into affines `U ⊆ S`), Mathlib `AlgebraicGeometry.Cover.Directed`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {S S' : AlgebraicGeometry.Scheme.{u}} (g : S' ⟶ S)

/-- Pairs `(U, V)` of affine opens of `S`, `S'` with `V ≤ g⁻¹U`, ordered componentwise
(the `Preorder` is `Subtype.preorder` of `Prod.instPreorder`; no new instance). -/
abbrev BaseChangeChartIndex : Type u :=
  {p : S.AffineZariskiSite × S'.AffineZariskiSite // p.2.toOpens ≤ g ⁻¹ᵁ p.1.toOpens}

namespace BaseChangeChartIndex

variable {g}

theorem le_U {i j : BaseChangeChartIndex g} (h : i ≤ j) : i.1.1 ≤ j.1.1 := h.1

theorem le_V {i j : BaseChangeChartIndex g} (h : i ≤ j) : i.1.2 ≤ j.1.2 := h.2

end BaseChangeChartIndex

variable (𝒜 : S.GradedQCAlgebra)

/-- **The small charts cover `Proj_{S'}(g^*𝒜)`.**
Proof: `x` lies in some chart `Proj((g^*𝒜)(V))` (`exists_projChart_mem`); `s := π'(x) ∈ V`;
choose an affine open `U ⊆ S` containing `g(s)` (`exists_affine_mem_range_and_range_subset`) and a
basic open `V' = D_V(r) ⊆ V ∩ g⁻¹U` containing `s` (`IsAffineOpen.exists_basicOpen_le`); then
`π'(x) ∈ V'`, and `π'⁻¹V'` is the image of the chart of `V'` (`proj_preimage_eq_opensRange`). -/
theorem baseChangeChart_covers (x : (AlgebraicGeometry.Scheme.relativeProj (𝒜.pullback g)).left) :
    ∃ (i : BaseChangeChartIndex g)
      (y : AlgebraicGeometry.Proj ((𝒜.pullback g).toGradedAffineAlgebra.grading i.1.2)),
      (𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2 y = x := by
  obtain ⟨V, y, rfl⟩ := (𝒜.pullback g).toGradedAffineAlgebra.exists_projChart_mem x
  have hs : (𝒜.pullback g).toGradedAffineAlgebra.relativeProj.hom
      ((𝒜.pullback g).toGradedAffineAlgebra.projChart V y) ∈ V.toOpens := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_apply,
      (𝒜.pullback g).toGradedAffineAlgebra.projChart_hom V,
      AlgebraicGeometry.Scheme.Hom.comp_apply]
    exact ((𝒜.pullback g).toGradedAffineAlgebra.projToOpen V y).2
  obtain ⟨R, f, hf, hmem, -⟩ := AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset
    (X := S) (U := ⊤)
    (x := g ((𝒜.pullback g).toGradedAffineAlgebra.relativeProj.hom
      ((𝒜.pullback g).toGradedAffineAlgebra.projChart V y))) trivial
  let U : S.AffineZariskiSite := ⟨f.opensRange, AlgebraicGeometry.isAffineOpen_opensRange f⟩
  have hsU : (𝒜.pullback g).toGradedAffineAlgebra.relativeProj.hom
      ((𝒜.pullback g).toGradedAffineAlgebra.projChart V y) ∈ g ⁻¹ᵁ U.toOpens := hmem
  obtain ⟨r, hr₁, hr₂⟩ := V.2.exists_basicOpen_le ⟨_, hsU⟩ hs
  have hx : (𝒜.pullback g).toGradedAffineAlgebra.projChart V y ∈
      ((𝒜.pullback g).toGradedAffineAlgebra.projChart (V.basicOpen r)).opensRange := by
    rw [← (𝒜.pullback g).toGradedAffineAlgebra.proj_preimage_eq_opensRange]
    exact hr₂
  obtain ⟨y', hy'⟩ := hx
  exact ⟨⟨(U, V.basicOpen r), hr₁⟩, y', hy'⟩

/-- The cover of `Proj_{S'}(g^*𝒜)` by the small charts `Proj((g^*𝒜)(V))`, `(U, V)` in
`BaseChangeChartIndex g`. An `abbrev` with a structure literal so that `(baseChangeChartCover g 𝒜).I₀`
reduces to `BaseChangeChartIndex g` for instance search (`Preorder.smallCategory`). -/
abbrev baseChangeChartCover : (AlgebraicGeometry.Scheme.relativeProj (𝒜.pullback g)).left.OpenCover where
  I₀ := BaseChangeChartIndex g
  X i := AlgebraicGeometry.Proj ((𝒜.pullback g).toGradedAffineAlgebra.grading i.1.2)
  f i := (𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2
  mem₀ := (AlgebraicGeometry.Scheme.Cover.mkOfCovers (BaseChangeChartIndex g)
    (fun i => AlgebraicGeometry.Proj ((𝒜.pullback g).toGradedAffineAlgebra.grading i.1.2))
    (fun i => (𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2)
    (baseChangeChart_covers g 𝒜)).mem₀

/-- Transition map of the small-chart cover along `i ≤ j`: `Proj.map` of the restriction
`(g^*𝒜)(V_j) → (g^*𝒜)(V_i)`. -/
def baseChangeChartTrans {i j : BaseChangeChartIndex g} (hij : i ⟶ j) :
    (baseChangeChartCover g 𝒜).X i ⟶ (baseChangeChartCover g 𝒜).X j :=
  (𝒜.pullback g).toGradedAffineAlgebra.projFunctor.map
    (homOfLE (BaseChangeChartIndex.le_V (leOfHom hij)))

theorem baseChangeChartTrans_f {i j : BaseChangeChartIndex g} (hij : i ⟶ j) :
    baseChangeChartTrans g 𝒜 hij ≫ (baseChangeChartCover g 𝒜).f j = (baseChangeChartCover g 𝒜).f i :=
  (𝒜.pullback g).toGradedAffineAlgebra.map_projChart (BaseChangeChartIndex.le_V (leOfHom hij))

/-- **Local directedness of the small-chart cover** (`Scheme.Cover.LocallyDirected.directed`):
every point `x` of `Proj((g^*𝒜)(V_i)) ×_{Proj_{S'}(g^*𝒜)} Proj((g^*𝒜)(V_j))` comes from a chart
`Proj((g^*𝒜)(V_k))` with `k ≤ i`, `k ≤ j`.

Source: Stacks 01O3 (the small charts form a basis); Mathlib `Cover.LocallyDirected`.

Proof. Let `p := pullback.fst x ∈ Proj((g^*𝒜)(V_i))` and `q := pullback.snd x`, with
`projChart V_i p = projChart V_j q =: z` (pullback condition). Let `s := π'(z) ∈ V_i ∩ V_j` and
`t := g(s) ∈ U_i ∩ U_j` (from `projChart_hom` and `V_i ≤ g⁻¹U_i`).
(1) `exists_basicOpen_le_affine_inter U_i.2 U_j.2 t` gives `a ∈ Γ(U_i)`, `b ∈ Γ(U_j)` with
`D(a) = D(b) ∋ t`; put `U_k := U_i.basicOpen a`, so `U_k ≤ U_i` and `U_k ≤ U_j` in the site
(the latter since `U_k = U_j.basicOpen b` as elements of the subtype).
(2) `exists_basicOpen_le_affine_inter V_i.2 V_j.2 s` gives `c, d` with `D(c) = D(d) ∋ s`; then
`(V_i.basicOpen c).2.exists_basicOpen_le ⟨s, _⟩ (hs : s ∈ g⁻¹U_k)` gives `e ∈ Γ(D(c))` with
`D(e) ≤ g⁻¹U_k`, `s ∈ D(e)`; put `V_k := (V_i.basicOpen c).basicOpen e`. Then `V_k ≤ V_i` and
`V_k ≤ V_j` in the site by transitivity (`le_trans` in `AffineZariskiSite` is
`basicOpen_basicOpen_is_basicOpen`), and `V_k ≤ g⁻¹U_k`. So `k := ((U_k, V_k), _)` with `k ≤ i`,
`k ≤ j`.
(3) `z ∈ π'⁻¹V_k = (projChart V_k).opensRange` (`proj_preimage_eq_opensRange`), so
`z = projChart V_k y` for some `y`.
(4) `pullback.lift (trans hki) (trans hkj) _ y = x`: both points of the fibre product have the same
image under `pullback.fst ≫ projChart V_i` (namely `z`, using `map_projChart`), and this composite
is an open immersion (`IsOpenImmersion` of a composite of the pullback projection of open
immersions with an open immersion), hence injective on points
(`Scheme.Hom.injective` / `IsOpenImmersion.base_open.injective`).
The formal proof follows this route, with one simplification in (4): since both points of the
fibre product have the same image under `pullback.fst` (an open immersion, hence injective on
points), it suffices to show `trans hki y = p`, which follows from `projChart V_i (trans hki y) =
projChart V_k y = z = projChart V_i p` and injectivity of the open immersion `projChart V_i`. -/
theorem baseChangeChart_directed {i j : BaseChangeChartIndex g}
    (x : (CategoryTheory.Limits.pullback ((baseChangeChartCover g 𝒜).f i)
      ((baseChangeChartCover g 𝒜).f j)).carrier) :
    ∃ (k : BaseChangeChartIndex g) (hki : k ⟶ i) (hkj : k ⟶ j) (y : (baseChangeChartCover g 𝒜).X k),
      CategoryTheory.Limits.pullback.lift (baseChangeChartTrans g 𝒜 hki) (baseChangeChartTrans g 𝒜 hkj)
        (by rw [baseChangeChartTrans_f, baseChangeChartTrans_f]) y = x := by
  -- the two projections of `x` and the point `z` of `Proj_{S'}(g^*𝒜)` they both map to
  set p := CategoryTheory.Limits.pullback.fst ((baseChangeChartCover g 𝒜).f i)
    ((baseChangeChartCover g 𝒜).f j) x with hp
  set q := CategoryTheory.Limits.pullback.snd ((baseChangeChartCover g 𝒜).f i)
    ((baseChangeChartCover g 𝒜).f j) x with hq
  have hpq : (𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2 p =
      (𝒜.pullback g).toGradedAffineAlgebra.projChart j.1.2 q := by
    rw [hp, hq, ← AlgebraicGeometry.Scheme.Hom.comp_apply, ← AlgebraicGeometry.Scheme.Hom.comp_apply]
    exact congrArg (fun φ => φ x) (CategoryTheory.Limits.pullback.condition
      (f := (baseChangeChartCover g 𝒜).f i) (g := (baseChangeChartCover g 𝒜).f j))
  -- `s := π'(z)` lies in every chart open through which `z` is presented
  have hsV : ∀ (V : S'.AffineZariskiSite) (r : AlgebraicGeometry.Proj
      ((𝒜.pullback g).toGradedAffineAlgebra.grading V)),
      (𝒜.pullback g).toGradedAffineAlgebra.relativeProj.hom
        ((𝒜.pullback g).toGradedAffineAlgebra.projChart V r) ∈ V.toOpens := by
    intro V r
    rw [← AlgebraicGeometry.Scheme.Hom.comp_apply,
      (𝒜.pullback g).toGradedAffineAlgebra.projChart_hom V, AlgebraicGeometry.Scheme.Hom.comp_apply]
    exact ((𝒜.pullback g).toGradedAffineAlgebra.projToOpen V r).2
  set s := (𝒜.pullback g).toGradedAffineAlgebra.relativeProj.hom
    ((𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2 p) with hs
  have hsi : s ∈ i.1.2.toOpens := hsV i.1.2 p
  have hsj : s ∈ j.1.2.toOpens := by rw [hs, hpq]; exact hsV j.1.2 q
  have hti : g s ∈ i.1.1.toOpens := i.2 hsi
  have htj : g s ∈ j.1.1.toOpens := j.2 hsj
  -- (1) the affine open `U_k ⊆ U_i ∩ U_j` containing `t = g s`
  obtain ⟨a, b, hab, hta⟩ :=
    AlgebraicGeometry.exists_basicOpen_le_affine_inter i.1.1.2 j.1.1.2 (g s) ⟨hti, htj⟩
  let Uk : S.AffineZariskiSite := i.1.1.basicOpen a
  have hUki : Uk ≤ i.1.1 := i.1.1.basicOpen_le a
  have hUkj : Uk ≤ j.1.1 := ⟨b, hab.symm⟩
  -- (2) the affine open `V_k ⊆ V_i ∩ V_j ∩ g⁻¹U_k` containing `s`
  obtain ⟨c, d, hcd, hsc⟩ :=
    AlgebraicGeometry.exists_basicOpen_le_affine_inter i.1.2.2 j.1.2.2 s ⟨hsi, hsj⟩
  have hsUk : s ∈ g ⁻¹ᵁ Uk.toOpens := hta
  obtain ⟨e, he₁, he₂⟩ :=
    (i.1.2.basicOpen c).2.exists_basicOpen_le (V := g ⁻¹ᵁ Uk.toOpens) ⟨s, hsUk⟩ hsc
  let Vk : S'.AffineZariskiSite := (i.1.2.basicOpen c).basicOpen e
  have hVki : Vk ≤ i.1.2 :=
    le_trans (AlgebraicGeometry.Scheme.AffineZariskiSite.basicOpen_le _ e) (i.1.2.basicOpen_le c)
  have hVkj : Vk ≤ j.1.2 :=
    le_trans (AlgebraicGeometry.Scheme.AffineZariskiSite.basicOpen_le _ e) ⟨d, hcd.symm⟩
  have hVk : Vk.toOpens ≤ g ⁻¹ᵁ Uk.toOpens := he₁
  let k : BaseChangeChartIndex g := ⟨(Uk, Vk), hVk⟩
  have hki : k ≤ i := ⟨hUki, hVki⟩
  have hkj : k ≤ j := ⟨hUkj, hVkj⟩
  -- (3) `z ∈ π'⁻¹V_k` is in the image of the chart of `V_k`
  have hz : (𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2 p ∈
      ((𝒜.pullback g).toGradedAffineAlgebra.projChart Vk).opensRange := by
    rw [← (𝒜.pullback g).toGradedAffineAlgebra.proj_preimage_eq_opensRange]
    exact he₂
  obtain ⟨y, hy⟩ := hz
  refine ⟨k, homOfLE hki, homOfLE hkj, y, ?_⟩
  -- (4) both points of the fibre product have the same first projection, which is an open immersion
  have : AlgebraicGeometry.IsOpenImmersion ((baseChangeChartCover g 𝒜).f j) :=
    (𝒜.pullback g).toGradedAffineAlgebra.projChart_isOpenImmersion j.1.2
  apply (CategoryTheory.Limits.pullback.fst ((baseChangeChartCover g 𝒜).f i)
    ((baseChangeChartCover g 𝒜).f j)).isOpenEmbedding.injective
  rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, CategoryTheory.Limits.pullback.lift_fst, ← hp]
  apply ((𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2).isOpenEmbedding.injective
  rw [← AlgebraicGeometry.Scheme.Hom.comp_apply]
  exact (congrArg (fun φ => φ y) (baseChangeChartTrans_f g 𝒜 (homOfLE hki))).trans hy

/-- The small-chart cover is locally directed (Mathlib `Scheme.Cover.LocallyDirected`); a `def`,
supplied with `letI` where needed (no global instance). -/
@[instance_reducible]
def baseChangeChartCoverLocallyDirected : (baseChangeChartCover g 𝒜).LocallyDirected where
  trans hij := baseChangeChartTrans g 𝒜 hij
  trans_id i := by
    show (𝒜.pullback g).toGradedAffineAlgebra.projFunctor.map _ = 𝟙 _
    rw [show homOfLE (BaseChangeChartIndex.le_V (leOfHom (𝟙 i))) = 𝟙 i.1.2 from
      Subsingleton.elim _ _]
    exact (𝒜.pullback g).toGradedAffineAlgebra.projFunctor.map_id _
  trans_comp hij hjk := by
    show (𝒜.pullback g).toGradedAffineAlgebra.projFunctor.map _ =
      (𝒜.pullback g).toGradedAffineAlgebra.projFunctor.map _ ≫
        (𝒜.pullback g).toGradedAffineAlgebra.projFunctor.map _
    rw [← Functor.map_comp]
    exact congrArg _ (Subsingleton.elim _ _)
  w hij := baseChangeChartTrans_f g 𝒜 hij
  directed x := baseChangeChart_directed g 𝒜 x
  property_trans {i j} hij := by
    have hj : AlgebraicGeometry.IsOpenImmersion ((baseChangeChartCover g 𝒜).f j) :=
      (𝒜.pullback g).toGradedAffineAlgebra.projChart_isOpenImmersion j.1.2
    have hi : AlgebraicGeometry.IsOpenImmersion
        (baseChangeChartTrans g 𝒜 hij ≫ (baseChangeChartCover g 𝒜).f j) := by
      rw [baseChangeChartTrans_f]
      exact (𝒜.pullback g).toGradedAffineAlgebra.projChart_isOpenImmersion i.1.2
    exact @AlgebraicGeometry.IsOpenImmersion.of_comp _ _ _ (baseChangeChartTrans g 𝒜 hij)
      ((baseChangeChartCover g 𝒜).f j) hj hi

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
