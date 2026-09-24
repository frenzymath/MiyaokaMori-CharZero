import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjBaseChangeCover

/-! # Gluing the base-change comparison morphism of a relative Proj

Statement: the **global comparison map** of Stacks 01O3,
`baseChangeHom g 𝒜 : Proj_{S'}(g^*𝒜) ⟶ Proj_S(𝒜)`, glued from the local comparison maps
`baseChangeProjMap g 𝒜 U V hV ≫ projChart U` on the small-chart cover
(`RelativeProjBaseChangeCover.lean`, Mathlib `Scheme.Cover.glueMorphismsOfLocallyDirected`;
the compatibility with the transition maps is `baseChangeProjMap_compat`). Properties:
* `projChart_comp_baseChangeHom`: on the chart of `(U, V)` it is the local comparison map;
* `baseChangeHom_hom`: it lies over `g` (`baseChangeHom ≫ π = π' ≫ g`);
* `isPullback_baseChangeHom`: the square `π' / baseChangeHom / g / π` is a pullback square
  (Stacks 01O3, first assertion), checked locally on the open cover `baseChangeBaseCover g` of `S'`
  by the small affine opens `V_i` (Mathlib `Scheme.isPullback_of_openCover`); see its docstring.

The chart-level inputs are `baseChangeProjMap_isPullback` (`…BaseChangeLocal`) and `baseChangeChart_directed`
(`…BaseChangeCover`).

The twisting-sheaf statement is `baseChangeHom_twist`; the comparison theorem
(`RelativeProjBaseChangeComparison.lean`) is assembled from these.

Source: Stacks 01O3; the base change of `P(O ⊕ L)` in Corollary 4.3 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {S S' : AlgebraicGeometry.Scheme.{u}} (g : S' ⟶ S) (𝒜 : S.GradedQCAlgebra)

/-- The leg on the chart of `(U, V)`: `Proj((g^*𝒜)(V)) ⟶ Proj(𝒜(U)) ⟶ Proj_S(𝒜)`. -/
def baseChangeChartLeg (i : BaseChangeChartIndex g) :
    (baseChangeChartCover g 𝒜).X i ⟶ (AlgebraicGeometry.Scheme.relativeProj 𝒜).left :=
  baseChangeProjMap g 𝒜 i.1.1 i.1.2 i.2 ≫ 𝒜.toGradedAffineAlgebra.projChart i.1.1

/-- Variable-level rewriting lemma (the concrete schemes enter only through `exact`, which keeps the
kernel from unfolding them). -/
private theorem comp_leg_aux {A B C D E : AlgebraicGeometry.Scheme.{u}} (t : A ⟶ B) (ψj : B ⟶ C)
    (ψi : A ⟶ D) (m : D ⟶ C) (cj : C ⟶ E) (ci : D ⟶ E) (h1 : t ≫ ψj = ψi ≫ m)
    (h2 : m ≫ cj = ci) : t ≫ ψj ≫ cj = ψi ≫ ci := by
  rw [← Category.assoc, h1, Category.assoc, h2]

/-- The legs are compatible with the transition maps of the small-chart cover. -/
theorem baseChangeChartTrans_leg {i j : BaseChangeChartIndex g} (hij : i ⟶ j) :
    baseChangeChartTrans g 𝒜 hij ≫ baseChangeChartLeg g 𝒜 j = baseChangeChartLeg g 𝒜 i :=
  comp_leg_aux _ _ _ _ _ _
    (baseChangeProjMap_compat g 𝒜 j.1.1 j.1.2 j.2 (BaseChangeChartIndex.le_U (leOfHom hij))
      (BaseChangeChartIndex.le_V (leOfHom hij)) i.2)
    (𝒜.toGradedAffineAlgebra.map_projChart (BaseChangeChartIndex.le_U (leOfHom hij)))

/-- **The comparison map** `Proj_{S'}(g^*𝒜) ⟶ Proj_S(𝒜)` (Stacks 01O3), glued from the local
comparison maps over the locally directed small-chart cover. -/
def baseChangeHom :
    (AlgebraicGeometry.Scheme.relativeProj (𝒜.pullback g)).left ⟶
      (AlgebraicGeometry.Scheme.relativeProj 𝒜).left :=
  letI := baseChangeChartCoverLocallyDirected g 𝒜
  (baseChangeChartCover g 𝒜).glueMorphismsOfLocallyDirected (baseChangeChartLeg g 𝒜)
    (fun hij => baseChangeChartTrans_leg g 𝒜 hij)

/-- On the chart of `(U, V)` the comparison map is the local comparison map. -/
@[reassoc]
theorem projChart_comp_baseChangeHom (i : BaseChangeChartIndex g) :
    (𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2 ≫ baseChangeHom g 𝒜 =
      baseChangeProjMap g 𝒜 i.1.1 i.1.2 i.2 ≫ 𝒜.toGradedAffineAlgebra.projChart i.1.1 :=
  letI := baseChangeChartCoverLocallyDirected g 𝒜
  (baseChangeChartCover g 𝒜).map_glueMorphismsOfLocallyDirected (baseChangeChartLeg g 𝒜)
    (fun hij => baseChangeChartTrans_leg g 𝒜 hij) i

/-- Variable-level diagram chase for `baseChangeHom_hom` (concrete schemes enter through `exact`). -/
private theorem over_aux {P' P S S' V U PV PU : AlgebraicGeometry.Scheme.{u}} (c : PV ⟶ P')
    (φ : P' ⟶ P) (π : P ⟶ S) (π' : P' ⟶ S') (g : S' ⟶ S) (ψ : PV ⟶ PU) (cU : PU ⟶ P)
    (pU : PU ⟶ U) (pV : PV ⟶ V) (ιU : U ⟶ S) (ιV : V ⟶ S') (r : V ⟶ U)
    (e1 : c ≫ φ = ψ ≫ cU) (e2 : cU ≫ π = pU ≫ ιU) (e3 : c ≫ π' = pV ≫ ιV)
    (e4 : pV ≫ r = ψ ≫ pU) (e5 : r ≫ ιU = ιV ≫ g) :
    c ≫ φ ≫ π = c ≫ π' ≫ g := by
  rw [← Category.assoc, e1, Category.assoc, e2, ← Category.assoc, ← e4, Category.assoc, e5,
    ← Category.assoc, ← e3, Category.assoc]

/-- The comparison map lies over `g`. -/
@[reassoc]
theorem baseChangeHom_hom :
    baseChangeHom g 𝒜 ≫ (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom =
      (AlgebraicGeometry.Scheme.relativeProj (𝒜.pullback g)).hom ≫ g := by
  apply (baseChangeChartCover g 𝒜).hom_ext
  intro i
  exact over_aux _ _ _ _ _ _ _ _ _ _ _ _ (projChart_comp_baseChangeHom g 𝒜 i)
    (𝒜.toGradedAffineAlgebra.projChart_hom i.1.1)
    ((𝒜.pullback g).toGradedAffineAlgebra.projChart_hom i.1.2)
    (baseChangeProjMap_isPullback g 𝒜 i.1.1 i.1.2 i.2).w
    (AlgebraicGeometry.Scheme.Hom.resLE_comp_ι g i.2)

/-- The small affine opens `V_i`, `i = (U_i, V_i) ∈ BaseChangeChartIndex g`, cover `S'`:
given `s ∈ S'`, pick an affine open `U ∋ g s` of `S` and an affine open `V ⊆ g⁻¹U` containing `s`
(`Scheme.exists_affine_mem_range_and_range_subset`). -/
theorem baseChangeChartIndex_covers (s : S') :
    ∃ (i : BaseChangeChartIndex g) (y : (i.1.2.toOpens.toScheme : AlgebraicGeometry.Scheme.{u})),
      i.1.2.toOpens.ι y = s := by
  obtain ⟨R, f, hf, hmem, -⟩ := AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset
    (X := S) (U := ⊤) (x := g s) trivial
  let U : S.AffineZariskiSite := ⟨f.opensRange, AlgebraicGeometry.isAffineOpen_opensRange f⟩
  have hsU : s ∈ g ⁻¹ᵁ U.toOpens := hmem
  obtain ⟨R', f', hf', hmem', hsub⟩ :=
    AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset (X := S')
      (U := g ⁻¹ᵁ U.toOpens) hsU
  let V : S'.AffineZariskiSite := ⟨f'.opensRange, AlgebraicGeometry.isAffineOpen_opensRange f'⟩
  have hV : V.toOpens ≤ g ⁻¹ᵁ U.toOpens := fun x hx => hsub hx
  exact ⟨⟨(U, V), hV⟩, ⟨s, hmem'⟩, rfl⟩

/-- The open cover of `S'` by the small affine opens `V_i`, `i ∈ BaseChangeChartIndex g`
(the base of the small-chart cover `baseChangeChartCover`). -/
abbrev baseChangeBaseCover : S'.OpenCover :=
  AlgebraicGeometry.Scheme.Cover.mkOfCovers (BaseChangeChartIndex g)
    (fun i => i.1.2.toOpens.toScheme) (fun i => i.1.2.toOpens.ι) (baseChangeChartIndex_covers g)

/-- Variable-level side conditions of `IsPullback.of_iso` for `isPullback_baseChangeHom` (the two
spellings `Scheme.relativeProj (𝒜.pullback g)` / `(𝒜.pullback g).toGradedAffineAlgebra.relativeProj`
are defeq but not syntactically equal, so the concrete schemes enter through `exact`). -/
private theorem of_iso_aux₁ {P Q Y : AlgebraicGeometry.Scheme.{u}} (a : P ⟶ Y) (e : P ≅ Q)
    (b : Q ⟶ Y) (h : e.hom ≫ b = a) : a ≫ (Iso.refl Y).hom = e.hom ≫ b := by
  rw [Iso.refl_hom, Category.comp_id, h]

private theorem of_iso_aux₂ {P Q Y Z : AlgebraicGeometry.Scheme.{u}} (a : P ⟶ Y) (e : P ≅ Q)
    (b : Q ⟶ Y) (c : Y ⟶ Z) (h : e.hom ≫ b = a) :
    (a ≫ c) ≫ (Iso.refl Z).hom = e.hom ≫ b ≫ c := by
  rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, h]

private theorem of_iso_aux₃ {Y Z : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ Z) :
    f ≫ (Iso.refl Z).hom = (Iso.refl Y).hom ≫ f := by
  rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- **Stacks 01O3, first assertion**: the square
```
Proj_{S'}(g^*𝒜) --baseChangeHom--> Proj_S(𝒜)
      | π'                            | π
      v                               v
      S' ------------ g ------------> S
```
is a pullback square.

Source: Stacks 01O3 (`constructions-lemma-relative-proj-base-change`), 01N2, 01NQ.

Proof. Pullback squares of schemes are local on the base of the left vertical map
(Mathlib `AlgebraicGeometry.Scheme.isPullback_of_openCover`, applied with `fWX = π'`, `fWY =
baseChangeHom`, `fXZ = g`, `fYZ = π` and the open cover `𝒱` of `S'` by the small affine opens
`V_i`, `i ∈ BaseChangeChartIndex g`, `𝒱.f i = V_i.ι`; `𝒱` covers `S'` since every `s ∈ S'` has an affine
neighbourhood inside `g⁻¹U` for an affine `U ∋ g s`). For each `i = (U, V)` the required square is
`IsPullback (pullback.snd π' V.ι) (pullback.fst π' V.ι ≫ baseChangeHom) (V.ι ≫ g) π`.
(1) By `projChart_isPullback V` (Stacks 01NQ, `RelativeProj.lean`) the chart square
`projToOpen V / projChart V / V.ι / π'` is a pullback, giving `e : Proj((g^*𝒜)(V)) ≅ pullback π' V.ι`
(`IsPullback.isoPullback` of the flipped square) with `e.hom ≫ fst = projChart V`,
`e.hom ≫ snd = projToOpen V`.
(2) Paste vertically (`IsPullback.paste_vert`) the local square `baseChangeProjMap_isPullback`
(`projToOpen V / baseChangeProjMap / g.resLE / projToOpen U`) with the chart square of `U`
(`projToOpen U / projChart U / U.ι / π`): this gives
`IsPullback (projToOpen V) (baseChangeProjMap ≫ projChart U) (g.resLE ≫ U.ι) π`.
(3) Rewrite `baseChangeProjMap ≫ projChart U = projChart V ≫ baseChangeHom`
(`projChart_comp_baseChangeHom`) and `g.resLE ≫ U.ι = V.ι ≫ g` (`Scheme.Hom.resLE_comp_ι`), and
transport along the isomorphism `e` of (1) (`IsPullback.of_iso` with `e` on the corner and
identities elsewhere) to obtain the square of the cover in the shape required by
`isPullback_of_openCover`.
The cover `𝒱` is `baseChangeBaseCover g` (covering by `baseChangeChartIndex_covers`); the chart-level
input is `baseChangeProjMap_isPullback` (01N2 on a chart, `RelativeProjBaseChangeLocal.lean`). -/
theorem isPullback_baseChangeHom :
    CategoryTheory.IsPullback (AlgebraicGeometry.Scheme.relativeProj (𝒜.pullback g)).hom
      (baseChangeHom g 𝒜) g (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom := by
  refine AlgebraicGeometry.Scheme.isPullback_of_openCover _ _ _ _ (baseChangeBaseCover g) ?_
  rintro (i : BaseChangeChartIndex g)
  show CategoryTheory.IsPullback
    (pullback.snd (AlgebraicGeometry.Scheme.relativeProj (𝒜.pullback g)).hom i.1.2.toOpens.ι)
    (pullback.fst (AlgebraicGeometry.Scheme.relativeProj (𝒜.pullback g)).hom i.1.2.toOpens.ι ≫
      baseChangeHom g 𝒜)
    (i.1.2.toOpens.ι ≫ g) (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom
  -- (1) the chart square of `V`, flipped: `Proj((g^*𝒜)(V)) ≅ pullback π' V.ι`
  have h1 := ((𝒜.pullback g).toGradedAffineAlgebra.projChart_isPullback i.1.2).flip
  -- (2) paste the local square with the chart square of `U`
  have h2 := (baseChangeProjMap_isPullback g 𝒜 i.1.1 i.1.2 i.2).paste_vert
    (𝒜.toGradedAffineAlgebra.projChart_isPullback i.1.1)
  -- (3) rewrite and transport along the isomorphism of (1)
  rw [← projChart_comp_baseChangeHom, AlgebraicGeometry.Scheme.Hom.resLE_comp_ι] at h2
  exact h2.of_iso h1.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (of_iso_aux₁ _ _ _ h1.isoPullback_hom_snd) (of_iso_aux₂ _ _ _ _ h1.isoPullback_hom_fst)
    (of_iso_aux₃ _) (of_iso_aux₃ _)

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
