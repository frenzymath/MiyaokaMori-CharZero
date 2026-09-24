import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousLocalFormula
import MiyaokaMori.AlgebraicGeometry.Modules.HomogeneousEquationAsSection
import MiyaokaMori.Paper.S2WeightedJets.Cone.HomogeneousIdealGenerators
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbedding
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeOpen
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeToProductEquationVanishes
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeToProductZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSection
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineCone
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOfNowhereZeroTuple

/-! # The projection of the punctured cone to `C × X`

The morphism `𝒵^× → C × X`: the base point gives the `C`-component, and the projective class of a
nonzero vector gives the `X`-component (§2.1 of the paper, the morphism `p : 𝒵^× → C × X`).
-/
/- `sectionPullbackAlong` is the primary definition (its body is the adjunction unit) and
`AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback` its `Γ`-typed reducible abbreviation: the sites below use
`simp only [sectionPullbackAlong_eq_pullback]` (to reach the latter) or plain `unfold sectionPullbackAlong`
(to reach the unit). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## The components of `puncturedConeToProduct` and their proof obligations

Notation (as in §2.1 of the paper): `W := Z^×` (the cone minus the zero section), `t : W → C` the base point,
`V := A^{⊕(N+1)}`, `z ∈ Γ(W, t^*V)` the section corresponding to `W ↪ Tot(V)`, and `z_ℓ` its `ℓ`-th component.
-/

section PuncturedConeToProduct

/-- `t : W = Z^× ⟶ C`, the base point: `W ↪ Z` followed by `Z → C`. -/
noncomputable def puncturedConeToProduct.base {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) :
    (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme ⟶ C :=
  (puncturedCone A N E.deg hdeg E.F E.homogeneous).ι ≫
    (twistedAffineCone A N E.deg E.F E.homogeneous).hom

set_option warn.classDefReducibility false in
/-- The `k`-scheme structure on `W`: `t ≫ (C ↘ Spec k)`. **Not registered as a global instance** (it would
change the behaviour of `split` downstream); it is introduced locally by
`letI := puncturedConeToProduct.overK e E A hdeg`, the same term as the `letI` in the body of
`puncturedConeToProduct`. -/
noncomputable def puncturedConeToProduct.overK {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) :
    (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme.Over
      (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  ⟨puncturedConeToProduct.base e E A hdeg ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩

/-- The compatibility condition for the `Over.homMk` of `toTot`: `(W ↪ Z ↪ Tot(V)) ≫ (Tot(V) → C) = t`.

Proof: `(twistedAffineCone A N E.deg E.F E.homogeneous).left` is by definition the closed subscheme of
`Tot(A^{⊕(N+1)})` cut out by the ideal sheaf `⨆ j, idealSheafOfSection _ (homogeneousEquationSection …)` of
the homogeneous equations, and `twistedAffineCone … .hom` is by definition `subschemeι ≫ (totalSpace V).hom`.
Both sides are therefore `W.ι ≫ subschemeι ≫ (totalSpace V).hom`, and `Category.assoc` finishes. -/
theorem puncturedConeToProduct.toTot_w {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) :
    ((puncturedCone A N E.deg hdeg E.F E.homogeneous).ι ≫
        (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
          (homogeneousEquationSection A N (E.F j) (E.homogeneous j))).subschemeι) ≫
      (AlgebraicGeometry.Scheme.totalSpace
        (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom =
    (CategoryTheory.Over.mk (puncturedConeToProduct.base e E A hdeg)).hom := by
  exact CategoryTheory.Category.assoc _ _ _

/-- `W ↪ Tot(A^{⊕(N+1)})`, as a morphism over `C`. -/
noncomputable def puncturedConeToProduct.toTot {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) :
    CategoryTheory.Over.mk (puncturedConeToProduct.base e E A hdeg) ⟶
      AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) :=
  CategoryTheory.Over.homMk
    ((puncturedCone A N E.deg hdeg E.F E.homogeneous).ι ≫
      (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
        (homogeneousEquationSection A N (E.F j) (E.homogeneous j))).subschemeι)
    (puncturedConeToProduct.toTot_w e E A hdeg)

/-- `z_ℓ ∈ Γ(W, t^*A)`: the `ℓ`-th component of the section `z` corresponding to `W ↪ Tot(A^{⊕(N+1)})`
under `totalSpaceHomEquiv`. -/
noncomputable def puncturedConeToProduct.coord {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) (ℓ : Fin (N + 1)) :
    (((AlgebraicGeometry.Scheme.Modules.pullback
      (puncturedConeToProduct.base e E A hdeg)).obj A).val.obj (Opposite.op ⊤) : Type u) :=
  (((AlgebraicGeometry.Scheme.Modules.pullback (puncturedConeToProduct.base e E A hdeg)).map
    (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
    (AlgebraicGeometry.Scheme.totalSpaceHomEquiv
      (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
      (CategoryTheory.Over.mk (puncturedConeToProduct.base e E A hdeg))
      (puncturedConeToProduct.toTot e E A hdeg))

/-- The coordinates `z` are nowhere all zero on `W = Z^×`: this is exactly the content of "removing the zero
section" (Definition 2.1 of the paper).

Proof: `puncturedCone` is by definition the open complement of the zero section in `Z`, i.e. `Z \ σ(C)`
(`PuncturedConeOpen.lean`: the vertex section `σ` is the lift through the closed immersion). Suppose all `z_ℓ`
vanish at `w ∈ W`. `isZeroAt_tautological_coordinate_of_isZeroAt` (`PuncturedConeToProductZeroSection.lean`;
naturality of coordinates + `isZeroAt_map` + `isZeroAt_of_isZeroAt_sectionPullbackAlong`) transports the vanishing
to `Tot(V)`: all coordinates of the tautological section vanish at `j(w)` (`j = W ↪ Z ↪ Tot(V)`). Then
`mem_range_zeroSection_of_forall_isZeroAt_coordinate` gives `j(w) = zeroSection(c)`; by
`IsClosedImmersion.lift_fac` (the vertex section satisfies `σ₀ ≫ ι_Z = zeroSection`) and injectivity of the
closed immersion `ι_Z` on points (`Scheme.Hom.isClosedEmbedding`), `W.ι(w) = σ₀(c)`, contradicting
`W = Z ∖ σ₀(C)` (`complementOfClosedImmersion`). -/
theorem puncturedConeToProduct.coord_nowhereZero {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) :
    ∀ w : (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme,
      ∃ ℓ, ¬ IsZeroAt (puncturedConeToProduct.coord e E A hdeg ℓ) w := by
  intro w
  by_contra hall
  push Not at hall
  let V := AlgebraicGeometry.Scheme.Modules.pow A (N + 1)
  let T := AlgebraicGeometry.Scheme.totalSpace V
  let I : T.left.IdealSheafData := ⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
    (homogeneousEquationSection A N (E.F j) (E.homogeneous j))
  let W := puncturedCone A N E.deg hdeg E.F E.homogeneous
  let j : W.toScheme ⟶ T.left := W.ι ≫ I.subschemeι
  -- all coordinates of the tautological section vanish at j w
  have hτ : ∀ ℓ : Fin (N + 1), IsZeroAt
      ((((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map
        (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T (CategoryTheory.CategoryStruct.id _))) (j.base w) :=
    fun ℓ => isZeroAt_tautological_coordinate_of_isZeroAt V
      (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) ℓ) j
      (puncturedConeToProduct.base e E A hdeg) (puncturedConeToProduct.toTot_w e E A hdeg) w (hall ℓ)
  -- hence j w lies on the zero section
  obtain ⟨c, hc⟩ :=
    AlgebraicGeometry.Scheme.mem_range_zeroSection_of_forall_isZeroAt_coordinate A N (j.base w) hτ
  -- the vertex section σ₀ : C → Z (the same term as in the definition of `puncturedCone`)
  let σ0 : C ⟶ (twistedAffineCone A N E.deg E.F E.homogeneous).left :=
    (AlgebraicGeometry.IsClosedImmersion.lift I.subschemeι (AlgebraicGeometry.Scheme.zeroSection V) (by
        obtain ⟨τ, hτ'⟩ := zeroSection_mem_twistedAffineCone A N E.deg hdeg E.F E.homogeneous
        rw [← hτ']
        exact AlgebraicGeometry.Scheme.Hom.le_ker_comp _ _) : C ⟶ I.subscheme)
  have hσ0 : σ0 ≫ I.subschemeι = AlgebraicGeometry.Scheme.zeroSection V :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac I.subschemeι (AlgebraicGeometry.Scheme.zeroSection V) _
  -- w ∈ W = Z ∖ σ₀(C)
  have hmem : W.ι.base w ∉ Set.range σ0.base := by
    have h1 : W.ι.base w ∈ Set.range W.ι.base := ⟨w, rfl⟩
    rw [AlgebraicGeometry.Scheme.Opens.range_ι] at h1
    exact h1
  apply hmem
  refine ⟨c, ?_⟩
  apply (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding I.subschemeι).injective
  change (σ0 ≫ I.subschemeι).base c = j.base w
  rw [hσ0]
  exact hc

/-- `eval_coord_eq_zero` with the base point map `t` generalized to any `q : W → C` with
`j ≫ p = q` (`j = W.ι ≫ I.subschemeι`, `p : Tot(V) → C`), so that `subst` removes the `Over.mk`
transport. Proof: `F_j(τ)` vanishes on `Z` (`sectionPullbackAlong_subschemeι_eq_zero`, since
`I(F_j(τ)) ≤ I`), hence on `W` (`pullback_comp`); `evalHomogeneousAtSections_pullback` along `j`
gives `F_j(j^*τ_0, …, j^*τ_N) = 0`; the coordinates are the images of `j^*τ_ℓ` under
`pullbackComp j p` (`totalSpaceHomEquiv_naturality_map`), and `evalHomogeneousAtSections_iso_eq_zero`
transports along that isomorphism. -/
theorem puncturedConeToProduct.eval_coord_eq_zero_aux {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) (q : (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme ⟶ C)
    (hq : ((puncturedCone A N E.deg hdeg E.F E.homogeneous).ι ≫
        (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
          (homogeneousEquationSection A N (E.F j) (E.homogeneous j))).subschemeι) ≫
      (AlgebraicGeometry.Scheme.totalSpace
        (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom = q) :
    letI : (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme.Over
      (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨q ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    ∀ j, evalHomogeneousAtSections ((AlgebraicGeometry.Scheme.Modules.pullback q).obj A)
      (E.F j) (E.homogeneous j)
      (fun ℓ => (((AlgebraicGeometry.Scheme.Modules.pullback q).map
        (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
          (CategoryTheory.Over.mk q) (CategoryTheory.Over.homMk _ hq))) = 0 := by
  subst hq
  intro j
  let V := AlgebraicGeometry.Scheme.Modules.pow A (N + 1)
  let T := AlgebraicGeometry.Scheme.totalSpace V
  let p := T.hom
  let I : T.left.IdealSheafData := ⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
    (homogeneousEquationSection A N (E.F j) (E.homogeneous j))
  let W := puncturedCone A N E.deg hdeg E.F E.homogeneous
  let jW : W.toScheme ⟶ T.left := W.ι ≫ I.subschemeι
  let instW : W.toScheme.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(jW ≫ p) ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  let instT : T.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨p ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have hover : jW.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨by
    show jW ≫ (p ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) =
      (jW ≫ p) ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    rw [Category.assoc]⟩
  -- F_j(τ) vanishes on Z, hence on W
  have hI : AlgebraicGeometry.Scheme.idealSheafOfSection _
      (homogeneousEquationSection A N (E.F j) (E.homogeneous j)) ≤ I :=
    le_iSup (fun j => AlgebraicGeometry.Scheme.idealSheafOfSection _
      (homogeneousEquationSection A N (E.F j) (E.homogeneous j))) j
  have hz1 : sectionPullbackAlong I.subschemeι
      (homogeneousEquationSection A N (E.F j) (E.homogeneous j)) = 0 :=
    AlgebraicGeometry.Scheme.sectionPullbackAlong_subschemeι_eq_zero I _ _ hI
  have hz2 : sectionPullbackAlong jW (homogeneousEquationSection A N (E.F j) (E.homogeneous j)) = 0 := by
    have h := AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp W.ι I.subschemeι
      (homogeneousEquationSection A N (E.F j) (E.homogeneous j))
    change ((AlgebraicGeometry.Scheme.Modules.pullbackComp W.ι I.subschemeι).app _).hom.app ⊤
      (sectionPullbackAlong W.ι (sectionPullbackAlong I.subschemeι
        (homogeneousEquationSection A N (E.F j) (E.homogeneous j)))) =
      sectionPullbackAlong jW (homogeneousEquationSection A N (E.F j) (E.homogeneous j)) at h
    rw [hz1] at h
    rw [← h]
    have h0 : sectionPullbackAlong W.ι (0 : (((AlgebraicGeometry.Scheme.Modules.pullback I.subschemeι).obj
        (AlgebraicGeometry.Scheme.Modules.tensorPow
          ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A) (E.deg j))).val.obj (Opposite.op ⊤) : Type u)) = 0 := by
      unfold sectionPullbackAlong
      exact map_zero _
    exact (congrArg (fun z => ((AlgebraicGeometry.Scheme.Modules.pullbackComp W.ι I.subschemeι).app
      (AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A) (E.deg j))).hom.app ⊤ z) h0).trans
      (map_zero _)
  -- F_j on the pulled-back tautological coordinates vanishes
  let τ := AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T (CategoryTheory.CategoryStruct.id T)
  let τc : Fin (N + 1) → ((((AlgebraicGeometry.Scheme.Modules.pullback p).obj A).val.obj (Opposite.op ⊤)) : Type u) :=
    fun i => (((AlgebraicGeometry.Scheme.Modules.pullback p).map
      (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom τ
  have h5 := evalHomogeneousAtSections_pullback (k := k) jW
    ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A) (E.F j) (E.homogeneous j) τc
  have hFτ : evalHomogeneousAtSections ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A)
      (E.F j) (E.homogeneous j) τc = homogeneousEquationSection A N (E.F j) (E.homogeneous j) := rfl
  rw [hFτ, hz2] at h5
  have h6 : evalHomogeneousAtSections
      ((AlgebraicGeometry.Scheme.Modules.pullback jW).obj ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A))
      (E.F j) (E.homogeneous j) (fun i => sectionPullbackAlong jW (τc i)) = 0 := by
    rw [← h5]
    exact map_zero _
  -- the coordinates z_ℓ are the images of jW^*τ_ℓ under pullbackComp
  let Θ : (AlgebraicGeometry.Scheme.Modules.pullback jW).obj ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (jW ≫ p)).obj A :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp jW p).app A
  have hcoord : (fun ℓ => (((AlgebraicGeometry.Scheme.Modules.pullback (jW ≫ p)).map
        (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk (jW ≫ p))
          (CategoryTheory.Over.homMk jW rfl))) =
      fun ℓ => ((Θ.hom.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong jW (τc ℓ))) := by
    funext ℓ
    have hn := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality_map V
      (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) ℓ) T jW (𝟙 T)
    rw [Category.comp_id] at hn
    exact hn
  rw [hcoord]
  exact evalHomogeneousAtSections_iso_eq_zero Θ (E.F j) (E.homogeneous j)
    (fun i => sectionPullbackAlong jW (τc i)) h6

/-- **F_j(z) = 0 on W = Z^×**: every defining equation `F_j` of `X ⊆ P^N`, evaluated
(`evalHomogeneousAtSections`) on the coordinate sections `z_ℓ = puncturedConeToProduct.coord ℓ`
∈ Γ(W, t^*A), is zero. This is the hypothesis `hzero` of `projectivizationMorphism_factors`,
from which `emb_ker_le` follows.

Source: Definition 2.1 of the paper (`W ⊆ Z` and `Z` is cut out by the `F_j(z)`); Stacks 02OR.

Notation: `V := A^{⊕(N+1)}`, `p : Tot(V) → C`, `τ` the tautological section, `τ_ℓ = p^*(π_ℓ)(τ)`;
`j : W → Tot(V)` is `W.ι ≫ I.subschemeι` (`I = ⨆_j I(F_j(τ))`, the ideal sheaf of `Z`), `t = j ≫ p`
(`toTot_w`), `d := E.deg j`, `F := E.F j`, and `F(τ) := homogeneousEquationSection A N F hF`
∈ Γ(Tot V, (p^*A)^{⊗d}).

Proof.
1. `I(F(τ)) ≤ I = ker (I.subschemeι) ≤ ker j` (`le_iSup`, `IdealSheafData.ker_subschemeι`,
   `Scheme.Hom.le_ker_comp`): `j` factors through the zero scheme of `F(τ)`.
2. Stacks 02OR, direction "factors through the zero scheme ⇒ the pulled-back section vanishes":
   `sectionPullbackAlong j (F(τ)) = 0`. Argument: on an affine open `U ⊆ Tot V` with a frame `ε` of
   `L := (p^*A)^{⊗d}` (`exists_affine_frame_le`), `F(τ)|_U = c • ε` with `c = coord_ε(F(τ)|_U)`;
   `c ∈ I(F(τ))(U)` (take the functional `coord_ε`), hence `c ∈ (ker j)(U)`, i.e. `j^♯(c) = 0` on
   `j^{-1}U` (`Scheme.Hom.ker` is the kernel of `j^♯`); so `j^*(F(τ))|_{j^{-1}U} = j^♯(c) • j^*ε = 0`
   (`sectionPullbackAlong_smul`); such `U` cover `Tot V`, so the `j^{-1}U` cover `W`, and the
   sheaf separatedness of `j^*L` gives `j^*(F(τ)) = 0`.
   This is `sectionPullbackAlong_subschemeι_eq_zero` (`PuncturedConeToProductEquationVanishes.lean`)
   applied to `I.subschemeι`; then
   `W.ι^*` of `0` is `0`, and `AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp` transports to `j = W.ι ≫ ι`.
3. `evalHomogeneousAtSections_pullback`:
   `θ_d (j^*(F(τ))) = F(j^*τ_0, …, j^*τ_N)` in `Γ(W, (j^*p^*A)^{⊗d})`, `θ_d = pullbackTensorPowIso`.
   With step 2 the left side is `θ_d 0 = 0`, so `F(j^*τ_0, …, j^*τ_N) = 0`. (Here `Tot V` carries the
   `k`-structure `p ≫ (C ↘ Spec k)` used inside `homogeneousEquationSection`, `W` carries
   `overK = t ≫ (C ↘ Spec k)`, and `j` is a `k`-morphism because `j ≫ p = t` (`toTot_w`).)
4. Coordinates: `z_ℓ = Θ_A (j^*τ_ℓ)` where `Θ = pullbackComp j p : j^*p^* ≅ (j ≫ p)^* = t^*`
   (`totalSpaceHomEquiv_naturality_map` in `PuncturedConeToProductZeroSection.lean`, after `subst`
   of `t = j ≫ p`; same transport as in `isZeroAt_tautological_coordinate_of_isZeroAt`).
5. Naturality of `evalHomogeneousAtSections` under the module isomorphism `Θ_A : j^*p^*A ≅ t^*A`:
   `F(Θ_A f_0, …, Θ_A f_N) = Θ_A^{⊗d} (F(f_0, …, f_N))`. `evalHomogeneousAtSections` is a sum of
   scalar multiples of iterated `sectionTensor`s (`evalHomogeneousAtSections.monomial`); a tensor of
   module maps acts factorwise on `tensorSections` (`tensorHom_tensorSections`), so induction on
   `d` exactly as in `evalHomogeneousAtSections_pullback_monomial` gives the claim.
   This is `evalHomogeneousAtSections_iso_eq_zero` (same module).
   Hence `F(z) = Θ_A^{⊗d}(F(j^*τ)) = Θ_A^{⊗d}(0) = 0`.

Formalization: `eval_coord_eq_zero_aux` states the claim for an arbitrary `q` with
`j ≫ p = q` (so that `subst` removes the `Over.mk t` transport of step 4) and is instantiated at
`q = t`, `hq = toTot_w`. -/
theorem puncturedConeToProduct.eval_coord_eq_zero {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) :
    letI := puncturedConeToProduct.overK e E A hdeg
    ∀ j, evalHomogeneousAtSections
      ((AlgebraicGeometry.Scheme.Modules.pullback (puncturedConeToProduct.base e E A hdeg)).obj A)
      (E.F j) (E.homogeneous j) (puncturedConeToProduct.coord e E A hdeg) = 0 :=
  puncturedConeToProduct.eval_coord_eq_zero_aux e E A hdeg (puncturedConeToProduct.base e E A hdeg)
    (puncturedConeToProduct.toTot_w e E A hdeg)

/-- The kernel of the projectivization `φ : W → P^N` contains the kernel of the closed immersion `e.emb`, so
`φ` lifts through `e.emb` to `X`.

Source: §2.1 of the paper; Stacks 01QO (universal property of closed immersions).

Proof: `X ⊆ P^N` is cut out by the homogeneous equations `F_j` (`EmbeddingEquations`: `e.emb.ker` is
generated by the `F_j`). A point of `W` has projective coordinates `(z_0 : … : z_N)`, and `W ⊆ Z` is the cone
cut out by `F_j(z) = 0`, so each `F_j` vanishes on `(z_0, …, z_N)`; `F_j` is homogeneous, so its value on the
projective coordinates is well defined and zero, i.e. `φ^♯` sends the ideal sheaf generated by the `F_j` to
zero, `e.emb.ker ≤ φ.ker`.

Formalization: `projectivizationMorphism_factors` (its hypothesis `IsVanishingLocus e E.F` is `E.spans`, and
the hypothesis `F_j(z) = 0` is `eval_coord_eq_zero` below) gives `Φ` with `Φ ≫ e.emb = φ`, hence
`e.emb.ker ≤ (Φ ≫ e.emb).ker = φ.ker` (`Scheme.Hom.le_ker_comp`). The existence is used only to prove a
proposition; it produces no data. -/
theorem puncturedConeToProduct.emb_ker_le {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) :
    letI := puncturedConeToProduct.overK e E A hdeg
    e.emb.ker ≤
      (projectivizationMorphism (k := k)
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (puncturedConeToProduct.base e E A hdeg)).obj A)
        (puncturedConeToProduct.coord e E A hdeg)
        (puncturedConeToProduct.coord_nowhereZero e E A hdeg)).ker := by
  let _ := puncturedConeToProduct.overK e E A hdeg
  obtain ⟨Φ, hΦ⟩ := projectivizationMorphism_factors (k := k) e E.deg E.F E.homogeneous E.spans
    ((AlgebraicGeometry.Scheme.Modules.pullback (puncturedConeToProduct.base e E A hdeg)).obj A)
    (puncturedConeToProduct.coord e E A hdeg)
    (puncturedConeToProduct.coord_nowhereZero e E A hdeg)
    (puncturedConeToProduct.eval_coord_eq_zero e E A hdeg)
  rw [← hΦ]
  exact AlgebraicGeometry.Scheme.Hom.le_ker_comp _ _

/-- `Φ : W → X`: the lift of the projectivization `φ` through the closed immersion `e.emb` by its universal
property (`IsClosedImmersion.lift`, no choice from an existential). -/
noncomputable def puncturedConeToProduct.toX {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) :
    (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme ⟶ X :=
  letI := puncturedConeToProduct.overK e E A hdeg
  AlgebraicGeometry.IsClosedImmersion.lift e.emb
    (projectivizationMorphism (k := k)
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (puncturedConeToProduct.base e E A hdeg)).obj A)
      (puncturedConeToProduct.coord e E A hdeg)
      (puncturedConeToProduct.coord_nowhereZero e E A hdeg))
    (puncturedConeToProduct.emb_ker_le e E A hdeg)

/-- The compatibility condition for the final `pullback.lift`: `t ≫ (C ↘ Spec k) = Φ ≫ (X ↘ Spec k)`
(`Z^× → C ×_k X` is a `k`-morphism).

Proof: by `IsClosedImmersion.lift_fac`, `Φ ≫ e.emb = φ` (the projectivization), so
`Φ ≫ (X ↘ Spec k) = Φ ≫ e.emb ≫ (P^N ↘ Spec k) = φ ≫ (P^N ↘ Spec k)` (using that `e.emb` is a `k`-morphism,
a field of `ProjectiveEmbedding`). By construction `projectivizationMorphism` is a `k`-morphism on `W` (given
on each chart by a `k`-algebra homomorphism; `projectivizationMorphism_comp_over`), and its composite to
`Spec k` is the structure morphism `puncturedConeToProduct.overK` of `W`, i.e. `t ≫ (C ↘ Spec k)`.
The proof is the three steps `IsClosedImmersion.lift_fac`, `e.over`, `projectivizationMorphism_comp_over`. -/
theorem puncturedConeToProduct.base_comp {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) :
    puncturedConeToProduct.base e E A hdeg ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      puncturedConeToProduct.toX e E A hdeg ≫
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  let _ := puncturedConeToProduct.overK e E A hdeg
  have hfac : puncturedConeToProduct.toX e E A hdeg ≫ e.emb =
      projectivizationMorphism (k := k)
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (puncturedConeToProduct.base e E A hdeg)).obj A)
        (puncturedConeToProduct.coord e E A hdeg)
        (puncturedConeToProduct.coord_nowhereZero e E A hdeg) :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _
  rw [← e.over, ← CategoryTheory.Category.assoc, hfac, projectivizationMorphism_comp_over]
  rfl

end PuncturedConeToProduct

/-- The morphism `Z^× → C ×_k X`. Let `W := Z^×` and `t := W ↪ Z → C`. The morphism `W → Z ↪ Tot(A^{⊕(N+1)})`
over `C` corresponds under `totalSpaceHomEquiv` to `z ∈ Γ(W, t^*(A^{⊕(N+1)}))`; its `ℓ`-th projection is
`z_ℓ ∈ Γ(W, t^*A)`; `z` is nowhere all zero (`W` avoids the zero section), giving the projectivization
`φ := projectivizationMorphism : W → P^N`; since `F_j(z) = 0` and the `F` cut out `X`, the kernel of `φ`
contains the kernel of the closed immersion `e.emb`, and `Φ := IsClosedImmersion.lift e.emb φ : W → X`
(`Φ ≫ e.emb = φ`, Mathlib's `lift_fac`); the result is `pullback.lift t Φ`. -/
noncomputable def puncturedConeToProduct {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) :
    (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme ⟶
      CategoryTheory.Limits.pullback (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  CategoryTheory.Limits.pullback.lift
    (puncturedConeToProduct.base e E A hdeg)
    (puncturedConeToProduct.toX e E A hdeg)
    (puncturedConeToProduct.base_comp e E A hdeg)

end
