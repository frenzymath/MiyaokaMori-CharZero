import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLift
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01nq
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback

/-! # `relativeProj.lift` on a piece adapted to a given affine chart

**Statement** (`exists_piece_chart`): let `S` be a graded quasi-coherent algebra on `X`, `f : T ⟶ X`, `M` a line
bundle on `T`, `D` lift data, `r := relativeProj.lift S f M D : T ⟶ Proj_X S`. For every **affine open `V ⊆ X`** and
every `t ∈ f⁻¹V` there is an affine open `V₃ ∋ t` of `T` with `V₃ ⊆ f⁻¹V`, and a trivialization
`et : (V₃ ↪ T)^*M ≅ O_{V₃}`, such that
`V₃.ι ≫ r = Proj.fromOfGlobalSections (A(V)) Φ ≫ chartHom S V`, where `A(V) = Γ(V, S)` is the section ring,
`Φ = liftLocalRingHomAux D V₃.ι et V : A(V) → Γ(V₃, O)` the local ring map of Stacks 01O4, and
`chartHom S V := affineIso⁻¹ ≫ ι : Proj A(V) ≅ π⁻¹V ↪ Proj_X S` the chart of Stacks 01NQ.

The point: the pieces used in the *definition* of `lift` come with affine opens `W ∋ f(t)` chosen by `choose`; here
the chart `V` is **prescribed**. This is the "chart change" needed by Stacks 07RM paragraph 5
and it follows from the compatibility lemmas of `RelativeProjLift.lean`.

**Proof.**
1. `exists_lift_restrict` (same script as the definition of `lift`; `Cover.ι_glueMorphisms`): `t` lies in a piece
   `V' ∋ t` (affine, `V' ≤ U ⊓ f⁻¹W`, `W` affine) with `V'.ι ≫ r = liftLocal S f M D U e W V' hV' hle`.
2. Choose an affine `W₃ ∋ f(t)` inside `W ⊓ V`, then an affine `V₃ ∋ t` inside `V' ⊓ f⁻¹W₃`
   (`exists_isAffineOpen_mem_and_subset`).
3. `V₃.ι ≫ r = homOfLE ≫ V'.ι ≫ r = homOfLE ≫ liftLocal = fromOfGlobalSections (Aux D V₃.ι et W) ≫ affineIso_W⁻¹ ≫ ι_W`
   (`homOfLE_liftLocal`), with `et := liftLocalTrivOn`.
4. Change the chart `W ↝ W₃` and then `W₃ ↝ V` with `liftLocalPiece_change_W` (`liftLocalRingHomAux_restrict`
   + `Proj.fromOfGlobalSections_comp_map` + `affineIso_restrict` of 01NQ), read once forwards and once backwards. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-- **The chart `Proj A(V) ≅ π⁻¹V ↪ Proj_X S`** of Stacks 01NQ over an affine open `V ⊆ X`
(`affineIso⁻¹` followed by the inclusion; equal to `projChart`, `affineIso_inv_ι`). -/
def chartHom (S : X.GradedQCAlgebra) (V : X.affineOpens) :
    AlgebraicGeometry.Proj (S.sectionsGrading V.1) ⟶ (AlgebraicGeometry.Scheme.relativeProj S).left :=
  (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).inv ≫
    ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι

theorem isOpenImmersion_chartHom (S : X.GradedQCAlgebra) (V : X.affineOpens) :
    AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Scheme.relativeProj.chartHom S V) := by
  unfold chartHom
  infer_instance

/-- The chart lands in `π⁻¹V`. -/
theorem opensRange_chartHom (S : X.GradedQCAlgebra) (V : X.affineOpens) :
    haveI := AlgebraicGeometry.Scheme.relativeProj.isOpenImmersion_chartHom S V
    (AlgebraicGeometry.Scheme.relativeProj.chartHom S V).opensRange =
      (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1 := by
  unfold chartHom
  rw [AlgebraicGeometry.Scheme.Hom.opensRange_comp_of_isIso, AlgebraicGeometry.Scheme.Opens.opensRange_ι]

/-- **`lift` agrees with the piece chosen in its definition** (copy of `exists_lift_restrict`,
`RelativeProjLiftEvaluationTwistFamily.lean`, kept here to avoid importing that module's closure): for every `t : T` there are an open `U ∋ t` trivializing `M`, an affine open `W ∋ f t`, and an affine open
`V' ∋ t` with `V' ≤ U ⊓ f⁻¹W`, such that `V'.ι ≫ lift S f M D = liftLocal S f M D U e W V' hV' hle`
(`Cover.ι_glueMorphisms`). -/
theorem exists_lift_restrict' (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (t : T) :
    ∃ (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
      (W : X.affineOpens) (V' : T.Opens) (hV' : AlgebraicGeometry.IsAffineOpen V')
      (hle : V' ≤ U ⊓ f ⁻¹ᵁ W.1),
      t ∈ V' ∧
        V'.ι ≫ AlgebraicGeometry.Scheme.relativeProj.lift S f M D =
          AlgebraicGeometry.Scheme.relativeProj.liftLocal S f M D U e W V' hV' hle := by
  let hU := fun t : T => SheafOfModules.IsLineBundle.locally_trivial (M := M) t
  let U : T → T.Opens := fun t => (hU t).choose
  let e : ∀ t, M.restrict (U t).ι ≅ SheafOfModules.unit (U t).toScheme.ringCatSheaf :=
    fun t => (hU t).choose_spec.snd.some
  let hW := fun t : T =>
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := f.base t) (U := ⊤) trivial
  let W : T → X.affineOpens := fun t => ⟨(hW t).choose, (hW t).choose_spec.1⟩
  let hA := fun t : T =>
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := t) (U := U t ⊓ f ⁻¹ᵁ (W t).1)
      ⟨(hU t).choose_spec.fst, (hW t).choose_spec.2.1⟩
  let Vt : T → T.Opens := fun t => (hA t).choose
  have hVt : ∀ t, AlgebraicGeometry.IsAffineOpen (Vt t) := fun t => (hA t).choose_spec.1
  have hle : ∀ t, Vt t ≤ U t ⊓ f ⁻¹ᵁ (W t).1 := fun t => (hA t).choose_spec.2.2
  have hcov : TopologicalSpace.IsOpenCover Vt := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro t _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨t, (hA t).choose_spec.2.1⟩
  refine ⟨U t, e t, W t, Vt t, hVt t, hle t, (hA t).choose_spec.2.1, ?_⟩
  exact (T.openCoverOfIsOpenCover Vt hcov).ι_glueMorphisms
    (fun t => AlgebraicGeometry.Scheme.relativeProj.liftLocal S f M D (U t) (e t) (W t) (Vt t) (hVt t) (hle t))
    (fun s t => AlgebraicGeometry.Scheme.relativeProj.liftLocal_compat S f M D
      (U s) (e s) (W s) (Vt s) (hVt s) (hle s) (U t) (e t) (W t) (Vt t) (hVt t) (hle t)) t

/-- **`lift` on a piece adapted to a prescribed affine chart `V`** (Stacks 01O4 / 01NQ): for `t ∈ f⁻¹V` there is an
affine `V₃ ∋ t`, `V₃ ⊆ f⁻¹V`, and a trivialization `et` of `M` on `V₃` with
`V₃.ι ≫ lift = fromOfGlobalSections (Aux D V₃.ι et V) ≫ chartHom S V`. -/
theorem exists_piece_chart (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (V : X.affineOpens) (t : T)
    (ht : f.base t ∈ V.1) :
    ∃ (V₃ : T.Opens) (hV₃ : AlgebraicGeometry.IsAffineOpen V₃)
      (et : (AlgebraicGeometry.Scheme.Modules.pullback V₃.ι).obj M ≅ SheafOfModules.unit V₃.toScheme.ringCatSheaf)
      (hW : (⊤ : V₃.toScheme.Opens) ≤ (V₃.ι ≫ f) ⁻¹ᵁ V.1),
      t ∈ V₃ ∧
        V₃.ι ≫ AlgebraicGeometry.Scheme.relativeProj.lift S f M D =
          AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading V.1)
              (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D V₃.ι et V.1 hW)
              (haveI : AlgebraicGeometry.IsAffine V₃.toScheme := hV₃
               AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_map_irrelevant D V₃.ι et V hW) ≫
            AlgebraicGeometry.Scheme.relativeProj.chartHom S V := by
  obtain ⟨U, e, W, V', hV', hle, htV', hr⟩ :=
    AlgebraicGeometry.Scheme.relativeProj.exists_lift_restrict' S f M D t
  obtain ⟨W₃, hW₃aff, hW₃mem, hW₃sub⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := f.base t) (U := W.1 ⊓ V.1) ⟨(hle htV').2, ht⟩
  obtain ⟨V₃, hV₃aff, hV₃mem, hV₃sub⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := t) (U := V' ⊓ f ⁻¹ᵁ W₃) ⟨htV', hW₃mem⟩
  have h₃ : V₃ ≤ V' := fun _ hx => (hV₃sub hx).1
  have hV₃W₃ : V₃ ≤ f ⁻¹ᵁ W₃ := fun _ hx => (hV₃sub hx).2
  have hW₃W : W₃ ≤ W.1 := fun _ hx => (hW₃sub hx).1
  have hW₃V : W₃ ≤ V.1 := fun _ hx => (hW₃sub hx).2
  have hV₃V : V₃ ≤ f ⁻¹ᵁ V.1 := hV₃W₃.trans (f.preimage_mono hW₃V)
  refine ⟨V₃, hV₃aff, AlgebraicGeometry.Scheme.relativeProj.liftLocalTrivOn f M U e W.1 (h₃.trans hle),
    AlgebraicGeometry.Scheme.relativeProj.top_le_ι_comp_preimage f hV₃V, hV₃mem, ?_⟩
  conv_lhs => rw [← AlgebraicGeometry.Scheme.homOfLE_ι T h₃, Category.assoc, hr]
  rw [AlgebraicGeometry.Scheme.relativeProj.homOfLE_liftLocal S f M D U e W V' hV' hle hV₃aff h₃,
    AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece_change_W S f M D hV₃aff _ W ⟨W₃, hW₃aff⟩ hW₃W _
      (AlgebraicGeometry.Scheme.relativeProj.top_le_ι_comp_preimage f hV₃W₃),
    ← AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece_change_W S f M D hV₃aff _ V ⟨W₃, hW₃aff⟩ hW₃V
      (AlgebraicGeometry.Scheme.relativeProj.top_le_ι_comp_preimage f hV₃V)
      (AlgebraicGeometry.Scheme.relativeProj.top_le_ι_comp_preimage f hV₃W₃)]
  rfl

end AlgebraicGeometry.Scheme.relativeProj

end
