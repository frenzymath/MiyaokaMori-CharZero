import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.JetProjectivize
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.PositiveLineCoreWeightedRescalingHonestChart
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftAffineBase

/-! # The chart coordinates of the generic weighted point of a based jet

Step 6 of the proof of Lemma 3.1 of the paper ("Wherever `γ` is
nonzero, the tuple `a_α` is a weighted rescaling of `b_α`; hence the weighted projectivization of
`ȷ` agrees generically with `τ`"), separated from the construction of the jet:
**reading the fiber coordinate of a `relativeProj.lift` in an honest chart**.

For a based jet `J : C̃_(κ)(L) → 𝒵` over `ρ` with some nonzero positive-order coefficient, its
generic weighted point `J.genericWeightedPoint hne : Spec κ(η_{C̃}) → Y_κ^GG` is
`relativeProj.lift` of the data `(η^*L^∨, Ψ_m = η^*(J.weightComponent m))` (`genericLiftData`).
Given an honest jet chart `(V, chart)` of `C` with `η_C ∈ V` and a trivialization `e` of `η^*L^∨` on
`Spec κ(η_{C̃})`, the **generic chart coordinates** of `J` (`BasedJet.genericChartCoords`) are the
values of the chart coordinates `x_{i,q} = chart.coords (i,q) ∈ S_{q+1}(V)` under the local ring
homomorphism `S(V) → Γ(Spec κ(η_{C̃}), O) ≅ κ(η_{C̃})` of the lift (`liftLocalPieceAux` on the
`(q+1)`-st piece), transported to `K(C̃)` by `functionFieldIsoResidueField`. Concretely
`genericChartCoords (i,q) = e(Ψ_{q+1}(x_{i,q})|_{η})`: the section `Ψ_{q+1}(x_{i,q})` of
`(L^∨)^{⊗(q+1)}` over `ρ⁻¹V` (`weightComponent_adj_app`), restricted to the generic point and read
in the trivialization `e^{⊗(q+1)}` — the paper's `a_{i,q}(η)` in the frame `ε` inducing `e`.

The lemma `HonestJetChart.fiberCoords_genericWeightedPoint` says that the fiber coordinate of the
generic weighted point in the chart is the `K(C̃)`-point of `P(w)` of this tuple
(`weightedProjectiveSpace.pointOfTuple`, for any `k`-algebra structure on `K(C̃)` compatible with the
structure morphism of `C̃`; in `PositiveLineCoreWeightedRescaling` this is
`weightedPointOfCoords` for `SmoothProjectiveCurve.functionFieldAlgebra`). Together with
`weightedPointOfCoords_scale` (weighted rescaling by a unit of `K(C̃)` does not change the point) it
reduces `weighted_rescaling_jet_of_tuple` to the construction lemma `exists_basedJet_of_tuple`
(`PositiveLineCoreWeightedRescaling_ExistsBasedJet`), which produces `J` together with `e` and a
unit `γ` such that `genericChartCoords (i,q) = γ^{q+1} b_{i,q}`.

This module is upstream of `PositiveLineCoreWeightedRescaling` (which owns `weightedPointOfCoords`),
so the lemma is stated with `pointOfTuple` directly.

-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}

/-- The generic point of `C̃` maps into any open `V` of `C` containing the generic point of `C`:
`Spec κ(η_{C̃}) → C̃ → C` lands in `V` (`fromSpecResidueField_apply`, `FiniteCover.hom_genericPoint`).
Stated in the form `⊤ ≤ (𝟙 ≫ (η ≫ ρ)) ⁻¹ᵁ V` needed by `relativeProj.liftLocalPieceAux`. -/
theorem FiniteCover.top_le_genericBase_preimage (ρ : FiniteCover k C) {V : C.toScheme.Opens}
    (hηV : genericPoint C.toScheme ∈ V) :
    (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      (𝟙 (AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))) ≫
        (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)) ⁻¹ᵁ V := by
  intro y _
  have := ρ.source.isIntegral
  have := C.isIntegral
  show ρ.hom.base
    ((ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme)).base y) ∈ V
  rw [AlgebraicGeometry.Scheme.fromSpecResidueField_apply, ρ.hom_genericPoint]
  exact hηV

/-- Global functions on `Spec κ(η_{C̃})` read as rational functions on `C̃`:
`Γ(Spec κ(η_{C̃}), O) ≅ κ(η_{C̃}) ≅ K(C̃)` (`ΓSpecIso`, `functionFieldIsoResidueField`). A regular
definition, so that `BasedJet.genericChartCoords` is `genericBaseToFunctionField ρ (genericChartCoordsAux …)`
with no proof term in its body (see `relativeProj.liftLocalPieceAuxApply` for why this matters). -/
noncomputable def FiniteCover.genericBaseToFunctionField (ρ : FiniteCover k C)
    (y : Γ(AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)), ⊤)) :
    ρ.source.toScheme.functionField :=
  haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  ρ.source.toScheme.functionFieldIsoResidueField.inv.hom
    ((AlgebraicGeometry.Scheme.ΓSpecIso
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).hom.hom y)

/-- The generic weighted point of a based jet lies over `V` as soon as `η_C ∈ V`
(`relativeProj.lift_hom`, `fromSpecResidueField_apply`, `FiniteCover.hom_genericPoint`). -/
theorem BasedJet.genericWeightedPoint_range_subset {f : C.toScheme ⟶ X.toScheme} [MMSetup f]
    {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (hne : ∃ ℓ q, 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0) {V : C.toScheme.Opens}
    (hηV : genericPoint C.toScheme ∈ V) :
    Set.range (J.genericWeightedPoint hne ≫ YGG.proj f κ).base ⊆ V := by
  rintro _ ⟨s, rfl⟩
  have := ρ.source.isIntegral
  have := C.isIntegral
  -- the projection of the generic weighted point is `η ≫ ρ` (`relativeProj.lift_hom`; this is
  -- `BasedJet.genericWeightedPoint_proj` of `PositiveLineCoreWeightedRescaling`, downstream)
  have hproj : J.genericWeightedPoint hne ≫ YGG.proj f κ =
      ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom :=
    AlgebraicGeometry.Scheme.relativeProj.lift_hom _ _ _ _
  rw [hproj]
  show ρ.hom.base
    ((ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme)).base s) ∈ V
  rw [AlgebraicGeometry.Scheme.fromSpecResidueField_apply, ρ.hom_genericPoint]
  exact hηV

/-- **The generic chart coordinates of a based jet, before transport to `K(C̃)`.** For
`J : BasedJet f ρ L κ` with a nonzero positive-order coefficient (`hne`), an honest jet chart
`(V, chart)` with `η_C ∈ V`, and a trivialization `e` of `η^*L^∨` on `T := Spec κ(η_{C̃})`
(`η : T → C̃` the generic point; the pullback along `𝟙 T` is the form in which
`relativeProj.liftLocalPieceAux` takes a trivialization), the value of the chart coordinate
`x_p = chart.coords p ∈ S_{w p}(V)` under the local ring homomorphism of the lift
`J.genericWeightedPoint hne = relativeProj.lift (jetAlgebra f κ) (η ≫ ρ) (η^*L^∨) (J.genericLiftData hne)`
on the chart `V`, as a global function on `T`:
`genericChartCoordsAux p = liftLocalPieceAux (J.genericLiftData hne) (𝟙 T) e V _ (w p) (x_p)`
(`genericChartCoordsAux_eq` + `liftLocalPieceAuxApply_eq`, both `rfl`; the regular-head spelling
`liftLocalPieceAuxApply` keeps the kernel cost of these unfoldings small). -/
noncomputable def BasedJet.genericChartCoordsAux {f : C.toScheme ⟶ X.toScheme} [MMSetup f]
    {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (hne : ∃ ℓ q, 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0) {V : C.toScheme.Opens}
    (chart : HonestJetChart f κ V) (hηV : genericPoint C.toScheme ∈ V)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback
          (𝟙 (AlgebraicGeometry.Spec
            (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))))).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme))).obj
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)) ≅
        SheafOfModules.unit (AlgebraicGeometry.Spec
          (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).ringCatSheaf)
    (p : Fin (X.toVariety.dim + 1) × Fin κ) :
    Γ(AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)), ⊤) :=
  AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAuxApply (J.genericLiftData hne) (𝟙 _) e V
    (ρ.top_le_genericBase_preimage hηV) (jetWeights.{u} X.toVariety.dim κ ⟨p⟩) (chart.coords p)

/-- `genericChartCoordsAux` unfolded (`rfl`); `liftLocalPieceAuxApply_eq` turns the right-hand side
into `liftLocalPieceAux … (jetWeights n κ ⟨p⟩) (chart.coords p)`. -/
theorem BasedJet.genericChartCoordsAux_eq {f : C.toScheme ⟶ X.toScheme} [MMSetup f]
    {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (hne : ∃ ℓ q, 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0) {V : C.toScheme.Opens}
    (chart : HonestJetChart f κ V) (hηV : genericPoint C.toScheme ∈ V)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback
          (𝟙 (AlgebraicGeometry.Spec
            (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))))).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme))).obj
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)) ≅
        SheafOfModules.unit (AlgebraicGeometry.Spec
          (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).ringCatSheaf)
    (p : Fin (X.toVariety.dim + 1) × Fin κ) :
    J.genericChartCoordsAux hne chart hηV e p =
      AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAuxApply (J.genericLiftData hne) (𝟙 _) e V
        (ρ.top_le_genericBase_preimage hηV) (jetWeights.{u} X.toVariety.dim κ ⟨p⟩) (chart.coords p) := rfl

/-- **The generic chart coordinates of a based jet.** `genericChartCoordsAux` (the value of the chart
coordinate `x_p` under the local ring homomorphism of the lift, a global function on
`Spec κ(η_{C̃})`) read in `K(C̃)` through `Γ(Spec κ(η_{C̃}), O) ≅ κ(η_{C̃}) ≅ K(C̃)`
(`FiniteCover.genericBaseToFunctionField`):
`genericChartCoords p = functionFieldIsoResidueField⁻¹ (ΓSpecIso (liftLocalPieceAux … (w p) (x_p)))`.

Unfolded (`liftLocalPieceAux_apply`, `liftLocalHomAux`): it is `e^{⊗(w p)}` applied to
`η^*(Ψ_{w p})(x_p)` where `Ψ = J.weightComponent` (`genericLiftData_Ψ`, `precompΨ`), i.e. the
section `Ψ_{q+1}(x_{i,q})` of `(L^∨)^{⊗(q+1)}` over `ρ⁻¹V` (`BasedJet.weightComponent_adj_app`)
restricted to the generic point and read in the trivialization: the paper's normalized coefficient
`a_{i,q}` at the generic point, in the frame inducing `e` (Lemma 3.1 of the paper).

Unfold with `genericChartCoords_spec` / `genericChartCoordsAux_eq` / `liftLocalPieceAuxApply_eq`
rather than `unfold`: the two-layer definition exists so that these steps are cheap for the kernel
(see `relativeProj.liftLocalPieceAuxApply`). -/
noncomputable def BasedJet.genericChartCoords {f : C.toScheme ⟶ X.toScheme} [MMSetup f]
    {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (hne : ∃ ℓ q, 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0) {V : C.toScheme.Opens}
    (chart : HonestJetChart f κ V) (hηV : genericPoint C.toScheme ∈ V)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback
          (𝟙 (AlgebraicGeometry.Spec
            (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))))).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme))).obj
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)) ≅
        SheafOfModules.unit (AlgebraicGeometry.Spec
          (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).ringCatSheaf)
    (p : Fin (X.toVariety.dim + 1) × Fin κ) : ρ.source.toScheme.functionField :=
  ρ.genericBaseToFunctionField (J.genericChartCoordsAux hne chart hηV e p)

/-- `g.appLE ⊤ ⊤ = g.appTop` (`app_eq_appLE`; `g⁻¹ᵁ ⊤` and `⊤` are definitionally equal). -/
private theorem appLE_top_top_gc {Y Z : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ Z)
    (h : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ ⊤) : g.appLE ⊤ ⊤ h = g.appTop :=
  (AlgebraicGeometry.Scheme.Hom.app_eq_appLE g).symm

/-- `e.hom (e.inv s) = s` for an isomorphism of commutative rings, in the `.hom.hom` spelling. -/
private theorem hom_inv_hom_apply_gc {R S : CommRingCat.{u}} (e : R ≅ S) (s : S) :
    e.hom.hom (e.inv.hom s) = s := by
  have h := congrArg (fun m => m.hom s) e.inv_hom_id
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_id, RingHom.comp_apply, RingHom.id_apply] using h

/-- `e.inv (e.hom r) = r` for an isomorphism of commutative rings, in the `.hom.hom` spelling. -/
private theorem inv_hom_hom_apply_gc {R S : CommRingCat.{u}} (e : R ≅ S) (r : R) :
    e.inv.hom (e.hom.hom r) = r := by
  have h := congrArg (fun m => m.hom r) e.hom_inv_id
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_id, RingHom.comp_apply, RingHom.id_apply] using h

/-- `fromOfGlobalSections` only depends on the ring homomorphism (the irrelevant-ideal condition is a `Prop`). -/
private theorem fromOfGlobalSections_congr_gc {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : AlgebraicGeometry.Scheme.{u}}
    {φ ψ : A →+* Γ(Y, ⊤)} (h : φ = ψ) (hφ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map φ = ⊤)
    (hψ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map ψ = ⊤) :
    AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 φ hφ = AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 ψ hψ := by
  subst h; rfl

/-- `genericBaseToFunctionField` inverted: `ΓSpecIso⁻¹ (functionFieldIsoResidueField (…)) = y`. -/
theorem FiniteCover.genericBaseToFunctionField_spec (ρ : FiniteCover k C)
    (y : Γ(AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)), ⊤)) :
    haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
    (AlgebraicGeometry.Scheme.ΓSpecIso
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).inv.hom
      (ρ.source.toScheme.functionFieldIsoResidueField.hom.hom (ρ.genericBaseToFunctionField y)) = y := by
  have : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  exact (congrArg (fun w => (AlgebraicGeometry.Scheme.ΓSpecIso
      (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).inv.hom w)
    (hom_inv_hom_apply_gc ρ.source.toScheme.functionFieldIsoResidueField
      ((AlgebraicGeometry.Scheme.ΓSpecIso
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).hom.hom y))).trans
    (inv_hom_hom_apply_gc _ y)

/-- **Defining property of the generic chart coordinates**: transported back to `κ(η_{C̃})` and
`Γ(Spec κ(η_{C̃}), O)`, `genericChartCoords p` is `genericChartCoordsAux p`, the value of the chart
coordinate `x_p` under the local ring homomorphism of the lift (`liftLocalPieceAux` on the `w p`-th
piece; `genericChartCoordsAux_eq`). -/
theorem BasedJet.genericChartCoords_spec {f : C.toScheme ⟶ X.toScheme} [MMSetup f]
    {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (hne : ∃ ℓ q, 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0) {V : C.toScheme.Opens}
    (chart : HonestJetChart f κ V) (hηV : genericPoint C.toScheme ∈ V)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback
          (𝟙 (AlgebraicGeometry.Spec
            (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))))).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme))).obj
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)) ≅
        SheafOfModules.unit (AlgebraicGeometry.Spec
          (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).ringCatSheaf)
    (p : Fin (X.toVariety.dim + 1) × Fin κ) :
    haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
    (AlgebraicGeometry.Scheme.ΓSpecIso
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).inv.hom
      (ρ.source.toScheme.functionFieldIsoResidueField.hom.hom (J.genericChartCoords hne chart hηV e p)) =
    J.genericChartCoordsAux hne chart hηV e p :=
  ρ.genericBaseToFunctionField_spec (J.genericChartCoordsAux hne chart hηV e p)

/-- **Fiber coordinates of the generic weighted point in an honest chart**
(Lemma 3.1 of the paper, step 6): the fiber coordinate of
`J.genericWeightedPoint hne` in the honest chart `(V, chart)` is the `K(C̃)`-point of `P(w)` given by
the tuple `v` of generic chart coordinates `J.genericChartCoords hne chart hηV e` (for any
trivialization `e`; the point does not depend on `e`, since changing `e` rescales the tuple by a
weighted unit, cf. `weightedPointOfCoords_scale` in `PositiveLineCoreWeightedRescaling`), read
on `Spec κ(η_{C̃})` through `K(C̃) ≅ κ(η_{C̃})`. The `k`-algebra structure on `K(C̃)` is arbitrary
subject to `halg` (its `Spec` is `Spec K(C̃) → C̃ → Spec k`); `SmoothProjectiveCurve.functionFieldAlgebra`
satisfies it (`SpecMap_algebraMap_functionFieldAlgebra`), and then the right-hand side is
`weightedPointOfCoords ρ.source n κ (genericChartCoords …) _` by definition.

Natural-language proof (all objects named; `T := Spec κ(η_{C̃})`, `g := η ≫ ρ : T → C`,
`S := jetAlgebra f κ`, `M := η^*L^∨`, `D := J.genericLiftData hne`, `π := YGG.proj f κ`,
`w := jetWeights n κ`, `𝒜 := k[x_σ]` weighted by `w`, `ι_K := functionFieldIsoResidueField.hom : K(C̃) → κ(η_{C̃})`):
1. **The lift on the chart.** `T` is affine with one point and `g(T) ⊆ V` (`top_le_genericBase_preimage`),
   so the piece of `relativeProj.lift S g M D` chosen by
   `relativeProj.lift_ι_eq_liftLocal` / `relativeProj.homOfLE_liftLocal` (`RelativeProjLiftLocalPrecomp`,
   `RelativeProjLift`) with `U = V' = ⊤`, `W = V` is the whole of `T` — but stated for `⊤.ι`.
   Transport along the isomorphism `⊤.ι : ⊤.toScheme ≅ T` (`Scheme.topIso`) and change the trivialization
   from `liftLocalTrivOn …` to `e` by `relativeProj.fromOfGlobalSections_liftLocalRingHomAux_change_triv`
   (two trivializations differ by a unit `u`; `fromOfGlobalSections_unit_scale`), to get
   `J.genericWeightedPoint hne = Proj.fromOfGlobalSections (S.sectionsGrading V) Φ hΦ ≫ (affineIso S ⟨V, hV⟩).inv ≫ (π⁻¹V).ι`
   with `Φ := liftLocalRingHomAux D (𝟙 T) e V hW : S(V) →+* Γ(T, ⊤)`
   (`hΦ := liftLocalRingHomAux_map_irrelevant`, `T` affine).
2. **The fiber coordinate.** `fiberCoords x hx = IsOpenImmersion.lift (π⁻¹V).ι x _ ≫ iso.hom ≫ snd`, and
   by `IsOpenImmersion.lift_uniq` the lift of the morphism of step 1 is
   `fromOfGlobalSections Φ hΦ ≫ (affineIso S ⟨V, hV⟩).inv`. Now `(affineIso S ⟨V,hV⟩).inv = jetProjChartToPreimage f κ hV`
   (both compose with `(π⁻¹V).ι` to `projChart ⟨V, hV⟩`: `relativeProj.affineIso_hom_comp_projChart`
   (`RelativeProjEvaluation`) and the definition of `jetProjChartToPreimage`; `(π⁻¹V).ι` is a
   monomorphism). Honesty (`chart.honest`, last conjunct) gives
   `jetProjChartToPreimage ≫ iso.hom ≫ snd = Proj.map φ hφ`, so
   `fiberCoords = fromOfGlobalSections (S.sectionsGrading V) Φ hΦ ≫ Proj.map φ hφ = fromOfGlobalSections 𝒜 (Φ ∘ φ) _`
   (`AlgebraicGeometry.Proj.fromOfGlobalSections_comp_map`, `ProjFromOfGlobalSectionsCompMap`;
   `A.grading ⟨V,hV⟩ = S.sectionsGrading V` by definition of `toGradedAffineAlgebra`).
3. **The right-hand side.** `pointOfTuple k w hw K(C̃) v = fromOfGlobalSections 𝒜 (ΓSpecIso_{K(C̃)}⁻¹ ∘ aeval v)`;
   by `AlgebraicGeometry.Proj.ProjectiveTupleRestriction.fromOfGlobalSections_naturality` the right-hand side is
   `fromOfGlobalSections 𝒜 ((Spec.map ι_K).appTop ∘ ΓSpecIso_{K(C̃)}⁻¹ ∘ aeval v) = fromOfGlobalSections 𝒜 (ΓSpecIso_{κ(η)}⁻¹ ∘ ι_K ∘ aeval v)`
   (`Scheme.ΓSpecIso_inv_naturality`).
4. **Comparison of the two ring maps `𝒜 → Γ(T, ⊤)`** (`MvPolynomial.ringHom_ext`, then
   `Proj.fromOfGlobalSections_congr'`):
   * on a variable `X p`: `φ (X p) = ε⁻¹ (X p) = ε⁻¹ (ε (ofPiece V (w p) (coords p))) = ofPiece V (w p) (coords p)`
     (honesty: `φ x = ε⁻¹ (map x)` and `ε (ofPiece (coords p)) = X p`; `MvPolynomial.map_X`), so
     `Φ (φ (X p)) = liftLocalPieceAux D (𝟙 T) e V hW (w p) (coords p)` (`ofPiece = DirectSum.of`,
     `liftLocalRingHomAux_of`) `= ΓSpecIso⁻¹ (ι_K (genericChartCoords p.down))` (definition of `genericChartCoords`,
     `Iso.inv_hom_id_apply` twice) `= ΓSpecIso⁻¹ (ι_K (v p))` (`hv`), which is the right-hand side on `X p` (`aeval_X`);
   * on a constant `C r`: `φ (C r) = ε⁻¹ (C (opensAlgebraMap V r)) = sectionsUnitHom V (opensAlgebraMap V r)`
     (honesty: `ε (sectionsUnitHom r) = C r`), so `Φ (φ (C r)) = (𝟙 ≫ g).appLE V ⊤ hW (opensAlgebraMap V r)`
     (`liftLocalRingHomAux_sectionsUnit`) — the function `r` on `Spec k` pulled back along `T → C̃ → C → Spec k`;
     the right-hand side is `ΓSpecIso⁻¹ (ι_K (algebraMap k K(C̃) r))` (`aeval_C`), i.e. `r` pulled back along
     `T → Spec K(C̃) → C̃ → Spec k` (`halg`, `SpecMap_functionFieldIsoResidueField_inv_fromSpecResidueField`);
     the two agree because `ρ` is a `k`-morphism (`FiniteCover.isOver`) and both are `appTop` of the same morphism
     `T → Spec k` composed with `ΓSpecIso`. ∎

Estimated 250–400 lines, medium–hard (plumbing: `appLE`/`appTop` transport, `⊤.ι` versus `𝟙`,
the change of trivialization). Edge cases: `κ = 0` — `hne` is then impossible (`1 ≤ q ≤ 0`), vacuous;
`n = 0` fine. The nonzeroness of `v` is part of the data (the tuple is in fact nonzero: `Φ` maps the
irrelevant ideal of `S(V)` onto `Γ(T, ⊤) ≠ 0`, and `S(V)_+` is generated by the `coords`); the user
derives it from `exists_basedJet_of_tuple`. -/
theorem HonestJetChart.fiberCoords_genericWeightedPoint {f : C.toScheme ⟶ X.toScheme} [MMSetup f]
    {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (hne : ∃ ℓ q, 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0) {V : C.toScheme.Opens}
    (chart : HonestJetChart f κ V) (hηV : genericPoint C.toScheme ∈ V)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback
          (𝟙 (AlgebraicGeometry.Spec
            (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))))).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme))).obj
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)) ≅
        SheafOfModules.unit (AlgebraicGeometry.Spec
          (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).ringCatSheaf)
    [Algebra k ρ.source.toScheme.functionField]
    (halg : AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k ρ.source.toScheme.functionField)) =
      ρ.source.toScheme.fromSpecStalk (genericPoint ρ.source.toScheme) ≫
        (ρ.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (v : {v : ULift.{u} (Fin (X.toVariety.dim + 1) × Fin κ) → ρ.source.toScheme.functionField // v ≠ 0})
    (hv : ∀ p, (v : ULift.{u} (Fin (X.toVariety.dim + 1) × Fin κ) → ρ.source.toScheme.functionField) p =
      J.genericChartCoords hne chart hηV e p.down) :
    chart.fiberCoords (J.genericWeightedPoint hne) (J.genericWeightedPoint_range_subset hne hηV) =
      (haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral;
        AlgebraicGeometry.Spec.map ρ.source.toScheme.functionFieldIsoResidueField.hom) ≫
        weightedProjectiveSpace.pointOfTuple k (jetWeights.{u} X.toVariety.dim κ) (jetWeights_pos _ _)
          ρ.source.toScheme.functionField v := by
  have : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  have : AlgebraicGeometry.IsIntegral C.toScheme := C.isIntegral
  classical
  let _ := MvPolynomial.weightedGradedAlgebra (R := k) (jetWeights.{u} X.toVariety.dim κ)
  have hV := chart.isAffineOpen
  obtain ⟨ε, φ, hφ, -, hC, hX, hφdef, hiso⟩ := chart.honest
  have hW := ρ.top_le_genericBase_preimage hηV
  -- Step 1: the lift on the chart is a single `fromOfGlobalSections` piece
  have h1 : J.genericWeightedPoint hne =
      AlgebraicGeometry.Proj.fromOfGlobalSections ((jetAlgebra f κ).sectionsGrading V)
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux (J.genericLiftData hne)
          (𝟙 _) e V hW)
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_map_irrelevant
          (J.genericLiftData hne) (𝟙 _) e ⟨V, hV⟩ hW) ≫
      (AlgebraicGeometry.Scheme.relativeProj.affineIso (jetAlgebra f κ) ⟨V, hV⟩).inv ≫
        ((YGG.proj f κ) ⁻¹ᵁ V).ι :=
    AlgebraicGeometry.Scheme.relativeProj.lift_eq_fromOfGlobalSections_of_isAffine (jetAlgebra f κ)
      _ _ (J.genericLiftData hne) e ⟨V, hV⟩ hW
  -- Step 2: `affineIso.inv = jetProjChartToPreimage`, and the lift through `π⁻¹V ↪ Y`
  have hl : (AlgebraicGeometry.Proj.fromOfGlobalSections ((jetAlgebra f κ).sectionsGrading V)
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux (J.genericLiftData hne)
          (𝟙 _) e V hW)
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_map_irrelevant
          (J.genericLiftData hne) (𝟙 _) e ⟨V, hV⟩ hW) ≫ jetProjChartToPreimage f κ hV) ≫
        ((YGG.proj f κ) ⁻¹ᵁ V).ι = J.genericWeightedPoint hne := by
    rw [h1]
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (fun m => AlgebraicGeometry.Proj.fromOfGlobalSections ((jetAlgebra f κ).sectionsGrading V)
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux (J.genericLiftData hne)
          (𝟙 _) e V hW)
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_map_irrelevant
          (J.genericLiftData hne) (𝟙 _) e ⟨V, hV⟩ hW) ≫ m)
      ((jetProjChartToPreimage_ι f κ hV).trans
        (AlgebraicGeometry.Scheme.relativeProj.affineIso_inv_ι (jetAlgebra f κ) ⟨V, hV⟩).symm)
  have hiso' : jetProjChartToPreimage f κ hV ≫ chart.iso.hom ≫ CategoryTheory.Limits.pullback.snd _ _ =
      AlgebraicGeometry.Proj.map φ hφ := hiso
  have hl2 : AlgebraicGeometry.IsOpenImmersion.lift ((YGG.proj f κ) ⁻¹ᵁ V).ι (J.genericWeightedPoint hne)
      (by
        rw [AlgebraicGeometry.Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact J.genericWeightedPoint_range_subset hne hηV ⟨y, rfl⟩) =
      AlgebraicGeometry.Proj.fromOfGlobalSections ((jetAlgebra f κ).sectionsGrading V)
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux (J.genericLiftData hne)
          (𝟙 _) e V hW)
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_map_irrelevant
          (J.genericLiftData hne) (𝟙 _) e ⟨V, hV⟩ hW) ≫ jetProjChartToPreimage f κ hV :=
    (AlgebraicGeometry.IsOpenImmersion.lift_uniq _ _ _ _ hl).symm
  show chart.tojetChart.fiberCoords _ _ = _
  unfold jetChart.fiberCoords
  refine (congrArg (fun m => m ≫ chart.iso.hom ≫ CategoryTheory.Limits.pullback.snd _ _) hl2).trans ?_
  set Φ := AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux (J.genericLiftData hne)
          (𝟙 _) e V hW
    with hΦ
  set hΦirr := AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_map_irrelevant
    (J.genericLiftData hne) (𝟙 _) e ⟨V, hV⟩ hW
  set A := AlgebraicGeometry.Proj.fromOfGlobalSections ((jetAlgebra f κ).sectionsGrading V) Φ hΦirr with hA
  -- Step 3: `A ≫ Proj.map φ = fromOfGlobalSections 𝒜 (Φ ∘ φ)`
  have h3 : A ≫ AlgebraicGeometry.Proj.map φ hφ =
      AlgebraicGeometry.Proj.fromOfGlobalSections
        (MvPolynomial.weightedHomogeneousSubmodule k (jetWeights.{u} X.toVariety.dim κ))
        (Φ.comp φ.toRingHom)
        (AlgebraicGeometry.Proj.irrelevant_map_comp_eq_top_of_map_eq_top _ _ φ hφ Φ hΦirr) :=
    AlgebraicGeometry.Proj.fromOfGlobalSections_comp_map _ _ φ hφ Φ hΦirr
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun m => A ≫ m) hiso').trans ?_
  refine h3.trans ?_
  -- Step 4: the right-hand side as a single `fromOfGlobalSections`
  unfold weightedProjectiveSpace.pointOfTuple
  refine Eq.trans ?_ (AlgebraicGeometry.Proj.ProjectiveTupleRestriction.fromOfGlobalSections_naturality _ _ _ _).symm
  refine fromOfGlobalSections_congr_gc _ ?_ _ _
  -- Step 5: the two ring homomorphisms `k[x] → Γ(Spec κ(η), O)` agree on generators
  have hφX : ∀ p : Fin (X.toVariety.dim + 1) × Fin κ,
      φ (MvPolynomial.X ⟨p⟩) =
        (jetAlgebra f κ).ofPiece V (jetWeights.{u} X.toVariety.dim κ ⟨p⟩) (chart.coords p) := by
    intro p
    rw [hφdef, MvPolynomial.map_X, ← hX p, RingEquiv.symm_apply_apply]
  have hφC : ∀ r : k, φ (MvPolynomial.C r) =
      (jetAlgebra f κ).sectionsUnitHom V (C.opensAlgebraMap V r) := by
    intro r
    rw [hφdef, MvPolynomial.map_C, ← hC, RingEquiv.symm_apply_apply]
  -- (the `CommRing` instance on `K(C̃)` is spelled `Field.toCommRing`, as inside `pointOfTuple`;
  -- with the instance inferred afresh the unifier spends ~30 s on `F.str ≟ Field.toCommRing`)
  have hnat' : ∀ x : ρ.source.toScheme.functionField,
      (AlgebraicGeometry.Spec.map ρ.source.toScheme.functionFieldIsoResidueField.hom).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso
          (@CommRingCat.of ρ.source.toScheme.functionField Field.toCommRing)).inv.hom x) =
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).inv.hom
        (ρ.source.toScheme.functionFieldIsoResidueField.hom.hom x) := fun x =>
    (congrArg (fun ψ => ψ.hom x)
      (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality
        ρ.source.toScheme.functionFieldIsoResidueField.hom)).symm
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
  · -- constants
    show Φ (φ (MvPolynomial.C r)) = (AlgebraicGeometry.Spec.map
        ρ.source.toScheme.functionFieldIsoResidueField.hom).appTop.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of ρ.source.toScheme.functionField)).inv.hom
        (MvPolynomial.aeval (v : ULift.{u} (Fin (X.toVariety.dim + 1) × Fin κ) →
          ρ.source.toScheme.functionField) (MvPolynomial.C r)))
    rw [hφC r, MvPolynomial.aeval_C]
    -- left: the structure map, `liftLocalRingHomAux_sectionsUnit`
    refine (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_sectionsUnit (J.genericLiftData hne)
      (𝟙 _) e V hW (C.opensAlgebraMap V r)).trans ?_
    -- right: `ΓSpecIso_inv_naturality` for the algebra map, then `halg`
    have hnat := congrArg (fun m => m.hom r)
      (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (algebraMap k ρ.source.toScheme.functionField)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
    rw [hnat, halg]
    have hmor : AlgebraicGeometry.Spec.map ρ.source.toScheme.functionFieldIsoResidueField.hom ≫
        ρ.source.toScheme.fromSpecStalk (genericPoint ρ.source.toScheme) ≫
          (ρ.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
        (𝟙 _ ≫ (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)) ≫
          (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
      rw [Category.id_comp, Category.assoc, ρ.isOver, ← Category.assoc]
      rfl
    have hcomp := congrArg (fun m => m.appTop.hom ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r))
      hmor
    -- left: `appLE_comp_appLE` and `appLE ⊤ ⊤ = appTop`
    have hLE := congrArg (fun m => m.hom ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r))
      (AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE
        (𝟙 _ ≫ (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom))
        (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ⊤ V ⊤ le_top hW)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hLE
    refine hLE.trans ?_
    rw [appLE_top_top_gc]
    exact hcomp.symm
  · -- variables
    obtain ⟨p⟩ := p
    show Φ (φ (MvPolynomial.X ⟨p⟩)) = (AlgebraicGeometry.Spec.map
        ρ.source.toScheme.functionFieldIsoResidueField.hom).appTop.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso
          (@CommRingCat.of ρ.source.toScheme.functionField Field.toCommRing)).inv.hom
        (MvPolynomial.aeval (v : ULift.{u} (Fin (X.toVariety.dim + 1) × Fin κ) →
          ρ.source.toScheme.functionField) (MvPolynomial.X ⟨p⟩)))
    rw [hφX p, MvPolynomial.aeval_X, hv ⟨p⟩]
    refine (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_of' (J.genericLiftData hne)
      (𝟙 _) e V hW _ _).trans ?_
    rw [hnat']
    exact (J.genericChartCoords_spec hne chart hηV e p).symm

/-- A section that is zero is zero at every point (the germ of `0` is `0 ∈ 𝔪 • M_x`). -/
private theorem isZeroAt_zero_aux {Y : AlgebraicGeometry.Scheme.{u}} {M : Y.Modules} (y : Y) :
    IsZeroAt (0 : (M.val.obj (Opposite.op ⊤) : Type u)) y := by
  change M.presheaf.germ ⊤ y trivial 0 ∈ _
  rw [map_zero]
  exact Submodule.zero_mem _

/-- A based jet with nowhere-zero normalized tuple has some nonzero positive-order coefficient
(take the point `η_{C̃}`: a coefficient that does not vanish there is not the zero section). -/
theorem NormalizedTupleNowhereZero.exists_coefficient_ne_zero {f : C.toScheme ⟶ X.toScheme}
    [MMSetup f] {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {κ : ℕ}
    {J : BasedJet f ρ L κ} (hnz : NormalizedTupleNowhereZero J) :
    ∃ ℓ q, 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0 := by
  obtain ⟨ℓ, q, h1, h2, h⟩ := hnz (genericPoint ρ.source.toScheme)
  refine ⟨ℓ, q, h1, h2, fun h0 => h ?_⟩
  rw [h0]
  exact isZeroAt_zero_aux _

end
