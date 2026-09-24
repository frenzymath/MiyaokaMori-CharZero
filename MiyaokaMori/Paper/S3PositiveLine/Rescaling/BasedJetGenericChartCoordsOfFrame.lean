import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.FramePullbackTrivialization
import MiyaokaMori.AlgebraicGeometry.Morphisms.ResidueFieldSectionsGerm
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.BasedJetPrecompLiftDataInFrame
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.BasedJetGenericChartCoordsEq

/-! # Generic chart coordinates of a based jet read in a local frame

`BasedJet.genericChartCoords` (`BasedJetGenericChartCoords`) reads the
chart coordinate `x_p` of a based jet `J` at the generic point of `C̃` through a trivialization `e` of
`η^*L^∨` on `Spec κ(η_{C̃})`. This module states the way this number is actually computed in the paper
(Lemma 3.1 of the paper, "In a local frame `ε` of `L`, write … `a_{i,q} = γ^{-q} b_{i,q}`"): if on an
open `U ∋ η_{C̃}` with a frame `μ` of `L^{-1}` the section `Ψ_{w p}(x_p)` of `(L^∨)^{⊗ w p}` is
`r · μ^{⊗ w p}` with `r ∈ O(U)`, then for the trivialization `e` induced by `μ` the generic chart
coordinate is the germ of `r` in `K(C̃)`. It is the interface between the construction of `J`
(which knows its coefficients only in local frames) and `genericChartCoords` (which is what
`HonestJetChart.fiberCoords_genericWeightedPoint` consumes).

-/
set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}

/-- **Generic chart coordinates read in a frame** (Lemma 3.1 of the paper; definition of
`BasedJet.genericChartCoords`). Let `J : BasedJet f ρ L κ` have a nonzero positive-order coefficient
(`hne`), let `(V, chart)` be an honest jet chart of `C` with `η_C ∈ V`, let `U ⊆ ρ⁻¹V` be an open of
`C̃` containing its generic point `η := η_{C̃}`, and let `μ ∈ Γ(U, L^{-1})` be a frame
(`Modules.IsFrame`; `L^{-1} = L.zpow (-1) ≅ L^∨` by `L.zpowNegOneIso`). Then there is a
trivialization `e` of `η^*L^∨` on `Spec κ(η)` (in the form `relativeProj.liftLocalPieceAux` takes it,
pulled back along `𝟙`) such that, for every chart coordinate `x_p = chart.coords p` (weight
`w p = jetWeights ⟨p⟩ = q + 1` for `p = (i, q)`) and every `r ∈ O(U)` with
`Ψ_{w p}(x_p)|_U = r • μ^{⊗ w p}` — here `Ψ_{w p}(x_p) ∈ Γ(ρ⁻¹V, (L^∨)^{⊗ w p})` is the section given
by `J.weightComponent (w p)` transposed along the pullback–pushforward adjunction
(`BasedJet.weightComponent_adj_app`), and `μ^{⊗ w p} = (pieceIso L (w p)) (framePow L U μ (w p))`
is the tensor power of `μ` (`truncatedJetAlgebra.framePow`, `JetChartTrivialization_Basis`)
carried to `monoidalPow L^∨ (w p)` by `truncatedJetAlgebra.pieceIso` — the generic chart
coordinate `J.genericChartCoords hne chart hηV e p` is the germ of `r` at `η`, i.e.
`germToFunctionField U r ∈ K(C̃)`. In the paper's words: `a_{i,q}(η)` is the coordinate.

Natural-language proof (notation `T := Spec κ(η)`, `η : T → C̃` the canonical morphism
`fromSpecResidueField`, `g := η ≫ ρ`, `D := J.genericLiftData hne`, `m := w p`,
`Mη := η^*L^∨`, `S := jetAlgebra f κ`):
1. **The trivialization.** `δ := L.zpowNegOneIso.hom.app U μ ∈ Γ(U, L^∨)` is a frame of `L^∨` on `U`
   (`IsFrame.map_iso`). `η` factors through `U` (`fromSpecResidueField_apply`: the image of `T` is
   `{η}` and `η ∈ U`), so `η^*δ ∈ Γ(T, Mη)` is a frame of `Mη` (the pullback of a frame is a frame:
   `Modules.pullback` of the trivialization `IsFrame.trivialization` of `L^∨|_U` is a trivialization of
   `Mη`, and `η^*δ` is the image of `1`). On the one-point scheme `T` a frame is a global
   trivialization: `e₀ : Mη ≅ O_T` with `e₀(η^*δ) = 1` (`IsFrame.trivialization` on `⊤`,
   `restrict_top`/`topTrivialization`, `LineCartierPresentationOfFrames.frameIso`). Put
   `e := (pullback (𝟙 T)).mapIso e₀ ≪≫ pullbackUnitIso (𝟙 T)` (or `pullbackId` iso; only `e(𝟙^*η^*δ) = 1`
   is used).
2. **Unfolding `genericChartCoords`.** By definition and `liftLocalPieceAux_apply`,
   `genericChartCoords p = ι_K⁻¹ (ΓSpecIso (Φ_m (res (unit_g (x_p)))))` with
   `Φ_m := liftLocalHomAux D (𝟙 T) e m = pullbackComp.inv ≫ (𝟙 T)^*(D.Ψ m) ≫ pullbackMonoidalPow ≫
   monoidalPowMap e.hom m ≫ unitPowCollapse T m` and `D.Ψ m = precompΨ η J.weightComponent m =
   pullbackComp.inv ≫ η^*(J.weightComponent m) ≫ pullbackMonoidalPow η L^∨ m` (`genericLiftData`,
   `precompLiftData`, `precompΨ`; `ι_K := functionFieldIsoResidueField.hom`).
3. **Naturality of the adjunction unit under pullback.** The element `res (unit_g (x_p)) ∈ Γ(T, g^*S_m)`
   is the pullback of the section `x_p ∈ Γ(V, S_m)` to `T`; `(𝟙 T)^*(η^*(J.weightComponent m))` applied
   to it is the pullback along `η` of `Ψ_m(x_p) := (homEquiv (J.weightComponent m)).app V (x_p) ∈
   Γ(ρ⁻¹V, (L^∨)^{⊗m})` (`Adjunction.homEquiv_unit`, the unit of `pullback ρ ⊣ pushforward ρ` on
   sections, then `pullbackComp` compatibility of units — `Modules.pullbackComp_unit` /
   `app_top_map_unit_app_eq` of `ProjectiveBundleUniversalProperty`). Restricting from `ρ⁻¹V` to
   `U` first does not change the pullback to `T` (the unit is natural in the open, `η(T) ⊆ U`).
4. **The hypothesis.** By `hΨ`, `Ψ_m(x_p)|_U = r • μ^{⊗m}`. Pullback of sections along `η` is
   `O`-linear for the ring map `η^♯ : O(U) → κ(η)` (`germ` followed by `residue`), and
   `pullbackMonoidalPow η L^∨ m` carries `η^*(μ^{⊗m})` to `(η^*δ)^{⊗m}` (`pullbackMonoidalPow` is
   built from `pullbackTensorObjHom`, which on sections is `η^*a ⊗ η^*b` —
   `pullbackTensorObjHom_tensorSections`; induction on `m` along `framePow_succ` and the definition of
   `pieceIso` as `tensorIso (pieceIso q) zpowNegOneIso`). Hence step 2 evaluates to
   `η^♯(r) · unitPowCollapse (monoidalPowMap e (η^*δ)^{⊗m}) = η^♯(r) · unitPowCollapse (1^{⊗m}) = η^♯(r)`
   (`monoidalPowMap` on tensor powers of sections is the tensor power of the values —
   `monoidalPowMap_tensorSections`; `unitPowCollapse_one_pow`: `1 ⊗ ⋯ ⊗ 1 ↦ 1`; step 1 for
   `e(η^*δ) = 1`). The `𝟙^*` layers are identities on sections up to `pullbackComp`/`pullbackUnitIso`
   which cancel (`liftLocalHomAux_zero` style bookkeeping, `Modules.pullbackId`).
5. **Back to `K(C̃)`.** `ΓSpecIso_{κ(η)} (η^♯ r) = residue (germ_η r)`
   (`fromSpecResidueField` is `Spec.map (residue) ≫ fromSpecStalk`, and `fromSpecStalk` on global
   sections is the germ: `Scheme.fromSpecStalk_appTop` / `germ_fromSpecStalk`), and
   `functionFieldIsoResidueField = asIso (residue η)`, so `ι_K⁻¹ (residue (germ_η r)) = germ_η r =
   germToFunctionField U r`. ∎

Auxiliary facts used (all routine):
`monoidalPowMap_tensorSections` / `unitPowCollapse` on `1^{⊗m}`, `pullbackMonoidalPow` on tensor
powers of sections, the compatibility of the adjunction unit with `pullbackComp` on sections (partly
in `ProjectiveBundleUniversalProperty`: `app_top_map_unit_app_eq`), and the frame-to-trivialization
step on `Spec` of a field. Estimated 300–450 lines, hard (plumbing of `pullback`/`pushforward`
sections; see `HonestJetChart.fiberCoords_genericWeightedPoint` for the parallel computation).

Edge cases: `κ = 0` — `hne` is impossible (`1 ≤ q ≤ 0`), vacuous. `n = 0` fine. `r = 0` is allowed
(then `Ψ_m(x_p)|_U = 0` and the coordinate is `0`). The equation `hΨ` is in `Γ(U, (L^∨)^{⊗m})` with
its `O(U)`-module structure; `hUV` is used to restrict from `ρ⁻¹V` to `U`. -/
theorem BasedJet.exists_genericTrivialization_of_frame {f : C.toScheme ⟶ X.toScheme} [MMSetup f]
    {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (hne : ∃ ℓ q, 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0) {V : C.toScheme.Opens}
    (chart : HonestJetChart f κ V) (hηV : genericPoint C.toScheme ∈ V)
    {U : ρ.source.toScheme.Opens} (hηU : genericPoint ρ.source.toScheme ∈ U)
    (hUV : U ≤ ρ.hom ⁻¹ᵁ V)
    (μ : Γ((L.zpow (-1)).toModules, U))
    (hμ : AlgebraicGeometry.Scheme.Modules.IsFrame (L.zpow (-1)).toModules U μ) :
    ∃ e : (AlgebraicGeometry.Scheme.Modules.pullback
          (𝟙 (AlgebraicGeometry.Spec
            (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))))).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme))).obj
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)) ≅
        SheafOfModules.unit (AlgebraicGeometry.Spec
          (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).ringCatSheaf,
      ∀ (p : Fin (X.toVariety.dim + 1) × Fin κ) (r : Γ(ρ.source.toScheme, U)),
        (show Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
            (jetWeights.{u} X.toVariety.dim κ ⟨p⟩), U) from
          ((AlgebraicGeometry.Scheme.Modules.monoidalPow
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
            (jetWeights.{u} X.toVariety.dim κ ⟨p⟩)).val.map (CategoryTheory.homOfLE hUV).op).hom
          (((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).homEquiv _ _)
            (J.weightComponent (jetWeights.{u} X.toVariety.dim κ ⟨p⟩))).val.app
              (Opposite.op V)).hom (chart.coords p))) =
          r • (show Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
            (jetWeights.{u} X.toVariety.dim κ ⟨p⟩), U) from
            (((truncatedJetAlgebra.pieceIso L (jetWeights.{u} X.toVariety.dim κ ⟨p⟩)).hom.val.app
              (Opposite.op U)).hom
              (truncatedJetAlgebra.framePow L U μ (jetWeights.{u} X.toVariety.dim κ ⟨p⟩)))) →
        J.genericChartCoords hne chart hηV e p =
          (by
            haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
            haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
            exact (ρ.source.toScheme.germToFunctionField U).hom r) := by
  have : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  -- `δ := zpowNegOneIso μ` is a frame of `L^∨` on `U`; its pullback `η^*δ` is a frame of `η^*L^∨` on `η⁻¹U`
  have hδ : AlgebraicGeometry.Scheme.Modules.IsFrame (AlgebraicGeometry.Scheme.Modules.dual L.toModules) U
      (AlgebraicGeometry.Scheme.Modules.Hom.app L.zpowNegOneIso.hom U μ) :=
    hμ.map_iso L.zpowNegOneIso
  have ht := MiyaokaMori.DualPullback.isFrame_unitSec_pullback
    (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme))
    (AlgebraicGeometry.Scheme.Modules.dual L.toModules) hδ
  -- `η` lands in `U`
  have hι' : (⊤ : (AlgebraicGeometry.Spec
      (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme)) ⁻¹ᵁ U := by
    intro y _
    show (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme)).base y ∈ U
    rw [AlgebraicGeometry.Scheme.fromSpecResidueField_apply]
    exact hηU
  have hι : (⊤ : (AlgebraicGeometry.Spec
      (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      (𝟙 (AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)))) ⁻¹ᵁ
        ((ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme)) ⁻¹ᵁ U) := hι'
  -- the trivialization induced by the frame `η^*δ`
  obtain ⟨e, he⟩ := AlgebraicGeometry.Scheme.Modules.exists_iso_unit_app_res_unitSec_eq_one
    (𝟙 (AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)))) _ hι ht
  refine ⟨e, fun p r hΨ => ?_⟩
  -- the local ring map of the lift at `x_p` is `η^♯ r` (general computation, `T' = Spec κ(η)`, `g = η`)
  have hlift := J.liftLocalPieceAux_precompLiftData_eq_of_frame
    (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme))
    (J.genericWeightComponent_generates_of_ne_zero hne) chart (ρ.top_le_genericBase_preimage hηV) hUV hι μ e he
    p r hΨ
  have hid : AlgebraicGeometry.Scheme.Hom.appLE
        (𝟙 (AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))))
        ((ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme)) ⁻¹ᵁ U) ⊤ hι
        ((ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme)).app U r) =
      (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme)).appLE U ⊤ hι' r := by
    show (AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).presheaf.map
        (homOfLE hι).op
        (AlgebraicGeometry.Scheme.Hom.app
          (𝟙 (AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))))
          ((ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme)) ⁻¹ᵁ U)
          ((ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme)).app U r)) =
      (AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).presheaf.map
        (homOfLE hι').op ((ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme)).app U r)
    rw [AlgebraicGeometry.Scheme.Hom.id_app]
    rfl
  have hD : J.genericLiftData hne =
      J.precompLiftData (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme))
        (J.genericWeightComponent_generates_of_ne_zero hne) := rfl
  -- unfold the definition by its (separately proved) defining equation, not by `unfold`/`show`: see the
  -- docstring of `BasedJetGenericChartCoordsEq`
  rw [BasedJet.genericChartCoords_eq_liftLocalPieceAux, hD, hlift, hid]
  exact AlgebraicGeometry.Scheme.functionFieldIsoResidueField_inv_ΓSpecIso_hom_appLE ρ.source.toScheme hηU hι' r

end
