import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.PositiveLineCoreWeightedRescalingHonestChart
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ConeCoefficientsVanishXiCoefficients
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.WeightComponentsVanishOfXiCoefficients

/-! # A unit chart coordinate at every point makes the normalized tuple nowhere zero
(step 5 of the proof of Lemma 3.1 of the paper)

> at each point at least one `a_{α,i,q}` is a unit … Its positive-order coefficient tuple is nowhere
> zero.

`NormalizedTupleNowhereZero J` is stated through the cone coefficients `J.coefficient ℓ q`,
while the construction of `J` controls the chart coordinates
`Ψ_{q+1}(x_{i,q})`. This module proves the passage from the second to the first: it is the converse
direction of `BasedJet.exists_pieceSection_generatesAt`.

It is assembled from the three lemmas `BasedJet.pieceSection_germ_mem_of_isZeroAt`,
`BasedJet.pieceSection_germ_mem_of_forall_isZeroAt` and `BasedJet.weightComponent_germ_mem_of_forall_pieceSection`.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}

/-- **Nowhere-zero normalized tuple from a unit chart coordinate at every point**
(Lemma 3.1 of the paper). Let `J : C̃_(κ)(L) → 𝒵` be a based jet
over `ρ`. Suppose that every `y ∈ C̃` has an honest jet chart `(V, chart)` with `ρ(y) ∈ V`, an open
`U ∋ y` with `U ≤ ρ⁻¹V`, a frame `μ` of `L^{-1}` on `U`, a chart coordinate `x_{i,q}` and a section
`r ∈ O(U)` **that is a unit at `y`** with `Ψ_{q+1}(x_{i,q})|_U = r • μ^{⊗(q+1)}`
(`Ψ_m := J.weightComponent m` transposed along the adjunction, `μ^{⊗m} := pieceIso (framePow μ m)`).
Then `NormalizedTupleNowhereZero J`: at every `y` some cone coefficient `J.coefficient ℓ m`,
`1 ≤ m ≤ κ`, does not vanish at `y`.

Natural-language proof. Fix `y` and the data above; `m := q + 1`. Suppose, for contradiction, that
all `J.coefficient ℓ m'` (`1 ≤ m' ≤ κ`) vanish at `y` (`IsZeroAt`). Shrink `V` to an affine `V' ∋ ρ(y)`
on which the cone's line bundle `A = f^*O_X(1)` has a frame, so that `B_{V'} = Γ(𝒵, π⁻¹V')` is generated
as a `Γ(V')`-algebra by the `N + 1` cone coordinates `x_ℓ` in that frame (`𝒵 = Tot(A^{⊕(N+1)})`,
`TotLineAffineOverBase`, `TwistedAffineCone`). The `t^{m'}`-coefficients `J.pieceSection V' m' (x_ℓ)`
are, up to the frame of `ρ^*A`, the `J.coefficient ℓ m'` (the key equality (4) recorded in the
docstring of `BasedJet.exists_pieceSection_generatesAt`; `IsZeroAt` is invariant under tensoring with a
frame), hence they all vanish at `y`. The map `c ↦ J^♯ c` is a ring homomorphism `B_{V'} → O(p⁻¹ρ⁻¹V')`
and the `ξ`-expansion `structureIso⁻¹` is multiplicative with `ξ^{a} ξ^{b} = ξ^{a+b}` (`pieceMul`), so
the positive-order `ξ`-coefficients of `J^♯(c)` for an arbitrary `c ∈ B_{V'}` — a polynomial in the
`x_ℓ` with coefficients in `Γ(V')` — are sums of products in which at least one factor is a positive
coefficient of some `J^♯ x_ℓ`; all vanish at `y` (`𝔪_y` is an ideal). Thus `J.pieceSection V' m' c`
vanishes at `y` for all `c ∈ B_{V'}`, `m' ≥ 1`. By `BasedJet.weightComponent_jetCoordinate`
, `Ψ_{m'}(d_{m'-1} c) = J.pieceSection V' m' c` vanishes
at `y` for every generator `d_{q'} c` of the based jet algebra `S(V') = J_κ(B_{V'}, s^♯)`
(`relativeJetScheme.chartSections`, `BasedJetAlgebra.coeffClass`). The chart coordinate `x_{i,q}|_{V'}`
lies in `S_m(V')`, which is spanned over `Γ(V')` by monomials in the `d_{q'} c` of total weight `m ≥ 1`
— every such monomial has at least one factor — and `Ψ` is multiplicative and `Γ(V')`-linear
(`BasedJet.weightComponent_map_mul`, `weightComponent_map_one`), so
`Ψ_m(x_{i,q})|_{U ⊓ ρ⁻¹V'}` vanishes at `y`. But `Ψ_m(x_{i,q})|_U = r • μ^{⊗m}` with `r` a unit at `y` and
`μ^{⊗m}` a frame (`truncatedJetAlgebra.framePow_isFrame`, `pieceIso` an isomorphism), whose germ at `y`
is not in `𝔪_y · (L^∨)^{⊗m}_y` (`IsFrame.germ_notMem_maximalIdeal_smul`) — contradiction. ∎

**Assembly.** Suppose all `J.coefficient ℓ m'`
(`1 ≤ m' ≤ κ`) vanish at `y`; shrink `V` to an affine `V' ∋ ρ(y)`, `V' ≤ V`, with a frame `a` of `A`
(`exists_affine_frame_le`). Then
(i) `BasedJet.pieceSection_germ_mem_of_forall_isZeroAt` (its step (1) is
`BasedJet.pieceSection_germ_mem_of_isZeroAt`, the converse of `exists_pieceSection_germ_notMem_of_not_isZeroAt`)
gives: every `J.pieceSection V' m' c` (`c ∈ B_{V'}`, `1 ≤ m' ≤ κ`) has germ at `y` in `𝔪_y • ⊤`;
(ii) `BasedJet.weightComponent_germ_mem_of_forall_pieceSection` gives: `Ψ_m(x|_{V'})` has germ at `y` in `𝔪_y • ⊤` for
`x = x_{i,q}`, `m = q + 1 ≤ κ`;
(iii) naturality of `Ψ_m` (`PresheafOfModules.naturality_apply`) and the invariance of the germ criterion
under restriction (`germ_res_mem_maximalIdeal_smul_iff`, twice: `ρ⁻¹V' ≤ ρ⁻¹V` and `U ≤ ρ⁻¹V`) turn this
into "`Ψ_m(x_{i,q})|_U` has germ at `y` in `𝔪_y • ⊤`"; by hypothesis that section is `r • μ^{⊗m}`, and
`germ (r • ν) = germ r • germ ν` (`germ_smul'`) with `germ r` a unit gives `germ ν ∈ 𝔪_y • ⊤` for the frame
`ν = pieceIso (framePow μ m)` (`framePow_isFrame`, `IsFrame.map_iso`), contradicting
`IsFrame.germ_notMem_maximalIdeal_smul`. The key equality is the one behind
`exists_pieceSection_generatesAt` (`coefficient_eq`, `pullbackSectionToPushforward_coneCoordinate_res`);
this module uses it through (i).

Edge cases: `κ = 0`: no `q : Fin 0`, the hypothesis is unsatisfiable and the conclusion
(`1 ≤ m ≤ 0`) is false — consistent; `r` a unit at `y` is needed only at `y`, not on `U`. -/
theorem BasedJet.normalizedTupleNowhereZero_of_unit_coefficient {f : C.toScheme ⟶ X.toScheme}
    [MMSetup f] {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {κ : ℕ}
    (J : BasedJet f ρ L κ)
    (h : ∀ y : ρ.source.toScheme, ∃ (V : C.toScheme.Opens) (chart : HonestJetChart f κ V)
      (U : ρ.source.toScheme.Opens) (hyU : y ∈ U) (hUV : U ≤ ρ.hom ⁻¹ᵁ V)
      (μ : Γ((L.zpow (-1)).toModules, U))
      (_ : AlgebraicGeometry.Scheme.Modules.IsFrame (L.zpow (-1)).toModules U μ)
      (i : Fin (X.toVariety.dim + 1)) (q : Fin κ) (r : Γ(ρ.source.toScheme, U)),
      IsUnit (ρ.source.toScheme.presheaf.germ U y hyU r) ∧
      (show Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
          (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩), U) from
        ((AlgebraicGeometry.Scheme.Modules.monoidalPow
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
          (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩)).val.map (CategoryTheory.homOfLE hUV).op).hom
        (((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).homEquiv _ _)
          (J.weightComponent (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩))).val.app
            (Opposite.op V)).hom (chart.coords (i, q)))) =
        r • (show Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
          (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩), U) from
          (((truncatedJetAlgebra.pieceIso L (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩)).hom.val.app
            (Opposite.op U)).hom
            (truncatedJetAlgebra.framePow L U μ (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩))))) :
    NormalizedTupleNowhereZero J := by
  intro y
  obtain ⟨V, chart, U, hyU, hUV, μ, hμ, i, q, r, hr, heq⟩ := h y
  by_contra hcon
  have hall : ∀ (ℓ : Fin (X.embDim + 1)) (n : ℕ), 1 ≤ n → n ≤ κ → IsZeroAt (J.coefficient ℓ n) y := by
    intro ℓ n h1 hn
    by_contra hne
    exact hcon ⟨ℓ, n, h1, hn, hne⟩
  have hyV : ρ.hom.base y ∈ V := hUV hyU
  obtain ⟨V', hV'aff, hV'V, hyV', a, ha⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_affine_frame_le (seedLineBundle X.embedding f) hyV
  have hy' : y ∈ ρ.hom ⁻¹ᵁ V' := hyV'
  have hm1 : 1 ≤ jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩ := jetWeights_pos _ _ _
  have hmκ : jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩ ≤ κ := Nat.succ_le_of_lt q.2
  have hE := J.pieceSection_germ_mem_of_forall_isZeroAt y ⟨V', hV'aff⟩ hy' ha hall
  have hD := J.weightComponent_germ_mem_of_forall_pieceSection y ⟨V', hV'aff⟩ hy' hE
    (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩) hm1 hmκ
    ((((jetAlgebra f κ).part (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩)).val.map
      (CategoryTheory.homOfLE hV'V).op).hom (chart.coords (i, q)))
  -- naturality of Ψ along V' ≤ V
  set N := AlgebraicGeometry.Scheme.Modules.monoidalPow
    (AlgebraicGeometry.Scheme.Modules.dual L.toModules) (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩) with hN
  set Ψ := ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).homEquiv _ _)
    (J.weightComponent (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩)) with hΨ
  have hnat := PresheafOfModules.naturality_apply Ψ.val (CategoryTheory.homOfLE hV'V).op (chart.coords (i, q))
  have hle' : ρ.hom ⁻¹ᵁ V' ≤ ρ.hom ⁻¹ᵁ V := fun z hz => hV'V hz
  rw [hnat] at hD
  have h1 : N.presheaf.germ (ρ.hom ⁻¹ᵁ V') y hy'
      (N.res hle' ((Ψ.val.app (Opposite.op V)).hom (chart.coords (i, q)))) ∈
      (IsLocalRing.maximalIdeal (ρ.source.toScheme.presheaf.stalk y)) •
        (⊤ : Submodule (ρ.source.toScheme.presheaf.stalk y) (N.presheaf.stalk y)) := hD
  have h2 := (AlgebraicGeometry.Scheme.Modules.germ_res_mem_maximalIdeal_smul_iff N hle' hy' _).mp h1
  have h3 := (AlgebraicGeometry.Scheme.Modules.germ_res_mem_maximalIdeal_smul_iff N hUV hyU
    ((Ψ.val.app (Opposite.op V)).hom (chart.coords (i, q)))).mpr h2
  have h4 : N.presheaf.germ U y hyU
      (r • (show Γ(N, U) from
        (((truncatedJetAlgebra.pieceIso L (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩)).hom.val.app
          (Opposite.op U)).hom
          (truncatedJetAlgebra.framePow L U μ (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩))))) ∈
      (IsLocalRing.maximalIdeal (ρ.source.toScheme.presheaf.stalk y)) •
        (⊤ : Submodule (ρ.source.toScheme.presheaf.stalk y) (N.presheaf.stalk y)) := by
    rw [← heq]
    exact h3
  rw [AlgebraicGeometry.Scheme.Modules.germ_smul'] at h4
  have hν : AlgebraicGeometry.Scheme.Modules.IsFrame N U
      (show Γ(N, U) from
        (((truncatedJetAlgebra.pieceIso L (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩)).hom.val.app
          (Opposite.op U)).hom
          (truncatedJetAlgebra.framePow L U μ (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩)))) :=
    (truncatedJetAlgebra.framePow_isFrame L U μ hμ (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩)).map_iso
      (truncatedJetAlgebra.pieceIso L (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩))
  apply hν.germ_notMem_maximalIdeal_smul hyU
  obtain ⟨u, hu⟩ := hr
  have h5 := Submodule.smul_mem _ (↑u⁻¹ : ρ.source.toScheme.presheaf.stalk y) h4
  rw [smul_smul, ← hu, Units.inv_mul, one_smul] at h5
  exact h5

end
