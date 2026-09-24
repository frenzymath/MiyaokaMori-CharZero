import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.TruncatedJetPositivePiecesVanishSubring
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.PieceSectionGermVanishing
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetXiExpansion
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ConeSectionsGeneratedByFrameCoordinates

/-! # All cone coefficients vanish at `y` ⇒ all positive `ξ`-coefficients of `J^♯` vanish at `y`
(proof of Lemma 3.1 of the paper; used for
`BasedJet.normalizedTupleNowhereZero_of_unit_coefficient`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
  {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
  {L : LineBundle ρ.source.toVariety} {κ : ℕ}

/-- **All cone coefficients vanish at `y` ⇒ all positive `ξ`-coefficients of `J^♯` vanish at `y`**
(proof of Lemma 3.1 of the paper). Let `U ⊆ C` be an affine open with a frame `a` of
`A = f^*O(1)`, `y ∈ ρ⁻¹U`, and suppose every cone coefficient `J.coefficient ℓ n` (`1 ≤ n ≤ κ`) vanishes
at `y` (`IsZeroAt`). Then for every function `c ∈ B_U = Γ(𝒵, π⁻¹U)` on the cone and every `1 ≤ n ≤ κ`,
the `n`-th `ξ`-coefficient `J.pieceSection U n _ c` of `J^♯ c` has germ at `y` in `𝔪_y • ⊤`.

Natural-language proof.
(1) *Coordinate functions.* For the `N + 1` coordinate functions
`x_ℓ := totalSpace.coordinateFunctionOn A (N+1) ℓ U hf.dualSec coneι (π⁻¹U) _` (the `ℓ`-th coordinate of
the frame `a`, restricted to the cone `𝒵 ↪ Tot(A^{⊕(N+1)})`), the claim is
`BasedJet.pieceSection_germ_mem_of_isZeroAt` (module `PieceSectionGermVanishing`; the converse of
`exists_pieceSection_germ_notMem_of_not_isZeroAt`).
(2) *Generation.* `B_U` is generated as a `Γ(U)`-algebra (`relativeJetScheme.sectionsAlgebra`, i.e.
through `π^♯`) by `x_0, …, x_N`. Indeed `Tot(A^{⊕(N+1)}) = relativeSpec (Sym (A^{⊕(N+1)})^∨)`, so
`Γ(Tot, π⁻¹U) ≅ (Sym (A^{⊕(N+1)})^∨).sectionsRing U` (`relativeSpec.structureIso`, multiplicative by
`structureIso_inv_app_mul`), which is the image of the symmetric algebra
`SymmetricAlgebra Γ(U) Γ((A^{⊕(N+1)})^∨, U)` (`symLiftHom_surjective`, module
`SymGradedAlgebraSectionsRingEquivSym`, for affine `U` and the quasi-coherent dual); the `Γ(U)`-module
`Γ((A^{⊕(N+1)})^∨, U) = ⊕_ℓ Γ(A^∨, U)` is free on the `N + 1` sections `dualMap (biproduct.π ℓ) (hf.dualSec)`
(`a` a frame ⇒ `hf.dualSec` a frame of `A^∨`, `IsFrame.dualFrame_isFrame`), and
`totalSpace.coordinateFunction A (N+1) ℓ U hf.dualSec` is exactly `linearFunction` of that section. So
`Γ(Tot, π⁻¹U)` is generated over `Γ(U)` by the `N + 1` coordinate functions. Finally
`coneι = (⨆ j, idealSheafOfSection …).subschemeι` is the closed immersion of an ideal sheaf and `π⁻¹U` is
affine (`Tot → C` is an affine morphism), so `coneι^♯ : Γ(Tot, π⁻¹U) → Γ(𝒵, π⁻¹U)` is surjective
(Mathlib `IdealSheafData.subschemeι_app_surjective`) and maps the coordinate functions to the `x_ℓ`
(definition of `coordinateFunctionOn`). Hence `Algebra.adjoin Γ(U) {x_0, …, x_N} = ⊤` in `B_U`.
(3) *Closure.* `T := {c ∈ B_U | ∀ 1 ≤ n ≤ κ, germ_y (J.pieceSection U n _ c) ∈ 𝔪_y • ⊤}` is a
`Γ(U)`-subalgebra of `B_U`. The map `c ↦ structureIso⁻¹(J^♯ c) ∈ (truncatedJetAlgebra L κ).sectionsRing (ρ⁻¹U)`
is a ring homomorphism (`J.hom.appLE` is a ring homomorphism; `relativeSpec.structureIso_inv_app_mul`,
`structureIso_inv_app_one`) sending `π^♯ r` to `sectionsUnit (ρ^♯ r)` (`J.over : J ≫ π = p ≫ ρ` and
`structureIso⁻¹ ∘ p^♯ = sectionsUnit`, the unit clause of `relativeSpec.structureHom_isAlgebraMap`), and
`J.pieceSection U n _ c = pieceIso_n (π_n (structureIso⁻¹ (J^♯ c)))` by definition. The germ criterion is
invariant under the isomorphism `pieceIso_n` (`germ_hom_app_mem_maximalIdeal_smul_iff_of_iso`) and under
restriction to a smaller open containing `y` (`germ_res_mem_maximalIdeal_smul_iff`); so shrink to
`U' ∋ y`, `U' ≤ ρ⁻¹U`, carrying a frame `μ` of `L^{-1}` (`exists_frame_le`). On `U'` the sections ring is
`O(U')[t]/(t^{κ+1})` (`polyToSections_surjective`, module `JetChartTrivialization_Basis`) with
`π_n (polyToSections P) = P.coeff n • μ^{⊗n}` (`π_polyToSections`) and `μ^{⊗n}` a frame
(`framePow_isFrame`), and `germ_y (r • μ^{⊗n}) ∈ 𝔪_y • ⊤ ↔ germ_y r ∈ 𝔪_y` (`germ_smul'`,
`IsFrame.germ_notMem_maximalIdeal_smul`, `IsFrame.germ_mem_maximalIdeal_smul_iff_coord`). Thus `T`
corresponds to `{P | ∀ 1 ≤ n ≤ κ, germ_y (P.coeff n) ∈ 𝔪_y}`, which contains the constants and is closed
under `+` and `*` (`Polynomial.coeff_mul`: `coeff n (P * Q) = ∑_{i+j=n} coeff i P * coeff j Q`, and in
every term with `n ≥ 1` one of `i, j` is `≥ 1`, so the term lies in the ideal `𝔪_y`).
(4) By (1) the generators `x_ℓ` lie in `T`, by (3) `T` is a subalgebra, by (2) `T = B_U`. ∎

The formal proof follows (1)–(4) literally:
(2) is `MMSetup.cone_sections_induction` (module `ConeSectionsGeneratedByFrameCoordinates`: an induction principle
for `Γ(𝒵, π⁻¹U)` — a predicate containing `π^♯(Γ(U))` and the `x_ℓ`, closed under `+` and `*`, holds everywhere —
from `totalSpace.isSymmetricAlgebra_linearFunctionLinearMap`, `eq_sum_dualMap_π_app`, `IsFrame.dualSec_isFrame` and
Mathlib's `IdealSheafData.subschemeι_app_surjective`); the transport of (3) is `BasedJet.xiExpansionHom`
(ring homomorphism `c ↦ structureIso⁻¹(J^♯ c) ∈ 𝒜(W)` for `W ≤ ρ⁻¹U`), `BasedJet.xiExpansion_cone_app` (unit clause,
via `relativeSpec.structureHom_app_sectionsUnit`) and `BasedJet.germ_pieceSection_mem_iff` (the germ criterion for
`J.pieceSection U n _ c` at `y ∈ W` is the germ criterion for the `n`-th piece of the `ξ`-expansion on `W`), all in
module `…_NowhereZero_PieceSectionAll_Transport`; the subring property of (3) is `truncatedJetAlgebra.PositivePiecesVanishAt`
with `.add`, `.mul`, `positivePiecesVanishAt_sectionsUnit` (module `…_NowhereZero_TruncatedVanishing`); (1) is
`BasedJet.pieceSection_germ_mem_of_isZeroAt` (module `…_NowhereZero_PieceSectionVanish`). The frame neighbourhood
`W ∋ y` of `L^{-1}` comes from `exists_frame_le`; it need not be affine.

Edge cases: `κ = 0` — hypothesis and conclusion are vacuous (`1 ≤ n ≤ 0`); `U = ⊥` is excluded by
`y ∈ ρ⁻¹U`; the frame `a` is used only through `hf.dualSec`. -/
theorem BasedJet.pieceSection_germ_mem_of_forall_isZeroAt (J : BasedJet f ρ L κ) (y : ρ.source.toScheme)
    (U : C.toScheme.AffineZariskiSite) (hy : y ∈ ρ.hom ⁻¹ᵁ U.1)
    {a : Γ(seedLineBundle X.embedding f, U.1)}
    (hf : AlgebraicGeometry.Scheme.Modules.IsFrame (seedLineBundle X.embedding f) U.1 a)
    (h : ∀ (ℓ : Fin (X.embDim + 1)) (n : ℕ), 1 ≤ n → n ≤ κ → IsZeroAt (J.coefficient ℓ n) y)
    (n : ℕ) (hn : n ≤ κ) (h1 : 1 ≤ n)
    (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U.1)) :
    (AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) n).presheaf.germ
        (ρ.hom ⁻¹ᵁ U.1) y hy (J.pieceSection U.1 n hn c) ∈
      (IsLocalRing.maximalIdeal (ρ.source.toScheme.presheaf.stalk y)) •
        (⊤ : Submodule (ρ.source.toScheme.presheaf.stalk y)
          ((AlgebraicGeometry.Scheme.Modules.monoidalPow
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules) n).presheaf.stalk y)) := by
  -- a frame `μ` of `L^{-1}` on a neighbourhood `W ∋ y`, `W ≤ ρ⁻¹U`
  obtain ⟨W, hWV, hyW, μ, hμ⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_frame_le (L.zpow (-1)).toModules hy
  -- every `c ∈ B_U` has a `ξ`-expansion on `W` with all positive pieces vanishing at `y`
  have key : ∀ c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U.1),
      truncatedJetAlgebra.PositivePiecesVanishAt L κ hyW (J.xiExpansion U.1 hWV c) := by
    refine MMSetup.cone_sections_induction f U hf le_rfl
      (fun c => truncatedJetAlgebra.PositivePiecesVanishAt L κ hyW (J.xiExpansion U.1 hWV c)) ?_ ?_ ?_ ?_
    · -- (3) constants: `xiExpansion (π^♯ r) = sectionsUnit (ρ^♯ r)`
      intro r
      show truncatedJetAlgebra.PositivePiecesVanishAt L κ hyW (J.xiExpansion U.1 hWV ((MMSetup.cone f).hom.app U.1 r))
      rw [J.xiExpansion_cone_app U.1 hWV r]
      exact truncatedJetAlgebra.positivePiecesVanishAt_sectionsUnit L κ hyW μ _
    · -- (1) coordinate functions: the single-coefficient case
      intro ℓ q hq
      have hqκ : (q : ℕ) ≤ κ := Nat.lt_succ_iff.mp q.2
      have h1 := J.pieceSection_germ_mem_of_isZeroAt y ℓ q hqκ U.1 hy hf le_rfl (h ℓ q hq hqκ)
      exact (J.germ_pieceSection_mem_iff y U.1 hWV hyW q hqκ _).mp h1
    · -- closure under `+`
      intro b c hb hc
      show truncatedJetAlgebra.PositivePiecesVanishAt L κ hyW (J.xiExpansionHom U.1 hWV (b + c))
      rw [map_add]
      exact truncatedJetAlgebra.PositivePiecesVanishAt.add L κ hyW μ hμ hb hc
    · -- closure under `*`
      intro b c hb hc
      show truncatedJetAlgebra.PositivePiecesVanishAt L κ hyW (J.xiExpansionHom U.1 hWV (b * c))
      rw [map_mul]
      exact truncatedJetAlgebra.PositivePiecesVanishAt.mul L κ hyW μ hμ hb hc
  -- (4) read off the `n`-th piece
  exact (J.germ_pieceSection_mem_iff y U.1 hWV hyW n hn c).mpr (key c ⟨n, Nat.lt_succ_of_le hn⟩ h1)

end
