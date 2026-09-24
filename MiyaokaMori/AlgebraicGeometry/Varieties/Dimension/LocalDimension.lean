import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.DimensionTruncation
/-! # Local dimension of a scheme at a point

The local dimension `dim_p Z` of a scheme at a point (the quantity bounded from below by
deformation theory).

**Typing convention.** `localDimension Z p : ℕ` is derived
from the one primitive `topologicalKrullDim : WithBot ℕ∞` — the infimum over the open neighbourhoods
`U ∋ p` of `topologicalKrullDim U` — by the same truncation `(·.unbotD 0).toNat` as
`Scheme.dimension`. `⊥` never occurs (every `U` contains `p`); `⊤` is excluded by the hypothesis
`topologicalKrullDim Z ≠ ⊤` of `localDimension_spec` / `localDimension_eq_iff`, the lemmas through which
every comparison with the untruncated value goes (corollaries of `MiyaokaMori.natCast_unbotD_toNat`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- `topologicalKrullDim` takes values in `WithBot ℕ∞`: first remove `⊥` with `WithBot.unbotD 0`
   (it does not occur since `p ∈ U`), then truncate to `ℕ` with `ENat.toNat`. -/

private theorem topologicalKrullDim_nonneg_of_nonempty (α : Type*) [TopologicalSpace α]
    [Nonempty α] : (0 : WithBot ℕ∞) ≤ topologicalKrullDim α := by
  obtain ⟨x⟩ := ‹Nonempty α›
  have : Nonempty (IrreducibleCloseds α) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact Order.krullDim_nonneg

/-- The local dimension of `Z` at `p`: the infimum over the open neighbourhoods `U ∋ p` of
`topologicalKrullDim U`, truncated to `ℕ`. -/
noncomputable def localDimension (Z : AlgebraicGeometry.Scheme.{u}) (p : Z) : ℕ :=
  (WithBot.unbotD 0 (⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U)).toNat

theorem localDimension_le_dim (Z : AlgebraicGeometry.Scheme.{u}) (p : Z) :
    (localDimension Z p : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
  have hI : (⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U) ≤ topologicalKrullDim Z :=
    (iInf₂_le (⊤ : Z.Opens) (show p ∈ (⊤ : Z.Opens) from trivial)).trans
      (Topology.IsInducing.subtypeVal.topologicalKrullDim_le)
  have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
    have : Nonempty Z := ⟨p⟩
    exact topologicalKrullDim_nonneg_of_nonempty Z
  unfold localDimension
  generalize (⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U) = I at hI
  cases I with
  | bot => simpa using h0
  | coe a =>
    refine le_trans ?_ hI
    rw [WithBot.unbotD_coe]
    exact WithBot.coe_le_coe.mpr (ENat.natCast_toNat_le_self a)

/-- The truncation loses nothing: when `Z` has finite Krull dimension, the infimum of the dimensions
of the open neighbourhoods (in `WithBot ℕ∞`) equals `localDimension`. (Each `U` contains `p`, so is
nonempty with dimension `≥ 0`, and the infimum is not `⊥`; it is `≤ dim Z < ⊤`, so not `⊤`.) -/

theorem localDimension_spec (Z : AlgebraicGeometry.Scheme.{u}) (p : Z)
    (h : topologicalKrullDim Z ≠ ⊤) :
    (⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U) = (localDimension Z p : WithBot ℕ∞) := by
  have hI : (⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U) ≤ topologicalKrullDim Z :=
    (iInf₂_le (⊤ : Z.Opens) (show p ∈ (⊤ : Z.Opens) from trivial)).trans
      (Topology.IsInducing.subtypeVal.topologicalKrullDim_le)
  have hbot : (⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U) ≠ ⊥ := by
    intro hb
    have h0 : (0 : WithBot ℕ∞) ≤ ⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U := by
      refine le_iInf₂ fun U hU => ?_
      have : Nonempty U := ⟨⟨p, hU⟩⟩
      exact topologicalKrullDim_nonneg_of_nonempty U
    rw [hb] at h0
    exact absurd h0 (by simp)
  have htop : (⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U) ≠ ⊤ := by
    intro ht
    rw [ht, top_le_iff] at hI
    exact h hI
  exact (MiyaokaMori.natCast_unbotD_toNat hbot htop).symm

/-- The infimum defining `localDimension` is never `⊥` (every neighbourhood contains `p`). -/
theorem localDimension_iInf_ne_bot (Z : AlgebraicGeometry.Scheme.{u}) (p : Z) :
    (⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U) ≠ ⊥ := by
  intro hb
  have h0 : (0 : WithBot ℕ∞) ≤ ⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U := by
    refine le_iInf₂ fun U hU => ?_
    have : Nonempty U := ⟨⟨p, hU⟩⟩
    exact topologicalKrullDim_nonneg_of_nonempty U
  rw [hb] at h0
  exact absurd h0 (by simp)

/-- The infimum defining `localDimension` is finite when `Z` is finite-dimensional. -/
theorem localDimension_iInf_ne_top (Z : AlgebraicGeometry.Scheme.{u}) (p : Z)
    (h : topologicalKrullDim Z ≠ ⊤) :
    (⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U) ≠ ⊤ := by
  intro ht
  have hI : (⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U) ≤ topologicalKrullDim Z :=
    (iInf₂_le (⊤ : Z.Opens) (show p ∈ (⊤ : Z.Opens) from trivial)).trans
      (Topology.IsInducing.subtypeVal.topologicalKrullDim_le)
  rw [ht, top_le_iff] at hI
  exact h hI

/-- The single coercion lemma for `localDimension Z p = n` versus the untruncated infimum. -/
theorem localDimension_eq_iff (Z : AlgebraicGeometry.Scheme.{u}) (p : Z)
    (h : topologicalKrullDim Z ≠ ⊤) (n : ℕ) :
    localDimension Z p = n ↔
      (⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U) = (n : WithBot ℕ∞) :=
  MiyaokaMori.unbotD_toNat_eq_iff (localDimension_iInf_ne_bot Z p)
    (localDimension_iInf_ne_top Z p h) n

end
