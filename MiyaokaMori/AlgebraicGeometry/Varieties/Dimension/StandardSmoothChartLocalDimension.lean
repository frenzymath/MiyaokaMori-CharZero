import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Dimension.EtaleOverMvPolynomialKrullDimEq
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.LocalDimension
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.KrullDimension

/-! # Local dimension on a standard smooth chart

If `V` is an affine open of a scheme `X` and `K → Γ(X, V)` is a standard smooth ring map of
relative dimension `n` from a field `K`, then the local dimension of `X` (`localDimension`, the
infimum of the topological Krull dimensions of open neighbourhoods) at every point of `V` is `n`.

Proof sketch: every open neighbourhood `W` of `x` contains a basic open `D(g) ∋ x` of `V`;
`Γ(X, D(g)) = Γ(X, V)_g` is again a nonzero standard smooth `K`-algebra of relative dimension
`n`, whose Krull dimension is `n` (`RingHom.IsStandardSmoothOfRelativeDimension.ringKrullDim_eq`),
so `n = dim D(g) ≤ dim W`; on the other hand `dim V = n`.

Source: Stacks 00T7 (7), in geometric form.
-/

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The topological Krull dimension of an affine open equals the Krull dimension of its section
ring. -/
theorem IsAffineOpen.topologicalKrullDim_eq_ringKrullDim {V : X.Opens} (hV : IsAffineOpen V) :
    topologicalKrullDim V = ringKrullDim Γ(X, V) := by
  calc topologicalKrullDim V = topologicalKrullDim (Spec Γ(X, V)) :=
        IsHomeomorph.topologicalKrullDim_eq _ hV.isoSpec.hom.homeomorph.isHomeomorph
    _ = ringKrullDim Γ(X, V) := by
        change topologicalKrullDim (PrimeSpectrum Γ(X, V)) = ringKrullDim Γ(X, V)
        exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, V)

/-- On a standard smooth chart, the (untruncated) infimum of the dimensions of open neighbourhoods
is the relative dimension. -/
theorem IsAffineOpen.iInf_topologicalKrullDim_eq_of_isStandardSmoothOfRelativeDimension
    {K : Type u} [Field K] {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (φ : K →+* Γ(X, V)) (hφ : φ.IsStandardSmoothOfRelativeDimension n) (x : X) (hx : x ∈ V) :
    (⨅ W ∈ {W : X.Opens | x ∈ W}, topologicalKrullDim W) = ((n : ℕ∞) : WithBot ℕ∞) := by
  have hnontriv : ∀ (D : X.Opens), x ∈ D → Nontrivial Γ(X, D) := fun D hD => by
    have : Nonempty D := ⟨⟨x, hD⟩⟩
    have : Nonempty (D : Scheme) := ‹_›
    exact Scheme.component_nontrivial X D
  refine le_antisymm ?_ (le_iInf₂ fun W hW => ?_)
  · refine (iInf₂_le V hx).trans ?_
    have := hnontriv V hx
    rw [hV.topologicalKrullDim_eq_ringKrullDim, hφ.ringKrullDim_eq]
    rfl
  · obtain ⟨g, hgW, hxg⟩ := hV.exists_basicOpen_le ⟨x, hW⟩ hx
    have hD : IsAffineOpen (X.basicOpen g) := hV.basicOpen g
    have := hV.isLocalization_basicOpen g
    have h0 : (algebraMap Γ(X, V) Γ(X, X.basicOpen g)).IsStandardSmoothOfRelativeDimension 0 :=
      RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway g
    have hψ : ((algebraMap Γ(X, V) Γ(X, X.basicOpen g)).comp φ).IsStandardSmoothOfRelativeDimension n := by
      have := h0.comp hφ
      rwa [zero_add] at this
    have := hnontriv _ hxg
    have hdim : topologicalKrullDim (X.basicOpen g) = ((n : ℕ∞) : WithBot ℕ∞) := by
      rw [hD.topologicalKrullDim_eq_ringKrullDim, hψ.ringKrullDim_eq]
      rfl
    rw [← hdim]
    exact (Topology.IsEmbedding.inclusion
      (s := (X.basicOpen g : Set X)) (t := (W : Set X)) hgW).isInducing.topologicalKrullDim_le

/-- Geometric form of Stacks 00T7 (7): on a standard smooth chart the local dimension at every
point equals the relative dimension. -/
theorem IsAffineOpen.localDimension_eq_of_isStandardSmoothOfRelativeDimension
    {K : Type u} [Field K] {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (φ : K →+* Γ(X, V)) (hφ : φ.IsStandardSmoothOfRelativeDimension n) (x : X) (hx : x ∈ V) :
    localDimension X x = n := by
  unfold localDimension
  rw [hV.iInf_topologicalKrullDim_eq_of_isStandardSmoothOfRelativeDimension φ hφ x hx,
    WithBot.unbotD_coe, ENat.toNat_natCast]

end AlgebraicGeometry
