import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks0892

/-! # Finite schemes over a projective `k`-scheme are projective

A scheme finite over a projective `k`-scheme is again projective over `k`: if `ν : C ⟶ Γ` is a finite
`k`-morphism and `Γ` is projective over `k`, then `C` is projective over `k`.

References: Stacks Project, Tag 0C4P (a finite morphism is projective) + Tag 01W7 (composition of
projective morphisms over a quasi-compact quasi-separated base). Here we instead use the
characterization `isProjectiveOver_iff_isProper_and_isAmple`: finite ⇒ proper (Mathlib's
`IsFinite → IsProper` instance); finite ⇒ affine ⇒ quasi-affine (Mathlib's low-priority `IsQuasiAffine`
instance) ⇒ the pullback of an ample sheaf along `ν` is ample (Stacks Project, Tag 0892 (2),
`IsAmple.pullback_of_isQuasiAffine`).

Typical use: the normalization `ν : C → Γ` of a projective curve `Γ` is finite, so `C` is projective;
this avoids the general result that a proper scheme of dimension `≤ 1` over a field is projective
(Stacks Project, Tag 0A26).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A scheme `C` finite over a projective `k`-scheme `Γ` is projective over `k`: `C` is proper (finite ⇒
proper, composed with `Γ ↘ Spec k`), and the pullback of an ample invertible sheaf on `Γ` along the
finite (hence quasi-affine) morphism `ν` is ample (Stacks Project, Tag 0892 (2)); then apply
`isProjectiveOver_iff_isProper_and_isAmple`. -/
theorem IsProjectiveOver.of_isFinite {k : Type u} [Field k]
    {C Γ : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Γ.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (ν : C ⟶ Γ) [AlgebraicGeometry.IsFinite ν]
    [ν.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hΓ : IsProjectiveOver k Γ) : IsProjectiveOver k C := by
  rw [isProjectiveOver_iff_isProper_and_isAmple] at hΓ ⊢
  obtain ⟨hproper, L, hL, hamp⟩ := hΓ
  have : L.IsLineBundle := hL
  have : AlgebraicGeometry.IsProper (Γ ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hproper
  have hcomp : ν ≫ (Γ ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      C ↘ AlgebraicGeometry.Spec (CommRingCat.of k) :=
    (inferInstance : ν.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))).1
  refine ⟨?_, (AlgebraicGeometry.Scheme.Modules.pullback ν).obj L, inferInstance, ?_⟩
  · rw [← hcomp]
    infer_instance
  · refine AlgebraicGeometry.IsAmple.pullback_of_isQuasiAffine ν (fun V => ?_) L hamp
    have : AlgebraicGeometry.IsAffine (ν ⁻¹ᵁ V.1) := V.2.preimage ν
    infer_instance

end
