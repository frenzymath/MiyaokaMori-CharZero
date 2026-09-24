import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.PointIdealSheaf

/-! # The support of a point ideal sheaf

For a closed point `x` and an `𝔪_x`-primary ideal `q`, the cosupport of `pointIdealSheaf x q` is
contained in `{x}`.

References: the hypothesis of Stacks 0AHH that `O_X/I` is supported at finitely many closed
points; Hartshorne II Example 7.17.3.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- If `x` is a closed point and `𝔪_xⁿ ≤ q`, then `supp(O_X / pointIdealSheaf x q) ⊆ {x}`.

Proof sketch: let `g := Spec.map (mk q) ≫ X.fromSpecStalk x : Spec(O_{X,x}/q) → X`.
(1) Since `𝔪ⁿ ≤ q`, the only prime of `O_{X,x}/q` is `𝔪/q`, so `Spec(O_{X,x}/q)` has at most one
point (none if `q = ⊤`), whose image is `x` (`Scheme.fromSpecStalk_closedPoint`); so
`Set.range g ⊆ {x}`.
(2) A source with at most one point makes `g` quasi-compact.
(3) `Scheme.Hom.support_ker`: `(g.ker).support = closure (range g) ⊆ closure {x} = {x}`. -/
theorem AlgebraicGeometry.Scheme.pointIdealSheaf_support_subset
    (X : AlgebraicGeometry.Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X))
    (q : Ideal (X.presheaf.stalk x)) (n : ℕ)
    (hq : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n ≤ q) :
    ((X.pointIdealSheaf x q).support : Set X) ⊆ {x} := by
  -- (1) every point of `Spec (O_{X,x} ⧸ q)` maps to the closed point of `Spec O_{X,x}`
  have hpt : ∀ P : AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.stalk x ⧸ q)),
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk q)) P =
        IsLocalRing.closedPoint (X.presheaf.stalk x) := by
    intro P
    rw [AlgebraicGeometry.Spec.map_apply]
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (Ideal.Quotient.mk q) P.asIdeal = IsLocalRing.maximalIdeal _
    have hP : P.asIdeal.IsPrime := P.isPrime
    have : (Ideal.comap (Ideal.Quotient.mk q) P.asIdeal).IsPrime := Ideal.comap_isPrime _ _
    apply le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime _)
    apply Ideal.IsPrime.le_of_pow_le (n := n)
    calc IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n ≤ q := hq
      _ = RingHom.ker (Ideal.Quotient.mk q) := Ideal.mk_ker.symm
      _ ≤ Ideal.comap (Ideal.Quotient.mk q) P.asIdeal := Ideal.ker_le_comap _
  -- the source has at most one point
  have hsub : Subsingleton (AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.stalk x ⧸ q))) := by
    refine ⟨fun P Q ↦ ?_⟩
    have h : AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk q)) P =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk q)) Q := by
      rw [hpt P, hpt Q]
    rw [AlgebraicGeometry.Spec.map_apply, AlgebraicGeometry.Spec.map_apply] at h
    exact PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective h
  -- (2) the composite is quasi-compact
  have : AlgebraicGeometry.QuasiCompact
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk q)) ≫ X.fromSpecStalk x) :=
    ⟨fun U _ _ ↦ (Set.subsingleton_of_subsingleton).isCompact⟩
  -- range of the composite is contained in `{x}`
  have hrange : Set.range
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk q)) ≫ X.fromSpecStalk x) ⊆
        {x} := by
    rintro _ ⟨P, rfl⟩
    rw [AlgebraicGeometry.Scheme.Hom.comp_apply, hpt P,
      AlgebraicGeometry.Scheme.fromSpecStalk_closedPoint]
    exact Set.mem_singleton x
  -- (3) support of the kernel is the closure of the range
  unfold AlgebraicGeometry.Scheme.pointIdealSheaf
  rw [AlgebraicGeometry.Scheme.Hom.support_ker]
  calc (closure (Set.range (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk q)) ≫
        X.fromSpecStalk x)) : Set X)
      ⊆ closure {x} := closure_mono hrange
    _ = {x} := hx.closure_eq

end
