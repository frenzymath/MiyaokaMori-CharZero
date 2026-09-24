import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowIsos
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowSectionLocus

/-! # A finite affine cover by sections of one tensor power of an ample sheaf

If `L` is ample (`X` quasi-compact, and every point lies in an affine `X_s` with
`s ∈ Γ(L^{⊗m})`, `m > 0`), then there are **one** positive degree `n` and **finitely many**
`s_i ∈ Γ(X, L^{⊗n})` whose nonvanishing loci `X_{s_i}` are affine and cover `X`.

Proof sketch (first paragraph of the proof of Stacks 01VU):
1. For every point `x` choose `m_x > 0` and `s_x ∈ Γ(L^{⊗m_x})` with `x ∈ X_{s_x}` affine; by
   quasi-compactness a finite set `T` of points suffices.
2. Put `n := ∏_{x ∈ T} m_x > 0`, so `n = m_x · e_x` with `e_x > 0`.
3. Let `S_x := θ_x(s_x^{⊗e_x})` with `θ_x : (L^{⊗m_x})^{⊗e_x} ≅ L^{⊗n}` (`tensorPowMulIso` followed by
   `eqToIso`). Nonvanishing loci are invariant under isomorphisms (`nonvanishingLocus_iso`) and
   `X_{s^{⊗e}} = X_s` for `e > 0` (`nonvanishingLocus_tensorPowSection`), so `X_{S_x} = X_{s_x}`.

Reference: the proof of Stacks 01VU.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Finite affine cover by sections of one tensor power** (Stacks 01VU, first step). -/
theorem AlgebraicGeometry.IsAmple.exists_finite_affine_cover {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (hL : AlgebraicGeometry.IsAmple L) :
    ∃ (n : ℕ) (_ : 0 < n) (ι : Type u) (_ : Fintype ι)
      (s : ι → Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤)),
      (∀ x : X, ∃ i, x ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus (s i)) ∧
      ∀ i, AlgebraicGeometry.IsAffineOpen
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus (s i)) := by
  obtain ⟨hcpt, hcov⟩ := hL
  choose m hm s hxs haff using hcov
  -- finite subcover
  obtain ⟨T, hT⟩ := CompactSpace.isCompact_univ.elim_finite_subcover
    (fun x : X => ((AlgebraicGeometry.Scheme.Modules.tensorPow L (m x)).nonvanishingLocus (s x) : Set X))
    (fun x => ((AlgebraicGeometry.Scheme.Modules.tensorPow L (m x)).nonvanishingLocus (s x)).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxs x⟩)
  set n : ℕ := ∏ x ∈ T, m x with hn
  have hnpos : 0 < n := Finset.prod_pos fun x _ => hm x
  have hdvd : ∀ x ∈ T, m x ∣ n := fun x hx => Finset.dvd_prod_of_mem m hx
  -- the uniform-power sections
  let e : X → ℕ := fun x => n / m x
  have hme : ∀ x ∈ T, m x * e x = n := fun x hx => Nat.mul_div_cancel' (hdvd x hx)
  have hepos : ∀ x ∈ T, 0 < e x := fun x hx =>
    Nat.div_pos (Nat.le_of_dvd hnpos (hdvd x hx)) (hm x)
  let θ : ∀ x ∈ T, AlgebraicGeometry.Scheme.Modules.tensorPow
      (AlgebraicGeometry.Scheme.Modules.tensorPow L (m x)) (e x) ≅
      AlgebraicGeometry.Scheme.Modules.tensorPow L n := fun x hx =>
    AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L (m x) (e x) ≪≫
      CategoryTheory.eqToIso (by rw [hme x hx])
  let S : ∀ x ∈ T, Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤) := fun x hx =>
    (θ x hx).hom.app ⊤ (AlgebraicGeometry.Scheme.Modules.tensorPowSection (s x) (e x))
  have hS : ∀ x (hx : x ∈ T),
      (AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus (S x hx) =
        (AlgebraicGeometry.Scheme.Modules.tensorPow L (m x)).nonvanishingLocus (s x) := by
    intro x hx
    have h1 := AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso (θ x hx)
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection (s x) (e x) :
        Γ(AlgebraicGeometry.Scheme.Modules.tensorPow
          (AlgebraicGeometry.Scheme.Modules.tensorPow L (m x)) (e x), ⊤))
    have h2 := AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_tensorPowSection
      (AlgebraicGeometry.Scheme.Modules.tensorPow L (m x)) (s x) (hepos x hx)
    exact h1.trans h2
  refine ⟨n, hnpos, {x // x ∈ T}, inferInstance, fun x => S x.1 x.2, ?_, ?_⟩
  · intro x
    have hx := hT (Set.mem_univ x)
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨y, hyT, hxy⟩ := hx
    refine ⟨⟨y, hyT⟩, ?_⟩
    rw [hS y hyT]
    exact hxy
  · intro x
    rw [hS x.1 x.2]
    exact haff x.1

end
