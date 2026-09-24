import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.NonZeroDivisorRes

/-! # Divisibility by a nonzerodivisor is local

Let `V` be an affine open of a scheme `X`, `a ∈ Γ(X, V)` a nonzerodivisor, `W ≤ V` any open and
`b ∈ Γ(X, W)`. If `b` is divisible by `a` on each member of an open cover of `W`, then `b` is divisible
by `a|_W` on `W` (`IsAffineOpen.dvd_of_locally_dvd`): the quotient `b/a` on each member is unique by the
nonzerodivisor property, hence the quotients agree on overlaps and glue by the sheaf property of `O_X`.
This is the sheaf-theoretic input for the surjectivity half of `EffCartier.exists_frame_ideal`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Composition of restriction maps of the structure sheaf. -/
theorem Scheme.presheaf_map_map {W'' W' W : X.Opens} (h' : W'' ≤ W') (h : W' ≤ W) (a : Γ(X, W)) :
    X.presheaf.map (homOfLE h').op (X.presheaf.map (homOfLE h).op a) =
      X.presheaf.map (homOfLE (h'.trans h)).op a := by
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]; rfl

/-- Divisibility by a nonzerodivisor is a local property. -/
theorem IsAffineOpen.dvd_of_locally_dvd {V : X.Opens} (hV : IsAffineOpen V) {a : Γ(X, V)}
    (ha : a ∈ nonZeroDivisors Γ(X, V)) {W : X.Opens} (hW : W ≤ V) (b : Γ(X, W))
    (h : ∀ p : W, ∃ (O : X.Opens) (hO : O ≤ W), p.1 ∈ O ∧
      X.presheaf.map (homOfLE (hO.trans hW)).op a ∣ X.presheaf.map (homOfLE hO).op b) :
    X.presheaf.map (homOfLE hW).op a ∣ b := by
  choose O hO hpO hdvd using h
  choose r hr using hdvd
  have hcover : W ≤ iSup O := fun p hp ↦ Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hpO _⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf O r := by
    intro p q
    have hle : O p ⊓ O q ≤ V := inf_le_left.trans ((hO p).trans hW)
    have hnzd := hV.res_mem_nonZeroDivisors ha hle
    have h1 := congrArg (X.presheaf.map (homOfLE (inf_le_left : O p ⊓ O q ≤ O p)).op) (hr p)
    have h2 := congrArg (X.presheaf.map (homOfLE (inf_le_right : O p ⊓ O q ≤ O q)).op) (hr q)
    rw [map_mul, Scheme.presheaf_map_map, Scheme.presheaf_map_map] at h1 h2
    have h3 : (X.presheaf.map (homOfLE (inf_le_left : O p ⊓ O q ≤ O p)).op (r p) -
        X.presheaf.map (homOfLE (inf_le_right : O p ⊓ O q ≤ O q)).op (r q)) *
        X.presheaf.map (homOfLE hle).op a = 0 := by
      rw [sub_mul, mul_comm, ← h1, mul_comm, ← h2, sub_self]
    exact sub_eq_zero.mp (mem_nonZeroDivisors_iff_right.mp hnzd _ h3)
  obtain ⟨s', hs, -⟩ := X.sheaf.existsUnique_gluing' O W (fun p ↦ homOfLE (hO p)) hcover r hcompat
  let s : Γ(X, W) := s'
  refine ⟨s, ?_⟩
  refine X.sheaf.eq_of_locally_eq' O W (fun p ↦ homOfLE (hO p)) hcover _ _ fun p ↦ ?_
  have hs' : X.presheaf.map (homOfLE (hO p)).op s = r p := hs p
  show X.presheaf.map (homOfLE (hO p)).op b =
    X.presheaf.map (homOfLE (hO p)).op (X.presheaf.map (homOfLE hW).op a * s)
  rw [map_mul, hs', Scheme.presheaf_map_map]
  exact hr p

end AlgebraicGeometry
