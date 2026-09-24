import MiyaokaMori.Prelude

/-! # Restriction of a nonzerodivisor

Let `V` be an affine open of a scheme `X` and `a ∈ Γ(X, V)` a nonzerodivisor. Then for every open
`W ≤ V`, the restriction `a|_W` is a nonzerodivisor of `Γ(X, W)` (i.e. `O_V →a O_V` is a monomorphism
of sheaves). The local equation of a Cartier divisor is only given on an affine open; this lemma allows
using it on smaller opens that need not be affine or basic. Proof: `W` is covered by basic opens
`D(f) ⊆ W` of `V`, `Γ(D(f)) = Γ(V)_f` is a localization, nonzerodivisors are preserved by localization,
and then the sheaf property of `O_X`. See the remark after Stacks 01WQ.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A nonzerodivisor on an affine open restricts to a nonzerodivisor on any smaller open. -/
theorem IsAffineOpen.res_mem_nonZeroDivisors {V : X.Opens} (hV : IsAffineOpen V) {a : Γ(X, V)}
    (ha : a ∈ nonZeroDivisors Γ(X, V)) {W : X.Opens} (h : W ≤ V) :
    X.presheaf.map (homOfLE h).op a ∈ nonZeroDivisors Γ(X, W) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro t ht
  have key : ∀ p : W, ∃ (O : X.Opens) (i : O ⟶ W), p.1 ∈ O ∧
      X.presheaf.map i.op t = X.presheaf.map i.op 0 := by
    rintro ⟨p, hp⟩
    obtain ⟨f, hfW, hpf⟩ := hV.exists_basicOpen_le ⟨p, hp⟩ (h hp)
    refine ⟨X.basicOpen f, homOfLE hfW, hpf, ?_⟩
    have := hV.isLocalization_basicOpen f
    have hnzd : algebraMap Γ(X, V) Γ(X, X.basicOpen f) a ∈ nonZeroDivisors Γ(X, X.basicOpen f) :=
      IsLocalization.map_nonZeroDivisors_le (Submonoid.powers f) Γ(X, X.basicOpen f)
        (Submonoid.mem_map_of_mem _ ha)
    rw [map_zero]
    apply (mem_nonZeroDivisors_iff_right.mp hnzd)
    have e : algebraMap Γ(X, V) Γ(X, X.basicOpen f) a =
        X.presheaf.map (homOfLE hfW).op (X.presheaf.map (homOfLE h).op a) := by
      rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]; rfl
    rw [e, ← map_mul, ht, map_zero]
  choose O i hpO hO using key
  exact X.sheaf.eq_of_locally_eq' O W i
    (fun p hp => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hpO _⟩) t 0 hO

end AlgebraicGeometry
