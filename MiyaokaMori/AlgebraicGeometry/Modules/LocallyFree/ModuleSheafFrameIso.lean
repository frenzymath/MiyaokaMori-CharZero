import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrame

/-! # Frames under isomorphisms of sheaves of modules

For a scheme `X` and an isomorphism `e : M ≅ N` of `O_X`-modules: if `x` is a frame of `M` on `W`,
then `e(x)` is a frame of `N` on `W`; if `y` is another frame of `N` on `W`, there is a unit
`u ∈ Γ(X, W)^×` with `u • y = e(x)`.

Proof: for `W' ⊆ W`, `r ↦ r • (e x)|_{W'}` equals `e_{W'} ∘ (r ↦ r • x|_{W'})` (`e` commutes with
restriction and scalar multiplication), and `e_{W'}` is a bijection (inverse `e.inv`); two frames of
the same sheaf differ by a unit (`IsFrame.exists_unit`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} {M N : X.Modules}

/-- A morphism of sheaves of modules commutes with restriction (elementwise form). -/
theorem Hom.app_res (φ : M ⟶ N) {W' W : X.Opens} (h : W' ≤ W) (x : Γ(M, W)) :
    φ.app W' (M.res h x) = N.res h (φ.app W x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x

theorem Iso.app_bijective (e : M ≅ N) (W : X.Opens) : Function.Bijective (e.hom.app W) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨e.inv.app W, fun x => ?_, fun y => ?_⟩
  · exact congrArg (fun φ : M ⟶ M => φ.app W x) e.hom_inv_id
  · exact congrArg (fun φ : N ⟶ N => φ.app W y) e.inv_hom_id

/-- An isomorphism sends frames to frames. -/
theorem IsFrame.map_iso {W : X.Opens} {x : Γ(M, W)} (hf : IsFrame M W x) (e : M ≅ N) :
    IsFrame N W (e.hom.app W x) := by
  intro W' h
  have hfun : (fun r : Γ(X, W') => r • N.res h (e.hom.app W x)) =
      (e.hom.app W') ∘ (fun r : Γ(X, W') => r • M.res h x) := by
    funext r
    rw [← Hom.app_res]
    exact (Hom.app_smul e.hom r (M.res h x)).symm
  rw [hfun]
  exact (Iso.app_bijective e W').comp (hf W' h)

/-- Under an isomorphism, two frames differ by a unit. -/
theorem IsFrame.exists_unit_of_iso {W : X.Opens} {x : Γ(M, W)} {y : Γ(N, W)}
    (hf : IsFrame M W x) (hf' : IsFrame N W y) (e : M ≅ N) :
    ∃ u : (Γ(X, W))ˣ, (u : Γ(X, W)) • y = e.hom.app W x :=
  hf'.exists_unit (hf.map_iso e)

end AlgebraicGeometry.Scheme.Modules

end
