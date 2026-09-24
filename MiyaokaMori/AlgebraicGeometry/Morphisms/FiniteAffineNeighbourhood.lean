import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks02rm

/-! # Affine neighbourhoods over which a proper generically finite morphism is finite

Let `X`, `Y` be integral schemes with `Y` locally Noetherian, and `p : X → Y` proper, mapping the
generic point to the generic point, with finite extension of function fields. Let `z ∈ Y` with
`dim O_{Y,z} = 1`. Then there is an affine open neighbourhood `U` of `z` such that `p⁻¹U` is an
affine open and `Γ(Y,U) → Γ(X,p⁻¹U)` is finite.

Proof:
1. `exists_isFinite_restrict_of_dim_one` (Stacks Project, Tag 02RM) gives an open `V ∋ z` over which
   `p∣_V` is finite. Choose an affine open `U ⊆ V` with `z ∈ U` (affine opens form a basis).
2. Finiteness is local on the target: `(p∣_V)∣_{V.ι⁻¹U}` is finite
   (`IsZariskiLocalAtTarget.restrict`), and via `morphismRestrictRestrict` and
   `V.ι''(V.ι⁻¹U) = V ∩ U = U` we get that `p∣_U` is finite (`isFinite_morphismRestrict_of_le`).
3. `p∣_U : p⁻¹U → U` finite and `U` affine imply `p⁻¹U` affine (`isAffine_of_isAffineHom`);
   `IsFinite.finite_app` on `⊤` gives finiteness, and `morphismRestrict_app` together with
   `Scheme.Opens.ι_image_top` reduce it to `p.app U`
   (`isAffineOpen_preimage_and_finite_app_of_isFinite`).
References: the first paragraph of the proof of Stacks Project, Tag 02RT; Tag 02RM.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
theorem isFinite_morphismRestrict_of_le {X Y : Scheme.{u}} (p : X ⟶ Y) {U V : Y.Opens}
    (hUV : U ≤ V) [IsFinite (p ∣_ V)] : IsFinite (p ∣_ U) := by
  have h1 : IsFinite (p ∣_ V ∣_ (V.ι ⁻¹ᵁ U)) := inferInstance
  have h2 : IsFinite (p ∣_ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U))) :=
    ((MorphismProperty.arrow_mk_iso_iff @IsFinite (morphismRestrictRestrict p V _))).mp h1
  have h3 : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hUV
  rwa [h3] at h2

set_option backward.isDefEq.respectTransparency.types false in
theorem isAffineOpen_preimage_and_finite_app_of_isFinite {X Y : Scheme.{u}} (p : X ⟶ Y)
    {U : Y.Opens} (hU : IsAffineOpen U) [IsFinite (p ∣_ U)] :
    IsAffineOpen (p ⁻¹ᵁ U) ∧ (p.app U).hom.Finite := by
  have : IsAffine U.toScheme := hU
  refine ⟨isAffine_of_isAffineHom (p ∣_ U), ?_⟩
  have h := IsFinite.finite_app (p ∣_ U) ⊤ (isAffineOpen_top _)
  rw [Scheme.Hom.app_eq_appLE, morphismRestrict_appLE] at h
  rw [Scheme.Hom.app_eq_appLE]
  exact (Scheme.Hom.appLE_congr p _ (Scheme.Opens.ι_image_top U) (by simp)
    (fun f => f.hom.Finite)).mp h

theorem exists_affine_finite_neighbourhood {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] (p : X ⟶ Y) [IsProper p]
    (hp : p.base (genericPoint X) = genericPoint Y)
    (hfin : (p.residueFieldMap (genericPoint X)).hom.Finite) (z : Y)
    (hz : ringKrullDim (Y.presheaf.stalk z) = 1) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ z ∈ U ∧ IsAffineOpen (p ⁻¹ᵁ U) ∧ (p.app U).hom.Finite := by
  obtain ⟨V, hzV, hV⟩ := exists_isFinite_restrict_of_dim_one p hp hfin z hz
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, hUV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hzV V.2
  have := isFinite_morphismRestrict_of_le p (U := U) (V := V) hUV
  exact ⟨U, hU, hzU, isAffineOpen_preimage_and_finite_app_of_isFinite p hU⟩

end AlgebraicGeometry

end
