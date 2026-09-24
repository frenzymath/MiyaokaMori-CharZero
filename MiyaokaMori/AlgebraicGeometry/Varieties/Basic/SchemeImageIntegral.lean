import MiyaokaMori.Prelude

/-! # The scheme-theoretic image of an integral scheme is integral

If `X` is an integral scheme and `f : X ⟶ Y` is quasi-compact, then the scheme-theoretic image
`f.image` (Mathlib's `Scheme.Hom.image = f.ker.subscheme`) is an integral scheme
(standard; compare Stacks 01R8, 056B).

Proof sketch.
1. Reduced: for `x ∈ f.image`, `Scheme.Hom.stalkFunctor_toImage_injective` gives an injection of
   the stalk `O_{image,x}` into the stalk at `x` of the pushforward presheaf `(toImage)_* O_X`;
   the latter is a filtered colimit of the reduced rings `Γ(X, toImage⁻¹U)`, hence reduced (if the
   germ of `sⁿ` is `0` then `(s|_W)ⁿ = 0` on some neighbourhood `W`, so `s|_W = 0`). A ring that
   injects into a reduced ring is reduced (`isReduced_of_injective`); conclude with
   `isReduced_of_isReduced_stalk`.
2. Irreducible: `f.toImage` is dominant, `X` is irreducible, and the closure of the image of an
   irreducible space under a continuous map is irreducible.
3. `isIntegral_of_irreducibleSpace_of_isReduced`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

noncomputable section

/-- A presheaf of commutative rings all of whose section rings are reduced has reduced stalks. -/
theorem TopCat.Presheaf.isReduced_stalk_of_isReduced_obj {T : TopCat.{u}}
    (F : TopCat.Presheaf CommRingCat.{u} T) (hF : ∀ U : Opens T, _root_.IsReduced (F.obj (op U)))
    (x : T) : _root_.IsReduced (F.stalk x) := by
  refine ⟨fun s hs => ?_⟩
  obtain ⟨n, hn⟩ := hs
  obtain ⟨U, hxU, t, rfl⟩ := F.exists_germ_eq s
  have h0 : F.germ U x hxU (t ^ n) = F.germ U x hxU 0 := by
    rw [map_pow, hn, map_zero]
  obtain ⟨W, hxW, iU, iV, h⟩ := F.germ_eq x hxU hxU _ _ h0
  rw [map_pow, map_zero] at h
  have hW := hF W
  have h1 : F.map iU.op t = 0 := IsReduced.eq_zero _ ⟨n, h⟩
  rw [← F.germ_res_apply iU x hxW t, h1, map_zero]

/-- The scheme-theoretic image of a quasi-compact morphism from an integral scheme is integral. -/
theorem AlgebraicGeometry.Scheme.Hom.isIntegral_image {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [QuasiCompact f] : IsIntegral f.image := by
  have hred : IsReduced f.image := by
    have : ∀ x : f.image, _root_.IsReduced (f.image.presheaf.stalk x) := fun x => by
      have h := TopCat.Presheaf.isReduced_stalk_of_isReduced_obj
        (f.toImage.base _* X.presheaf) (fun U => by dsimp; infer_instance) x
      exact @isReduced_of_injective _ _ _ _ _ _ _ _ (f.stalkFunctor_toImage_injective x) h
    exact isReduced_of_isReduced_stalk _
  have hirr : IrreducibleSpace f.image := by
    have hd : DenseRange f.toImage.base := f.toImage.denseRange
    have := (IrreducibleSpace.isIrreducible_univ X).image f.toImage.base
      f.toImage.continuous.continuousOn
    rw [Set.image_univ] at this
    have h2 := this.closure
    rw [hd.closure_range] at h2
    exact { toPreirreducibleSpace := ⟨h2.2⟩, toNonempty := ⟨h2.1.some⟩ }
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end
