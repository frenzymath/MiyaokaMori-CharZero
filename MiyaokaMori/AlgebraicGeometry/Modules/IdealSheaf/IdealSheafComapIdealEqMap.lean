import MiyaokaMori.Prelude

/-! # Affine local formula for inverse image ideal sheaves

For `f : X → Y`, an affine open `U ⊆ Y` and an affine open `V ⊆ f⁻¹U`, one has
`(f⁻¹I·O_X)(V) = I(U)·Γ(V, O_X)`.

References: Stacks 01HQ (the inverse image of a closed subscheme is the fibre product, with ideal
`Im(f^*I → O_X)`); Hartshorne II p.163 (the notation `f⁻¹I·O_X`).

Route: no fibre-product computation `Spec B ×_{Spec A} Spec(A/𝔞)` is needed.
Write `p = pullback.fst f I.subschemeι`, so `I.comap f = p.ker`.
* `⊇`: `𝔞·B ⊆ ker(Γ(p))` because `Γ(p) ∘ Γ(f) = Γ(p ≫ f) = Γ(q ≫ I.subschemeι)` kills `𝔞 = ker Γ(I.subschemeι)`
  (`pullback.condition`, `ker_subschemeι_app`).
* `⊆`: restrict to `f|_V : V ⟶ U` (both affine) and use the Galois connection
  `J ≤ K.map g ↔ J.comap g ≤ K` (`le_map_iff_comap_le`) with `K = ofIdealTop (𝔞·B)`:
  `J ≤ K.map g` holds on affine `U` since `(K.map g)(U) = Γ(g)⁻¹(𝔞·B) ⊇ 𝔞` (`ker_of_isAffine`, `Ideal.le_comap_map`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Affine core of `comap_ideal_eq_map_appLE`, inequality `⊆`: for `g : X ⟶ Y` between affine
schemes and `J` an ideal sheaf on `Y` with `𝔞 = J(Y)`, one has `(J.comap g)(X) ⊆ 𝔞·Γ(X)`.

Proof: let `K := ofIdealTop (𝔞·Γ(X))`. By the Galois connection `J ≤ K.map g ↔ J.comap g ≤ K`
(`le_map_iff_comap_le`) it suffices to show `J ≤ K.map g`; on the affine `Y` this is
`le_of_isAffine` from `𝔞 ≤ ((K.subschemeι ≫ g).ker)(Y) = ker(Γ(g) ≫ Γ(K.subschemeι)) = Γ(g)⁻¹(𝔞·Γ(X))`
(`ker_of_isAffine`, `ker_subschemeι_app`), which is `Ideal.le_comap_map`. -/
theorem comap_ideal_top_le_map_appTop {X Y : AlgebraicGeometry.Scheme.{u}} [IsAffine X] [IsAffine Y]
    (J : Y.IdealSheafData) (g : X ⟶ Y) :
    (J.comap g).ideal ⟨⊤, isAffineOpen_top X⟩ ≤
      (J.ideal ⟨⊤, isAffineOpen_top Y⟩).map g.appTop.hom := by
  set 𝔟 : Ideal Γ(X, ⊤) := (J.ideal ⟨⊤, isAffineOpen_top Y⟩).map g.appTop.hom with h𝔟
  have hker : RingHom.ker ((ofIdealTop 𝔟).subschemeι.appTop).hom = 𝔟 :=
    ((ofIdealTop 𝔟).ker_subschemeι_app ⟨⊤, isAffineOpen_top X⟩).trans (by simp)
  have hK : J.comap g ≤ ofIdealTop 𝔟 := by
    rw [← le_map_iff_comap_le]
    refine le_of_isAffine ?_
    rw [map, ker_of_isAffine, ofIdealTop_ideal, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      ← RingHom.comap_ker, hker]
    simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id,
      Ideal.map_id]
    exact Ideal.le_comap_map
  simpa using hK ⟨⊤, isAffineOpen_top X⟩

/-- Transport along `V.topIso : Γ(V, ⊤) ≅ Γ(X, V)`: the global value of `I.comap V.ι` on the affine
open subscheme `V` is `I(V)` (`ideal_comap_of_isOpenImmersion`, `Opens.ι_appIso`, `map_ideal'`). -/
theorem map_topIso_ideal_comap_ι_top {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData)
    (V : X.affineOpens) :
    ((I.comap V.1.ι).ideal ⟨⊤, isAffineOpen_top V.1.toScheme⟩).map V.1.topIso.hom.hom =
      I.ideal V := by
  rw [ideal_comap_of_isOpenImmersion I V.1.ι, Opens.ι_appIso, Iso.refl_inv]
  erw [Ideal.comap_id]
  rw [Scheme.Opens.topIso_hom]
  exact I.map_ideal' (U := V) (V := ⟨V.1.ι ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion _⟩)
    (eqToHom V.1.ι_image_top.symm).op

/-- `(I.comap f)(V)` is the extension of `I(U)` along `f.appLE U V`.

Proof sketch (see the module docstring): `I.comap f` is `(pullback.fst f I.subschemeι).ker`.
`⊇`: `𝔞·B ⊆ ker Γ(p)` since `Γ(p) ∘ Γ(f) = Γ(q ≫ I.subschemeι)` kills `𝔞 = ker Γ(I.subschemeι)`
(`pullback.condition`, `ker_subschemeι_app`, `appLE_comp_appLE`, `comp_appLE`).
`⊆`: reduce along `f.resLE U V e : V ⟶ U` to the affine case `comap_ideal_top_le_map_appTop`,
then transport back to `Γ(X, V)`, `Γ(Y, U)` with `map_topIso_ideal_comap_ι_top`.
Note that `f.appLE U V e` needs `e : V ≤ f ⁻¹ᵁ U`. -/
theorem comap_ideal_eq_map_appLE
    {X Y : AlgebraicGeometry.Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE U.1 V.1 e).hom := by
  apply le_antisymm
  · -- ⊆ : reduce to the affine core along `f.resLE U V e : V ⟶ U`.
    have core := comap_ideal_top_le_map_appTop (I.comap U.1.ι) (f.resLE U.1 V.1 e)
    rw [← comap_comp, Scheme.Hom.resLE_comp_ι, comap_comp] at core
    have h3 : (f.resLE U.1 V.1 e).appTop = U.1.topIso.hom ≫ f.appLE U.1 V.1 e ≫ V.1.topIso.inv :=
      Scheme.Hom.resLE_app_top f e
    have h2 := Ideal.map_mono (f := V.1.topIso.hom.hom) core
    rw [map_topIso_ideal_comap_ι_top, Ideal.map_map, ← CommRingCat.hom_comp, h3,
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      CommRingCat.hom_comp, ← Ideal.map_map, map_topIso_ideal_comap_ι_top] at h2
    exact h2
  · -- ⊇ : elementwise, via `pullback.condition`.
    have hqc : QuasiCompact (pullback.fst f I.subschemeι) := inferInstance
    rw [comap, Scheme.Hom.ker_apply, Ideal.map_le_iff_le_comap]
    intro x hx
    have h1 : (I.subschemeι.app U).hom x = 0 := by
      rw [← RingHom.mem_ker, I.ker_subschemeι_app U]; exact hx
    have key : ∀ (g : pullback f I.subschemeι ⟶ Y)
        (e' : (pullback.fst f I.subschemeι) ⁻¹ᵁ V.1 ≤ g ⁻¹ᵁ U.1),
        g = pullback.snd f I.subschemeι ≫ I.subschemeι →
        (g.appLE U.1 _ e').hom x = 0 := by
      rintro g e' rfl
      rw [Scheme.Hom.comp_appLE, CommRingCat.hom_comp, RingHom.comp_apply, h1, map_zero]
    rw [Ideal.mem_comap, RingHom.mem_ker, (pullback.fst f I.subschemeι).app_eq_appLE,
      ← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
    exact key _ _ pullback.condition

end AlgebraicGeometry.Scheme.IdealSheafData

end
