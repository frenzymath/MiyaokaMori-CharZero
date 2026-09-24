import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.GmLaurentIndependence

/-! # Section charts of `Spec A ×_k T` over affine opens of `T`

The section `GmChart` of `GmLaurentIndependence.lean` identifies, for `G_m = Spec k[λ^{±1}]`,
the open subscheme `pr₂⁻¹V ⊆ G_m ×_k T` with `Spec (k[λ^{±1}] ⊗_k Γ(T,V))`. That argument only uses
that `G_m` is a `Spec` whose structure morphism is `Spec.map (algebraMap)`; this file generalises
it verbatim to an arbitrary `k`-algebra `A`:

* `SpecChart.isPullback_preimage`: `(pr₂⁻¹V, ι ≫ pr₁, (pr₂ ∣_ V) ≫ isoSpec)` is the fibre product
  of `f` and `Spec Γ(T,V) → Spec k`;
* `SpecChart.isPullback_specTensor`: `Spec (A ⊗_k Γ(T,V))` is the same fibre product
  (`CommRingCat.isPushout_tensorProduct`);
* `SpecChart.preimageIsoSpecTensor`, its two component identities and two `appTop` identities;
* `SpecChart.pullback_sections_tensorEquiv`, the main theorem:
  `Γ(Spec A ×_k T, pr₂⁻¹V) ≃+* A ⊗_k Γ(T,V)`, sending `pr₂^♯(a)` to `1 ⊗ a` and
  `res(pr₁^♯(ΓSpecIso⁻¹ x))` to `x ⊗ 1`.

Applications: `A = k[X]` (the nonnegative chart of `WeightDecompositionPolynomialChart.lean`);
`A = k[λ^{±1}]` recovers `Gm_pullback_sections_tensorEquiv`.

Ingredients from Mathlib: `CommRingCat.isPushout_tensorProduct`, `isPullback_SpecMap_of_isPushout`,
and `isPullback_morphismRestrict` (base change of an open immersion).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace SpecChart

open AlgebraicGeometry

variable {k : Type u} [Field k] {T : Scheme.{u}}
  {A : Type u} [CommRing A] [Algebra k A]
  (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k))
  (q : T ⟶ Spec (CommRingCat.of k)) (V : T.Opens)

omit [Algebra k A] in
/-- The open subscheme `U = pr₂⁻¹V ⊆ Spec A ×_k T`, with `ι ≫ pr₁` and `(pr₂ ∣_ V) ≫ isoSpec`,
is the fibre product of `f` and `Spec Γ(T,V) → Spec k` (the generalisation of
`Gm.isPullback_preimage`, with the same proof). -/
theorem isPullback_preimage (hV : IsAffineOpen V) :
    letI := Gm.sectionsAlgebra q V
    IsPullback
      ((pullback.snd f q ⁻¹ᵁ V).ι ≫ pullback.fst f q)
      ((pullback.snd f q ∣_ V) ≫ hV.isoSpec.hom)
      f
      (Spec.map (CommRingCat.ofHom (algebraMap k Γ(T, V)))) := by
  letI := Gm.sectionsAlgebra q V
  have h1 := (isPullback_morphismRestrict (pullback.snd f q) V).flip.paste_horiz
    (IsPullback.of_hasPullback f q)
  refine h1.of_iso (Iso.refl _) (Iso.refl _) hV.isoSpec (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · simp [Gm.ι_comp_eq_isoSpec_hom_comp_specMap q V hV]

/-- `Spec (A ⊗_k Γ(T,V))`, with the two maps `Spec (include)`, is the same fibre product
(`CommRingCat.isPushout_tensorProduct`), provided `f = Spec (algebraMap k A)`. -/
theorem isPullback_specTensor (hf : f = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    letI := Gm.sectionsAlgebra q V
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          A →+* A ⊗[k] Γ(T, V))))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          Γ(T, V) →ₐ[k] A ⊗[k] Γ(T, V)).toRingHom))
      f
      (Spec.map (CommRingCat.ofHom (algebraMap k Γ(T, V)))) := by
  letI := Gm.sectionsAlgebra q V
  subst hf
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct k A Γ(T, V))

/-- The chart `U = pr₂⁻¹V ≅ Spec (A ⊗_k Γ(T,V))` (the canonical isomorphism between the two
fibre products). -/
def preimageIsoSpecTensor (hV : IsAffineOpen V)
    (hf : f = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    letI := Gm.sectionsAlgebra q V
    (pullback.snd f q ⁻¹ᵁ V).toScheme ≅ Spec (CommRingCat.of (A ⊗[k] Γ(T, V))) :=
  letI := Gm.sectionsAlgebra q V
  (isPullback_preimage f q V hV).isoIsPullback _ _ (isPullback_specTensor f q V hf)

theorem preimageIsoSpecTensor_hom_includeLeft (hV : IsAffineOpen V)
    (hf : f = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    letI := Gm.sectionsAlgebra q V
    (preimageIsoSpecTensor f q V hV hf).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          A →+* A ⊗[k] Γ(T, V))) =
      (pullback.snd f q ⁻¹ᵁ V).ι ≫ pullback.fst f q :=
  IsPullback.isoIsPullback_hom_fst _ _ (isPullback_preimage f q V hV) (isPullback_specTensor f q V hf)

theorem preimageIsoSpecTensor_hom_includeRight (hV : IsAffineOpen V)
    (hf : f = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    letI := Gm.sectionsAlgebra q V
    (preimageIsoSpecTensor f q V hV hf).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          Γ(T, V) →ₐ[k] A ⊗[k] Γ(T, V)).toRingHom) =
      (pullback.snd f q ∣_ V) ≫ hV.isoSpec.hom :=
  IsPullback.isoIsPullback_hom_snd _ _ (isPullback_preimage f q V hV) (isPullback_specTensor f q V hf)

/-- The chart on `x ⊗ 1`: `E^♯(x ⊗ 1) = (ι ≫ pr₁)^♯(ΓSpecIso⁻¹ x)`. -/
theorem preimageIsoSpecTensor_appTop_tmul_one (hV : IsAffineOpen V)
    (hf : f = Spec.map (CommRingCat.ofHom (algebraMap k A))) (x : A) :
    letI := Gm.sectionsAlgebra q V
    (preimageIsoSpecTensor f q V hV hf).hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (A ⊗[k] Γ(T, V)))).inv.hom (x ⊗ₜ[k] (1 : Γ(T, V)))) =
      ((pullback.snd f q ⁻¹ᵁ V).ι ≫ pullback.fst f q).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x) := by
  letI := Gm.sectionsAlgebra q V
  have h := congrArg (fun m : _ ⟶ Spec (CommRingCat.of A) =>
      m.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x))
    (preimageIsoSpecTensor_hom_includeLeft f q V hV hf)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h
  refine Eq.trans ?_ h
  congr 1
  exact (Gm.Spec_map_appTop_ΓSpecIso_inv (R := CommRingCat.of A)
    (S := CommRingCat.of (A ⊗[k] Γ(T, V)))
    (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) x).symm

/-- The chart on `1 ⊗ a`: `E^♯(1 ⊗ a) = ((pr₂ ∣_ V) ≫ isoSpec)^♯(ΓSpecIso⁻¹ a)`. -/
theorem preimageIsoSpecTensor_appTop_one_tmul (hV : IsAffineOpen V)
    (hf : f = Spec.map (CommRingCat.ofHom (algebraMap k A))) (a : Γ(T, V)) :
    letI := Gm.sectionsAlgebra q V
    (preimageIsoSpecTensor f q V hV hf).hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (A ⊗[k] Γ(T, V)))).inv.hom ((1 : A) ⊗ₜ[k] a)) =
      ((pullback.snd f q ∣_ V) ≫ hV.isoSpec.hom).appTop.hom
        ((Scheme.ΓSpecIso Γ(T, V)).inv.hom a) := by
  letI := Gm.sectionsAlgebra q V
  have h := congrArg (fun m : _ ⟶ Spec Γ(T, V) =>
      m.appTop.hom ((Scheme.ΓSpecIso Γ(T, V)).inv.hom a))
    (preimageIsoSpecTensor_hom_includeRight f q V hV hf)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h
  refine Eq.trans ?_ h
  congr 1
  exact (Gm.Spec_map_appTop_ΓSpecIso_inv (R := Γ(T, V))
    (S := CommRingCat.of (A ⊗[k] Γ(T, V)))
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      Γ(T, V) →ₐ[k] A ⊗[k] Γ(T, V)).toRingHom) a).symm

/-- **The general chart**: over an affine open `V ⊆ T`, the ring of sections `Γ(pr₂⁻¹V)` of
`Spec A ×_k T` is `A ⊗_k Γ(T,V)`: there is a ring isomorphism `e` sending `pr₂^♯(a)` to `1 ⊗ a`
and `res(pr₁^♯(ΓSpecIso⁻¹ x))` to `x ⊗ 1` (for all `x ∈ A`).
Hypothesis: `f = Spec (algebraMap k A)` (for `Spec A ↘ Spec k` this is `specOverSpec_over`).

The proof is the same as for `Gm_pullback_sections_tensorEquiv` (see steps (1)–(5) of its
docstring), with `G_m` replaced by `Spec A`: `e⁻¹ := ΓSpecIso⁻¹ ≫ E^♯ ≫ U.topIso`, and the two
compatibilities reduce to the identities of morphisms
`ΓSpecIso⁻¹ ≫ ((pr₂ ∣_ V) ≫ isoSpec)^♯ ≫ topIso = pr₂.appLE V U` (`Scheme.Opens.toSpecΓ_naturality`)
and `ι^♯ ≫ topIso = ` the restriction `Γ(W,⊤) → Γ(W,U)` (`Scheme.Opens.ι_appTop`, `topIso_hom`).
Edge case: for `V = ⊥` both sides are the zero ring. -/
theorem pullback_sections_tensorEquiv (hV : IsAffineOpen V)
    (hf : f = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    letI := Gm.sectionsAlgebra q V
    ∃ e : Γ(pullback f q, pullback.snd f q ⁻¹ᵁ V) ≃+* (A ⊗[k] Γ(T, V)),
      (∀ a : Γ(T, V), e ((pullback.snd f q).appLE V _ le_rfl |>.hom a) = (1 : A) ⊗ₜ[k] a) ∧
      ∀ x : A, e (((pullback f q).presheaf.map (homOfLE le_top).op).hom
          ((pullback.fst f q).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x))) =
        x ⊗ₜ[k] (1 : Γ(T, V)) := by
  letI := Gm.sectionsAlgebra q V
  let E := preimageIsoSpecTensor f q V hV hf
  haveI : IsIso E.hom.appTop := inferInstanceAs (IsIso (E.hom.app ⊤))
  let eInv :=
    ((Scheme.ΓSpecIso (CommRingCat.of (A ⊗[k] Γ(T, V)))).symm ≪≫
      asIso E.hom.appTop ≪≫ (pullback.snd f q ⁻¹ᵁ V).topIso).commRingCatIsoToRingEquiv
  have heInv : ∀ t, eInv t = (pullback.snd f q ⁻¹ᵁ V).topIso.hom.hom
      (E.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (A ⊗[k] Γ(T, V)))).inv.hom t)) :=
    fun t => rfl
  refine ⟨eInv.symm, ?_, ?_⟩
  · intro a
    have keyA : (Scheme.ΓSpecIso Γ(T, V)).inv ≫
        ((pullback.snd f q ∣_ V) ≫ hV.isoSpec.hom).appTop ≫ (pullback.snd f q ⁻¹ᵁ V).topIso.hom =
        (pullback.snd f q).appLE V _ le_rfl := by
      rw [IsAffineOpen.isoSpec_hom, ← Scheme.Opens.toSpecΓ_naturality,
        Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc, Scheme.Hom.app_eq_appLE]
    rw [RingEquiv.symm_apply_eq, heInv, preimageIsoSpecTensor_appTop_one_tmul, ← keyA]
    rfl
  · intro x
    have keyB : (pullback.snd f q ⁻¹ᵁ V).ι.appTop ≫ (pullback.snd f q ⁻¹ᵁ V).topIso.hom =
        (pullback f q).presheaf.map (homOfLE le_top).op := by
      rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
      erw [← Functor.map_comp]
      congr 1
    rw [RingEquiv.symm_apply_eq, heInv, preimageIsoSpecTensor_appTop_tmul_one, ← keyB]
    rfl

end SpecChart

end
