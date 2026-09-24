import MiyaokaMori.Prelude

/-! # Injectivity on sections of a base-changed morphism of affine schemes

Injectivity on sections of a base-changed morphism of affine `R`-schemes over an affine open.

Setting: `R`-algebras `S`, `S'`, an `R`-algebra map `φ : S → S'`, a scheme `X` over `Spec R`
(`p : X ⟶ Spec R`), and the morphism
`J := Spec φ ×_R 𝟙_X : Spec S' ×_R X ⟶ Spec S ×_R X`.  For an affine open `V ⊆ X` (modelled by
`ι : Spec A ⟶ X` with `ι ⁻¹ᵁ V = ⊤`, e.g. `ι = hV.fromSpec`) the map `J^♯` on sections over
`pr₂⁻¹V` is injective as soon as `φ ⊗ id_A : S ⊗_R A → S' ⊗_R A` is injective.

Proof (Stacks 01JQ / 01HR-type bookkeeping, all in Mathlib's pullback API):
1. Let `P := Spec S ×_R X`, `W := pr₂⁻¹V`, `P_V := Spec S ×_R Spec A ≅ Spec (S ⊗_R A)`
   (`pullbackSpecIso`), `u := pullback.map (𝟙) ι (𝟙) : P_V ⟶ P`; similarly `Q, Q_V, u'` for `S'`.
2. The square `u' ≫ J = J_V ≫ u` with `J_V = Spec (φ ⊗ id)` holds after composing with the
   pullback isos (`pullback.hom_ext`, `pullbackSpecIso_inv_fst/snd`, `Spec.map_comp`,
   `Algebra.TensorProduct.map_comp_includeLeft/Right`).  Hence, on sections,
   `Ψ_G ∘ J^♯ = (φ ⊗ id) ∘ Ψ_A` where `Ψ_A : Γ(P, W) → S ⊗_R A` is
   `(pullbackSpecIso.inv ≫ u)^♯` followed by `ΓSpecIso`, and likewise `Ψ_G`.
3. `Ψ_A` is injective: the open subscheme `W` maps to `P_V` (via `W.ι ≫ pr₁` and a given
   `zA : W ⟶ Spec A` with `zA ≫ ι = W.ι ≫ pr₂`), and the composite `W ⟶ P_V ⟶ P` is `W.ι`, whose
   `appLE W ⊤` is the restriction iso `Γ(P, W) ≅ Γ(W, ⊤)`.  So `u^♯ : Γ(P, W) → Γ(P_V, ⊤)` has an
   injective composite, hence is injective.
4. `J^♯ b = 0 ⇒ (φ ⊗ id)(Ψ_A b) = Ψ_G (J^♯ b) = 0 ⇒ Ψ_A b = 0 ⇒ b = 0`.

For `R = k` a field every `k`-module is flat, so `φ ⊗ id_A` is injective whenever `φ` is
(`tensorProduct_map_id_injective_of_field`).

Edge cases: `V = ⊥` (then `W = ⊥`, `Γ(P, W)` is the zero ring, statement trivial); `X = ∅`; zero
rings `S`, `S'`, `A` (all maps between zero rings are injective).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry

/-- Over a field `k`, `φ ⊗ id_A : S ⊗_k A → S' ⊗_k A` is injective whenever `φ` is
(every `k`-module is free, hence flat). -/
theorem tensorProduct_map_id_injective_of_field {k S S' A : Type u} [Field k] [CommRing S]
    [CommRing S'] [CommRing A] [Algebra k S] [Algebra k S'] [Algebra k A] (φ : S →ₐ[k] S')
    (hφ : Function.Injective φ) :
    Function.Injective (Algebra.TensorProduct.map φ (AlgHom.id k A)) := by
  have h : ⇑(Algebra.TensorProduct.map φ (AlgHom.id k A)) =
      ⇑(LinearMap.rTensor A φ.toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a => simp [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [h]
  exact Module.Flat.rTensor_preserves_injective_linearMap _ hφ

/-- `f.appLE W ⊤` is injective as soon as some composite `(w ≫ f).appLE W ⊤` is. -/
theorem Scheme.Hom.appLE_top_injective_of_comp {Z Y P : Scheme.{u}} (f : Y ⟶ P) (w : Z ⟶ Y)
    (W : P.Opens) (hW : ⊤ ≤ f ⁻¹ᵁ W) (hW' : ⊤ ≤ (w ≫ f) ⁻¹ᵁ W)
    (hinj : Function.Injective ((w ≫ f).appLE W ⊤ hW').hom) :
    Function.Injective (f.appLE W ⊤ hW).hom := by
  have h : (w ≫ f).appLE W ⊤ hW' = f.appLE W ⊤ hW ≫ w.appLE ⊤ ⊤ (by simp) :=
    (Scheme.Hom.appLE_comp_appLE w f W ⊤ ⊤ hW (by simp)).symm
  rw [h, CommRingCat.hom_comp, RingHom.coe_comp] at hinj
  exact hinj.of_comp

/-- The restriction `Γ(P, W) → Γ(W, ⊤)` (as `W.ι.appLE W ⊤`) is injective (it is `W.topIso.inv`). -/
theorem Scheme.Opens.ι_appLE_top_injective {P : Scheme.{u}} (W : P.Opens) (e : ⊤ ≤ W.ι ⁻¹ᵁ W) :
    Function.Injective (W.ι.appLE W ⊤ e).hom := by
  have h : W.ι.appLE W ⊤ e = W.topIso.inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    congr 1
  rw [h]
  exact (ConcreteCategory.bijective_of_isIso W.topIso.inv).1

/-- `appLE` depends only on the morphism (up to the transported proof). -/
theorem Scheme.Hom.appLE_congr_hom_transport {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens)
    (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

section Generic

variable {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']

/-- The `R`-algebra structure on `Γ(X, V)` (for `V` affine) whose `Spec` is `hV.fromSpec ≫ p`. -/
@[instance_reducible] def IsAffineOpen.specAlgebra {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    (p : X ⟶ Spec (CommRingCat.of R)) : Algebra R Γ(X, V) :=
  (Spec.preimage (hV.fromSpec ≫ p)).hom.toAlgebra

theorem IsAffineOpen.Spec_map_algebraMap_specAlgebra {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) (p : X ⟶ Spec (CommRingCat.of R)) :
    letI := hV.specAlgebra p
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, V))) = hV.fromSpec ≫ p := by
  let _ := hV.specAlgebra p
  show Spec.map (CommRingCat.ofHom (Spec.preimage (hV.fromSpec ≫ p)).hom) = _
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

/-- If `f ≫ pr₂ = g ≫ ι` and `ι ⁻¹ᵁ V = ⊤`, then `f ⁻¹ᵁ (pr₂ ⁻¹ᵁ V) = ⊤`. -/
theorem preimage_pullback_snd_preimage_eq_top {X Y Z T : Scheme.{u}} (q : Y ⟶ X)
    (ι : Z ⟶ X) (V : X.Opens) (hιV : ι ⁻¹ᵁ V = ⊤) (f : T ⟶ Y) (g : T ⟶ Z)
    (hf : f ≫ q = g ≫ ι) : f ⁻¹ᵁ (q ⁻¹ᵁ V) = ⊤ := by
  rw [← Scheme.Hom.comp_preimage, hf, Scheme.Hom.comp_preimage, hιV, Scheme.Hom.preimage_top]

/-- **Injectivity of `(Spec φ ×_R 𝟙_X)^♯` over an affine open.**  See the module docstring.
`W` is the open `pr₂⁻¹V` (kept as a variable with `hWdef` so that `W.toScheme` can be used). -/
theorem pullback_map_Spec_app_injective_of_affine (φ : S →ₐ[R] S') {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of R)) (V : X.Opens)
    {A : Type u} [CommRing A] [Algebra R A] (ι : Spec (CommRingCat.of A) ⟶ X)
    (hι : Spec.map (CommRingCat.ofHom (algebraMap R A)) = ι ≫ p) (hιV : ι ⁻¹ᵁ V = ⊤)
    (W : (pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) p).Opens)
    (hWdef : W = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S))) p ⁻¹ᵁ V)
    (zA : W.toScheme ⟶ Spec (CommRingCat.of A))
    (hz : zA ≫ ι = W.ι ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S))) p)
    (hmap : Function.Injective (Algebra.TensorProduct.map φ (AlgHom.id R A)))
    (e₁ : Spec.map (CommRingCat.ofHom (algebraMap R S')) ≫ 𝟙 (Spec (CommRingCat.of R)) =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (e₂ : p ≫ 𝟙 (Spec (CommRingCat.of R)) = 𝟙 X ≫ p) :
    Function.Injective
      ((pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R S'))) p
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) p
          (Spec.map (CommRingCat.ofHom φ.toRingHom)) (𝟙 X) (𝟙 _) e₁ e₂).app W).hom := by
  set J := pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R S'))) p
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) p
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) (𝟙 X) (𝟙 _) e₁ e₂ with hJ
  -- the affine models over `Spec A`
  let u : pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) p :=
    pullback.map _ _ _ _ (𝟙 _) ι (𝟙 _) (by simp) (by rw [Category.comp_id, hι])
  let u' : pullback (Spec.map (CommRingCat.ofHom (algebraMap R S')))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R S'))) p :=
    pullback.map _ _ _ _ (𝟙 _) ι (𝟙 _) (by simp) (by rw [Category.comp_id, hι])
  let ψ : CommRingCat.of (S ⊗[R] A) ⟶ CommRingCat.of (S' ⊗[R] A) :=
    CommRingCat.ofHom (Algebra.TensorProduct.map φ (AlgHom.id R A)).toRingHom
  -- the key square
  have key : (pullbackSpecIso R S' A).inv ≫ u' ≫ J = Spec.map ψ ≫ (pullbackSpecIso R S A).inv ≫ u := by
    apply pullback.hom_ext
    · simp only [u, u', hJ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Category.comp_id, pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
      congr 1
    · simp only [u, u', hJ, Category.assoc, pullback.lift_snd, Category.comp_id,
        pullbackSpecIso_inv_snd_assoc, ← Spec.map_comp_assoc]
      congr 2
      ext a
      simp [ψ]
  -- compatibilities with the projections
  have hJsnd : J ≫ pullback.snd _ p = pullback.snd _ p :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hu_fst : u ≫ pullback.fst _ p = pullback.fst _ _ ≫ 𝟙 _ := pullback.lift_fst _ _ _
  have hu : u ≫ pullback.snd _ p = pullback.snd _ _ ≫ ι := pullback.lift_snd _ _ _
  have hu' : u' ≫ pullback.snd _ p = pullback.snd _ _ ≫ ι := pullback.lift_snd _ _ _
  -- the model morphisms `Spec (S ⊗ A) ⟶ P`, `Spec (S' ⊗ A) ⟶ Q`
  let mA := (pullbackSpecIso R S A).inv ≫ u
  let mG := (pullbackSpecIso R S' A).inv ≫ u'
  have hmA : mA ⁻¹ᵁ W = ⊤ := by
    rw [hWdef]
    exact preimage_pullback_snd_preimage_eq_top _ ι V hιV mA
      ((pullbackSpecIso R S A).inv ≫ pullback.snd _ _) (by simp only [mA, Category.assoc, hu])
  have hmG : mG ⁻¹ᵁ (J ⁻¹ᵁ W) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, hWdef]
    exact preimage_pullback_snd_preimage_eq_top _ ι V hιV (mG ≫ J)
      ((pullbackSpecIso R S' A).inv ≫ pullback.snd _ _)
      (by simp only [mG, Category.assoc, hJsnd, hu'])
  -- sections-level comparison maps
  let ΨA : Γ(pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) p, W) ⟶
      CommRingCat.of (S ⊗[R] A) :=
    mA.appLE W ⊤ hmA.ge ≫ (Scheme.ΓSpecIso _).hom
  let ΨG : Γ(pullback (Spec.map (CommRingCat.ofHom (algebraMap R S'))) p, J ⁻¹ᵁ W) ⟶
      CommRingCat.of (S' ⊗[R] A) :=
    mG.appLE (J ⁻¹ᵁ W) ⊤ hmG.ge ≫ (Scheme.ΓSpecIso _).hom
  have hm : mG ≫ J = Spec.map ψ ≫ mA := by
    simp only [mG, mA, Category.assoc]
    exact key
  have hψtop : ⊤ ≤ (Spec.map ψ) ⁻¹ᵁ ⊤ := le_of_eq (Scheme.Hom.preimage_top _).symm
  have h2 : (Spec.map ψ).appTop = (Spec.map ψ).appLE ⊤ ⊤ hψtop :=
    (Scheme.Hom.appLE_eq_app _).symm
  have hmG' : ⊤ ≤ (mG ≫ J) ⁻¹ᵁ W := hmG.ge
  have hmA' : ⊤ ≤ (Spec.map ψ ≫ mA) ⁻¹ᵁ W := by
    rw [Scheme.Hom.comp_preimage, hmA]
    exact le_of_eq (Scheme.Hom.preimage_top _).symm
  have hsq : J.app W ≫ ΨG = ΨA ≫ ψ :=
    calc J.app W ≫ ΨG
        = (mG ≫ J).appLE W ⊤ hmG' ≫ (Scheme.ΓSpecIso (CommRingCat.of (S' ⊗[R] A))).hom := by
          simp only [ΨG]
          rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE_assoc]
      _ = (Spec.map ψ ≫ mA).appLE W ⊤ hmA' ≫
            (Scheme.ΓSpecIso (CommRingCat.of (S' ⊗[R] A))).hom := by
          rw [Scheme.Hom.appLE_congr_hom_transport hm]
      _ = ΨA ≫ ψ := by
          simp only [ΨA, Category.assoc]
          rw [← Scheme.ΓSpecIso_naturality, h2, Scheme.Hom.appLE_comp_appLE_assoc]
  -- `ΨA` is injective
  have hΨA : Function.Injective ΨA.hom := by
    simp only [ΨA, CommRingCat.hom_comp, RingHom.coe_comp]
    refine Function.Injective.comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] A))).hom).1 ?_
    let w : W.toScheme ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
      pullback.lift (W.ι ≫ pullback.fst _ p) zA
        (by rw [hι, ← Category.assoc zA, hz, Category.assoc, Category.assoc, pullback.condition])
    have hw_fst : w ≫ pullback.fst _ _ = W.ι ≫ pullback.fst _ p := pullback.lift_fst _ _ _
    have hw_snd : w ≫ pullback.snd _ _ = zA := pullback.lift_snd _ _ _
    have hwu : w ≫ u = W.ι := by
      apply pullback.hom_ext
      · rw [Category.assoc, hu_fst, ← Category.assoc, hw_fst, Category.comp_id]
      · rw [Category.assoc, hu, ← Category.assoc, hw_snd, hz]
    have hw' : (w ≫ (pullbackSpecIso R S A).hom) ≫ mA = W.ι := by
      simp only [mA, Category.assoc, Iso.hom_inv_id_assoc]
      exact hwu
    refine Scheme.Hom.appLE_top_injective_of_comp mA (w ≫ (pullbackSpecIso R S A).hom) W hmA.ge
      ?_ ?_
    · rw [hw']
      exact (Scheme.Opens.ι_preimage_self W).ge
    · rw [Scheme.Hom.appLE_congr_hom_transport hw']
      exact Scheme.Opens.ι_appLE_top_injective W _
  -- conclusion
  rw [injective_iff_map_eq_zero]
  intro b hb
  have h1 : ψ.hom (ΨA.hom b) = 0 := by
    have := congrArg (fun g => g.hom b) hsq
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [← this, hb, map_zero]
  have h2 : ΨA.hom b = 0 := hmap (by rw [map_zero]; simpa [ψ] using h1)
  exact hΨA (by rw [h2, map_zero])

end Generic

end AlgebraicGeometry

end
