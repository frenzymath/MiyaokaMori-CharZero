import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.GroupSchemeAction
import MiyaokaMori.AlgebraicGeometry.Morphisms.MultiplicativeGroupScheme
import MiyaokaMori.AlgebraicGeometry.Morphisms.PullbackSpecAppInjective

/-! # The comorphism of a morphism over a base, as a morphism of pushforward modules

The comorphism `g^♯ : π_*O_T ⟶ q_*O_W` of a morphism `g : W ⟶ T` over `S` (with `g ≫ π = q`),
as a morphism of `O_S`-modules: `π_*` of the unit `O_T → g_*O_W`, followed by `π_*g_* ≅ (g ≫ π)_*`
and the retargeting `(g ≫ π)_* ≅ q_*`.  On sections over `U ⊆ S` it is `g.app (π⁻¹U)` (up to the
identification `q⁻¹U = (g ≫ π)⁻¹U`).  This is the "morphism part" of Stacks 01S5 (affine morphisms
↔ quasi-coherent algebras), written with an explicit target so that it composes:

* `pushforwardUnitMap_comp`: `(g₁ ≫ g₂)^♯ = g₂^♯ ≫ g₁^♯`;
* `pushforwardUnitMap_id`: `(𝟙 T)^♯ = 𝟙`;
* `pushforwardUnitMap_congr`: it depends only on `g`.

Both summands of the weight defect `GroupSchemeAction.weightDefect α m` (`JetGrading.lean`) are of
this form (`act^♯` and `pr₂^♯`), see `weightDefect_zero_eq` in `JetGradingNonnegative.lean`.

Also here: the sections-level lemma `affineLine_fromGm_app_injective` — restriction from `A¹ ×_k X`
to the open `G_m ×_k X` is injective on functions (`A[λ] ↪ A[λ^{±1}]`); proved by reduction to
affine `V` and `pullback_map_Spec_app_injective_of_affine` (`PullbackSpecAppInjective.lean`).

Source: Stacks 01S5; §2 of the paper (the grading `S_m` of the jet algebra is defined through
`act^♯` and `pr₂^♯`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {W T S : AlgebraicGeometry.Scheme.{u}}

/-- The comorphism `g^♯ : π_*O_T ⟶ q_*O_W` of `g : W ⟶ T` with `g ≫ π = q`. -/
noncomputable def pushforwardUnitMap (g : W ⟶ T) (π : T ⟶ S) (q : W ⟶ S) (h : g ≫ π = q) :
    (AlgebraicGeometry.Scheme.Modules.pushforward π).obj (SheafOfModules.unit T.ringCatSheaf) ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward q).obj (SheafOfModules.unit W.ringCatSheaf) :=
  (AlgebraicGeometry.Scheme.Modules.pushforward π).map
      (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) ≫
    (AlgebraicGeometry.Scheme.Modules.pushforwardComp g π).hom.app _ ≫
    (AlgebraicGeometry.Scheme.Modules.pushforwardCongr h).hom.app _

/-- Sections of `g^♯` over `U`: `g.app (π⁻¹U)` followed by the identification `q⁻¹U = (g ≫ π)⁻¹U`. -/
theorem pushforwardUnitMap_app_apply (g : W ⟶ T) (π : T ⟶ S) (q : W ⟶ S) (h : g ≫ π = q) (U : S.Opens)
    (x : Γ((AlgebraicGeometry.Scheme.Modules.pushforward π).obj (SheafOfModules.unit T.ringCatSheaf), U)) :
    ((pushforwardUnitMap g π q h).app U).hom x =
      (W.presheaf.map (CategoryTheory.eqToHom (h ▸ rfl : q ⁻¹ᵁ U = (g ≫ π) ⁻¹ᵁ U)).op).hom
        ((g.app (π ⁻¹ᵁ U)).hom x) :=
  rfl

/-- `g^♯` depends only on `g` (the target and the proof are determined). -/
theorem pushforwardUnitMap_congr {g g' : W ⟶ T} (e : g = g') (π : T ⟶ S) (q : W ⟶ S)
    (h : g ≫ π = q) (h' : g' ≫ π = q) :
    pushforwardUnitMap g π q h = pushforwardUnitMap g' π q h' := by
  subst e
  rfl

/-- `pushforwardCongr rfl` has identity components. -/
theorem pushforwardCongr_rfl_hom_app' (f : W ⟶ S) (M : W.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pushforwardCongr (rfl : f = f)).hom.app M = 𝟙 _ := by
  apply AlgebraicGeometry.Scheme.Modules.hom_ext
  intro U
  ext x
  show (M.presheaf.map (CategoryTheory.eqToHom rfl).op).hom x = x
  rw [CategoryTheory.eqToHom_refl, CategoryTheory.op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Transport along `eqToHom` between definitionally equal opens is the identity on sections
(`HEq.rfl` supplies the definitional equality of the two sections). -/
theorem presheaf_map_eqToHom_op_apply {X : AlgebraicGeometry.Scheme.{u}} {U V : X.Opens} (e : U = V)
    (y : Γ(X, V)) (y' : Γ(X, U)) (hy : HEq y y') :
    (X.presheaf.map (CategoryTheory.eqToHom e).op).hom y = y' := by
  subst e
  cases hy
  rw [CategoryTheory.eqToHom_refl, CategoryTheory.op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Sections of `g^♯`, with the transport along `q⁻¹U = (g ≫ π)⁻¹U` absorbed: any `y'` definitionally
equal to `g.app (π⁻¹U) x` (witnessed by `HEq.rfl`) is the value. -/
theorem pushforwardUnitMap_app_apply_eq (g : W ⟶ T) (π : T ⟶ S) (q : W ⟶ S) (h : g ≫ π = q) (U : S.Opens)
    (x : Γ((AlgebraicGeometry.Scheme.Modules.pushforward π).obj (SheafOfModules.unit T.ringCatSheaf), U))
    (y' : Γ((AlgebraicGeometry.Scheme.Modules.pushforward q).obj (SheafOfModules.unit W.ringCatSheaf), U))
    (hy : HEq ((g.app (π ⁻¹ᵁ U)).hom x) y') :
    ((pushforwardUnitMap g π q h).app U).hom x = y' :=
  presheaf_map_eqToHom_op_apply (h ▸ rfl : q ⁻¹ᵁ U = (g ≫ π) ⁻¹ᵁ U) ((g.app (π ⁻¹ᵁ U)).hom x) y' hy

/-- Functoriality: `(g₁ ≫ g₂)^♯ = g₂^♯ ≫ g₁^♯`. -/
theorem pushforwardUnitMap_comp {W₁ : AlgebraicGeometry.Scheme.{u}} (g₁ : W₁ ⟶ W) (g₂ : W ⟶ T) (π : T ⟶ S)
    (q₂ : W ⟶ S) (h₂ : g₂ ≫ π = q₂) (q₁ : W₁ ⟶ S) (h₁ : g₁ ≫ q₂ = q₁) (h : (g₁ ≫ g₂) ≫ π = q₁) :
    pushforwardUnitMap g₂ π q₂ h₂ ≫ pushforwardUnitMap g₁ q₂ q₁ h₁ =
      pushforwardUnitMap (g₁ ≫ g₂) π q₁ h := by
  subst h₂
  subst h₁
  apply AlgebraicGeometry.Scheme.Modules.hom_ext
  intro U
  ext x
  show ((pushforwardUnitMap g₁ (g₂ ≫ π) (g₁ ≫ g₂ ≫ π) rfl).app U).hom
      (((pushforwardUnitMap g₂ π (g₂ ≫ π) rfl).app U).hom x) =
    ((pushforwardUnitMap (g₁ ≫ g₂) π (g₁ ≫ g₂ ≫ π) h).app U).hom x
  have a1 : ((pushforwardUnitMap g₂ π (g₂ ≫ π) rfl).app U).hom x = (g₂.app (π ⁻¹ᵁ U)).hom x :=
    pushforwardUnitMap_app_apply_eq _ _ _ _ _ _ _ HEq.rfl
  have a2 : ((pushforwardUnitMap g₁ (g₂ ≫ π) (g₁ ≫ g₂ ≫ π) rfl).app U).hom ((g₂.app (π ⁻¹ᵁ U)).hom x) =
      (g₁.app ((g₂ ≫ π) ⁻¹ᵁ U)).hom ((g₂.app (π ⁻¹ᵁ U)).hom x) :=
    pushforwardUnitMap_app_apply_eq _ _ _ _ _ _ _ HEq.rfl
  have a3 : ((pushforwardUnitMap (g₁ ≫ g₂) π (g₁ ≫ g₂ ≫ π) h).app U).hom x =
      (g₁.app ((g₂ ≫ π) ⁻¹ᵁ U)).hom ((g₂.app (π ⁻¹ᵁ U)).hom x) :=
    pushforwardUnitMap_app_apply_eq _ _ _ _ _ _ _ HEq.rfl
  exact (congrArg (fun y => ((pushforwardUnitMap g₁ (g₂ ≫ π) (g₁ ≫ g₂ ≫ π) rfl).app U).hom y) a1).trans
    (a2.trans a3.symm)

/-- `(𝟙 T)^♯ = 𝟙`. -/
theorem pushforwardUnitMap_id (π : T ⟶ S) :
    pushforwardUnitMap (CategoryTheory.CategoryStruct.id T) π π (CategoryTheory.Category.id_comp π) =
      CategoryTheory.CategoryStruct.id _ := by
  apply AlgebraicGeometry.Scheme.Modules.hom_ext
  intro U
  ext x
  show ((pushforwardUnitMap (CategoryTheory.CategoryStruct.id T) π π (CategoryTheory.Category.id_comp π)).app U).hom x = x
  exact pushforwardUnitMap_app_apply_eq _ _ _ _ _ _ _ HEq.rfl

end AlgebraicGeometry.Scheme.Modules

/-- Affine case of `affineLine_fromGm_app_injective`, written with `Spec.map (algebraMap)` in place
of `Gm k`, `↘` (definitionally the same morphisms): `V ⊆ X` affine.  This is
`pullback_map_Spec_app_injective_of_affine` (module `PullbackSpecAppInjective`) applied to
`φ = toLaurentAlg : k[λ] → k[λ^{±1}]`, `A = Γ(X, V)` with the `k`-algebra structure
`IsAffineOpen.specAlgebra`, `ι = hV.fromSpec`, `zA = (pr₂' ∣_ V) ≫ hV.isoSpec.hom`, and the flatness
input `tensorProduct_map_id_injective_of_field` (`k` a field) with `Polynomial.toLaurent_injective`. -/
theorem affineLine_fromGm_app_injective_specMap_of_isAffineOpen {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} (p : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (V : X.Opens) (hV : AlgebraicGeometry.IsAffineOpen V)
    (e₁ : AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k))) ≫
        CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of k)) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Polynomial.toLaurentAlg (R := k)).toRingHom) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
    (e₂ : p ≫ CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of k)) =
      CategoryTheory.CategoryStruct.id X ≫ p) :
    Function.Injective
      ((CategoryTheory.Limits.pullback.map
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k)))) p
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) p
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Polynomial.toLaurentAlg (R := k)).toRingHom))
          (CategoryTheory.CategoryStruct.id X) (CategoryTheory.CategoryStruct.id _) e₁ e₂).app
        (CategoryTheory.Limits.pullback.snd
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) p ⁻¹ᵁ V)).hom := by
  let _ := hV.specAlgebra (R := k) p
  refine AlgebraicGeometry.pullback_map_Spec_app_injective_of_affine (R := k) (S := Polynomial k)
    (S' := LaurentPolynomial k) (Polynomial.toLaurentAlg (R := k)) p V (A := Γ(X, V)) hV.fromSpec
    (hV.Spec_map_algebraMap_specAlgebra p) hV.fromSpec_preimage_self _ rfl
    ((CategoryTheory.Limits.pullback.snd
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) p ∣_ V) ≫
      hV.isoSpec.hom) ?_
    (AlgebraicGeometry.tensorProduct_map_id_injective_of_field _ Polynomial.toLaurent_injective) e₁ e₂
  rw [CategoryTheory.Category.assoc, AlgebraicGeometry.IsAffineOpen.isoSpec_hom_fromSpec,
    AlgebraicGeometry.morphismRestrict_ι]

/-- `affineLine_fromGm_app_injective` written with `Spec.map (algebraMap)` in place of `Gm k`, `↘`
(definitionally the same morphisms); general open `V`.  Proof: reduce to the affine opens of `V`
by the sheaf property (`TopCat.Sheaf.eq_of_locally_eq'`, `Scheme.Hom.naturality`) and apply
`affineLine_fromGm_app_injective_specMap_of_isAffineOpen`. -/
theorem affineLine_fromGm_app_injective_specMap {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} (p : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (V : X.Opens)
    (e₁ : AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k))) ≫
        CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of k)) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Polynomial.toLaurentAlg (R := k)).toRingHom) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
    (e₂ : p ≫ CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of k)) =
      CategoryTheory.CategoryStruct.id X ≫ p) :
    Function.Injective
      ((CategoryTheory.Limits.pullback.map
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k)))) p
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) p
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Polynomial.toLaurentAlg (R := k)).toRingHom))
          (CategoryTheory.CategoryStruct.id X) (CategoryTheory.CategoryStruct.id _) e₁ e₂).app
        (CategoryTheory.Limits.pullback.snd
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) p ⁻¹ᵁ V)).hom := by
  set J := CategoryTheory.Limits.pullback.map
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k)))) p
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) p
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Polynomial.toLaurentAlg (R := k)).toRingHom))
    (CategoryTheory.CategoryStruct.id X) (CategoryTheory.CategoryStruct.id _) e₁ e₂
  set pr := CategoryTheory.Limits.pullback.snd
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) p
  rw [injective_iff_map_eq_zero]
  intro b hb
  -- an affine open cover of `V`
  have hcov : ∀ x : V, ∃ U : X.affineOpens, x.1 ∈ (U : X.Opens) ∧ (U : X.Opens) ≤ V := fun x => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open x.2 V.2
    exact ⟨⟨U, hU⟩, hxU, hUV⟩
  choose U hxU hUV using hcov
  have hle : ∀ x : V, pr ⁻¹ᵁ (U x : X.Opens) ≤ pr ⁻¹ᵁ V := fun x y hy => hUV x hy
  refine (CategoryTheory.Limits.pullback
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
      p).sheaf.eq_of_locally_eq' _ _ (fun x => CategoryTheory.homOfLE (hle x)) ?_ b 0 ?_
  · intro y hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨_, hy⟩, hxU ⟨_, hy⟩⟩
  · intro x
    -- `j^♯` commutes with restriction, so `j^♯ (b|_{pr⁻¹U_x}) = (j^♯ b)|_… = 0`
    have hnat : (J.app (pr ⁻¹ᵁ (U x : X.Opens))).hom
        (((CategoryTheory.Limits.pullback
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) p).presheaf.map
            (CategoryTheory.homOfLE (hle x)).op).hom b) = 0 := by
      rw [← CommRingCat.comp_apply, AlgebraicGeometry.Scheme.Hom.naturality, CommRingCat.comp_apply,
        hb, map_zero]
    rw [map_zero]
    exact affineLine_fromGm_app_injective_specMap_of_isAffineOpen p (U x : X.Opens) (U x).2 e₁ e₂
      (hnat.trans (map_zero _).symm)

/-- Restriction of functions from `A¹ ×_k X` to the open subscheme `G_m ×_k X` is injective
(the inclusion `j = Spec(toLaurent) ×_k 𝟙 : G_m ×_k X → A¹ ×_k X`, on sections over the opens
`pr₂⁻¹V`, `V ⊆ X` open).  Algebraically: `A[λ] → A[λ, λ⁻¹]` is injective for every ring `A`.

Proof.  Let `b ∈ Γ(A¹ ×_k X, pr₂'⁻¹V)` with `j^♯ b = 0`.
1. Reduce to `X` affine: the affine opens `V_x ⊆ V` (`x ∈ V`) cover `V` (`isBasis_affineOpens`), the
   opens `pr₂'⁻¹V_x` cover `pr₂'⁻¹V`, and `Γ(A¹ ×_k X, -)` is a sheaf, so it suffices to show
   `b|_{pr₂'⁻¹V_x} = 0` for each `x` (`TopCat.Sheaf.eq_of_locally_eq'`); the restriction of `j^♯ b` is
   `j^♯` of the restriction (`Scheme.Hom.naturality`).  (`affineLine_fromGm_app_injective_specMap`.)
2. For `V_x = Spec A` affine this is `affineLine_fromGm_app_injective_specMap_of_isAffineOpen`
   (= `pullback_map_Spec_app_injective_of_affine`: `pr₂'⁻¹V_x ≅ Spec (k[λ] ⊗_k A)`,
   `pr₂⁻¹V_x ≅ Spec (k[λ^{±1}] ⊗_k A)` via `pullbackSpecIso`, `j` becomes `Spec (toLaurent ⊗ id)`,
   and `toLaurent ⊗_k id_A` is injective because `k` is a field, so `A` is flat over `k`).
3. Hence `b|_{pr₂'⁻¹V_x} = 0` for all `x`, so `b = 0`.
The statement below is the `Spec.map`-form statement up to unfolding `Gm k` and `↘` (`exact`).
Edge cases: `V = ∅` (zero rings, empty cover); `X = ∅`; `r` plays no role. -/
theorem affineLine_fromGm_app_injective {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    (p : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) (V : X.Opens) :
    Function.Injective
      ((CategoryTheory.Limits.pullback.map (((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom) p
          (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) p
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Polynomial.toLaurentAlg (R := k)).toRingHom))
          (CategoryTheory.CategoryStruct.id X) (CategoryTheory.CategoryStruct.id _)
          GroupSchemeAction.isNonnegative_cond₁
          (by rw [CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp])).app
        (CategoryTheory.Limits.pullback.snd
          (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) p ⁻¹ᵁ V)).hom :=
  affineLine_fromGm_app_injective_specMap p V _ _

end
