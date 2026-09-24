import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.MultiplicativeGroupScheme

/-! # Linear independence of the powers of `λ` on `G_m ×_k T`

On `G_m ×_k T`, the powers of the coordinate `λ` are linearly independent over the sections of `T`:
if `Σ_n λ^n · pr₂^♯(y_n) = 0` in `Γ(G_m ×_k T, pr₂⁻¹V)` for an affine open `V ⊆ T`, then `y = 0`.
This is the general fact behind the step "compare the coefficients of `λ`" in the analysis of the
symmetric coefficients of a based jet (`BasedJet.symCoeffHom_jetPoint_partι_of_ne`).

Contents:
* `tp_basis_indep`, `laurentTmulIndep`: the purely algebraic part (the basis `{λ^n}` is linearly
  independent in `k[λ^{±1}] ⊗_k R` with coefficients in `R`);
* `Gm_pullback_sections_tensorEquiv`: the geometric part,
  `Γ(G_m ×_k T, pr₂⁻¹V) ≅ k[λ^{±1}] ⊗_k Γ(T,V)`, compatibly with `pr₁^♯λ` and `pr₂^♯`
  (section `GmChart`: `pr₂⁻¹V` and `Spec (k[λ^{±1}] ⊗_k Γ(T,V))` are two realizations of the same
  fibre product);
* `Gm_pullback_lambda_pow_independent`: the assembly of the two.

Reference: the nonnegative grading of the coordinate algebra of the cone, §2.1 of the paper
("replacing `t` by `λt` gives its coordinate algebra a nonnegative grading"); the ring-level
counterpart of the relative version of Stacks Project, Tag 0EKK is
`BasedJetAlgebra.mem_grading_iff_coaction`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

/-! ## Pure algebra: linear independence of basis elements over the coefficients -/

/-- If `b` is a basis of the `k`-module `M` and `e : ι → κ` is injective, then the family `b ∘ e` is
    linearly independent in `M ⊗_k R` with coefficients in `R`: `Σ_i b(e i) ⊗ y_i = 0 ⇒ y = 0`.
    Proof: apply `rTensor` of the dual coordinate functional `b.coord (e i)` followed by
    `TensorProduct.lid` to land in `R`; the `j`-th term becomes `δ_{ij} · y_j`. -/
theorem tp_basis_indep {k M R : Type u} [CommRing k] [AddCommGroup M] [Module k M]
    [AddCommGroup R] [Module k R] {κ : Type v} {ι : Type w} [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis κ k M) (e : ι → κ) (he : Function.Injective e) (y : ι →₀ R)
    (h : (y.sum fun i a => b (e i) ⊗ₜ[k] a) = 0) : y = 0 := by
  ext i
  set φ : M ⊗[k] R →ₗ[k] R :=
    (TensorProduct.lid k R).toLinearMap ∘ₗ LinearMap.rTensor R (b.coord (e i)) with hφdef
  have hφ : ∀ (j : ι) (a : R), φ (b (e j) ⊗ₜ[k] a) = (if j = i then a else 0) := by
    intro j a
    have hc : b.coord (e i) (b (e j)) = if j = i then (1 : k) else 0 := by
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      by_cases hji : j = i
      · subst hji; simp
      · rw [if_neg (fun hcc => hji (he hcc)), if_neg hji]
    simp only [hφdef, LinearMap.coe_comp, Function.comp_apply, LinearMap.rTensor_tmul,
      LinearEquiv.coe_coe, TensorProduct.lid_tmul, hc]
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]
  have h2 : φ (y.sum fun j a => b (e j) ⊗ₜ[k] a) = 0 := by rw [h]; exact map_zero φ
  rw [Finsupp.sum, map_sum] at h2
  simp only [hφ] at h2
  rw [Finset.sum_ite_eq' y.support i (fun j => y j)] at h2
  simpa using h2

/-- Laurent version: the `λ^n` (`n : ℕ`) are linearly independent in `k[λ^{±1}] ⊗_k R` with
    coefficients in `R`. The standard basis of `k[λ^{±1}] = AddMonoidAlgebra k ℤ` is
    `AddMonoidAlgebra.basis ℤ k`, whose `n`-th element is `T n`. -/
theorem laurentTmulIndep {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] (y : ℕ →₀ R)
    (h : (y.sum fun n a => (LaurentPolynomial.T (n : ℤ) : LaurentPolynomial k) ⊗ₜ[k] a) = 0) :
    y = 0 := by
  refine tp_basis_indep (AddMonoidAlgebra.basis ℤ k) (fun n : ℕ => (n : ℤ))
    (fun a b hab => Nat.cast_injective hab) y ?_
  rw [← h]
  exact Finsupp.sum_congr (fun n _ => by rw [AddMonoidAlgebra.basis_apply]; rfl)

/-! ## Geometry: the ring of sections of `G_m ×_k T` over an affine open -/

variable {k : Type u} [Field k] {T : AlgebraicGeometry.Scheme.{u}}

/-- The `k`-algebra structure on `Γ(T, V)` for `V ⊆ T`: `k = Γ(Spec k, ⊤)` maps to `Γ(T,V)` via `q^♯`. -/
@[instance_reducible] def Gm.sectionsAlgebra (q : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) (V : T.Opens) :
    Algebra k Γ(T, V) :=
  (CommRingCat.Hom.hom
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      q.appLE ⊤ V le_top)).toAlgebra

/-- The coordinate `λ = T 1 ∈ Γ(G_m, ⊤)` of `G_m`. -/
def Gm.lambda (k : Type u) [Field k] : Γ(Gm k, ⊤) :=
  (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom
    (LaurentPolynomial.T 1)

/-- `λ` pulled back along `pr₁` to `W = G_m ×_k T` and restricted to `pr₂⁻¹V`. -/
def Gm.lambdaOn (q : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) (V : T.Opens) :
    Γ(CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom q,
      CategoryTheory.Limits.pullback.snd
        ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom q ⁻¹ᵁ V) :=
  ((CategoryTheory.Limits.pullback
      ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom q).presheaf.map
      (CategoryTheory.homOfLE le_top).op).hom
    ((CategoryTheory.Limits.pullback.fst
      ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom q).appTop.hom (Gm.lambda k))


/-! ## Proof of the geometric part: `pr₂⁻¹V` is the fibre product `G_m ×_k V`, compared with `Spec (k[λ^{±1}] ⊗_k Γ(T,V))`

Write `S = Spec k`, `L = k[λ^{±1}]`, `R = Γ(T,V)`, `W = G_m ×_S T`, `U = pr₂⁻¹V`.
* `Gm.isPullback_preimage`: `(U, ι ≫ pr₁, (pr₂ ∣_ V) ≫ hV.isoSpec.hom)` is the fibre product of
  `G_m → S` and `Spec R → S` (paste `isPullback_morphismRestrict` horizontally with
  `IsPullback.of_hasPullback`, then transport along `V ≅ Spec R`);
* `Gm.isPullback_specTensor`: `(Spec (L ⊗ R), Spec inclL, Spec inclR)` is one as well
  (`CommRingCat.isPushout_tensorProduct`);
* the two fibre products are canonically isomorphic (`IsPullback.isoIsPullback`); applying `Γ(-, ⊤)`
  gives the isomorphism of section rings.
Note that the target of `pullback.fst` is `((Gm k).asOver S).left`, which is only definitionally
(not syntactically) equal to `Spec L`; so the pullback square on the `Spec` side is rewritten to this
object with `exact` (default transparency), so that all later `rw`s match. -/

section GmChart

open AlgebraicGeometry

/-- The structure morphism of `G_m` is `Spec (k → k[λ^{±1}])` (Mathlib's `specOverSpec_over`). -/
theorem Gm.over_hom_eq (k : Type u) [Field k] :
    (Gm k ↘ Spec (CommRingCat.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k))) :=
  AlgebraicGeometry.specOverSpec_over ..

/-- Elementwise form of the naturality of `ΓSpecIso`: `(Spec.map f).appTop (ΓSpecIso.inv x) = ΓSpecIso.inv (f x)`. -/
theorem Gm.Spec_map_appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (f : R ⟶ S) (x : R) :
    (Spec.map f).appTop.hom ((Scheme.ΓSpecIso R).inv.hom x) =
      (Scheme.ΓSpecIso S).inv.hom (f.hom x) := by
  have h := congrArg (fun φ : R ⟶ Γ(Spec S, ⊤) => φ.hom x) (Scheme.ΓSpecIso_inv_naturality f)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  exact h.symm

variable (q : T ⟶ Spec (CommRingCat.of k)) (V : T.Opens) (hV : IsAffineOpen V)

/-- Under `Gm.sectionsAlgebra`, the `k`-structure morphism `V.ι ≫ q` of `V` is `V ≅ Spec Γ(T,V)`
    followed by `Spec (algebraMap)`.
    Proof: `Scheme.Opens.toSpecΓ_SpecMap_appLE` + `toSpecΓ_top` + `toSpecΓ_SpecMap_ΓSpecIso_inv` + `resLE_comp_ι`. -/
theorem Gm.ι_comp_eq_isoSpec_hom_comp_specMap :
    letI := Gm.sectionsAlgebra q V
    V.ι ≫ q = hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(T, V))) := by
  letI := Gm.sectionsAlgebra q V
  have hle : V ≤ q ⁻¹ᵁ ⊤ := le_top.trans (by simp)
  have halg : CommRingCat.ofHom (algebraMap k Γ(T, V)) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ q.appLE ⊤ V hle := rfl
  have key := Scheme.Opens.toSpecΓ_SpecMap_appLE q ⊤ V hle
  rw [halg, Spec.map_comp, IsAffineOpen.isoSpec_hom, ← Category.assoc, key,
    Scheme.Opens.toSpecΓ_top, Category.assoc, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id, Scheme.Hom.resLE_comp_ι]

/-- The open subscheme `U = pr₂⁻¹V ⊆ G_m ×_k T` together with `ι ≫ pr₁` and `(pr₂ ∣_ V) ≫ isoSpec` is the
    fibre product of `G_m → Spec k` and `Spec Γ(T,V) → Spec k` (paste `isPullback_morphismRestrict`
    horizontally with `of_hasPullback`, then transport along `hV.isoSpec`). -/
theorem Gm.isPullback_preimage :
    letI := Gm.sectionsAlgebra q V
    IsPullback
      ((pullback.snd ((Gm k).asOver (Spec (CommRingCat.of k))).hom q ⁻¹ᵁ V).ι ≫
        pullback.fst ((Gm k).asOver (Spec (CommRingCat.of k))).hom q)
      ((pullback.snd ((Gm k).asOver (Spec (CommRingCat.of k))).hom q ∣_ V) ≫ hV.isoSpec.hom)
      ((Gm k).asOver (Spec (CommRingCat.of k))).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k Γ(T, V)))) := by
  letI := Gm.sectionsAlgebra q V
  have h1 := (isPullback_morphismRestrict
    (pullback.snd ((Gm k).asOver (Spec (CommRingCat.of k))).hom q) V).flip.paste_horiz
    (IsPullback.of_hasPullback ((Gm k).asOver (Spec (CommRingCat.of k))).hom q)
  refine h1.of_iso (Iso.refl _) (Iso.refl _) hV.isoSpec (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · simp [Gm.ι_comp_eq_isoSpec_hom_comp_specMap q V hV]

/-- `Spec (k[λ^{±1}] ⊗_k Γ(T,V))` with the two `Spec (include)` maps is the same fibre product
    (`CommRingCat.isPushout_tensorProduct`). Mathlib's square (with base `Spec (algebraMap k L)`) is
    rewritten up to definitional equality so that its base is the structure morphism of `G_m`. -/
theorem Gm.isPullback_specTensor :
    letI := Gm.sectionsAlgebra q V
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          LaurentPolynomial k →+* LaurentPolynomial k ⊗[k] Γ(T, V))) :
        Spec (CommRingCat.of (LaurentPolynomial k ⊗[k] Γ(T, V))) ⟶
          ((Gm k).asOver (Spec (CommRingCat.of k))).left)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          Γ(T, V) →ₐ[k] LaurentPolynomial k ⊗[k] Γ(T, V)).toRingHom))
      ((Gm k).asOver (Spec (CommRingCat.of k))).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k Γ(T, V)))) := by
  letI := Gm.sectionsAlgebra q V
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct k (LaurentPolynomial k) Γ(T, V))

/-- The chart `U = pr₂⁻¹V ≅ Spec (k[λ^{±1}] ⊗_k Γ(T,V))` (the canonical isomorphism of the two fibre products). -/
def Gm.preimageIsoSpecTensor :
    letI := Gm.sectionsAlgebra q V
    (pullback.snd ((Gm k).asOver (Spec (CommRingCat.of k))).hom q ⁻¹ᵁ V).toScheme ≅
      Spec (CommRingCat.of (LaurentPolynomial k ⊗[k] Γ(T, V))) :=
  letI := Gm.sectionsAlgebra q V
  (Gm.isPullback_preimage q V hV).isoIsPullback _ _ (Gm.isPullback_specTensor q V)

theorem Gm.preimageIsoSpecTensor_hom_includeLeft :
    letI := Gm.sectionsAlgebra q V
    (Gm.preimageIsoSpecTensor q V hV).hom ≫
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          LaurentPolynomial k →+* LaurentPolynomial k ⊗[k] Γ(T, V))) :
        Spec (CommRingCat.of (LaurentPolynomial k ⊗[k] Γ(T, V))) ⟶
          ((Gm k).asOver (Spec (CommRingCat.of k))).left) =
      (pullback.snd ((Gm k).asOver (Spec (CommRingCat.of k))).hom q ⁻¹ᵁ V).ι ≫
        pullback.fst ((Gm k).asOver (Spec (CommRingCat.of k))).hom q :=
  IsPullback.isoIsPullback_hom_fst _ _ (Gm.isPullback_preimage q V hV) (Gm.isPullback_specTensor q V)

theorem Gm.preimageIsoSpecTensor_hom_includeRight :
    letI := Gm.sectionsAlgebra q V
    (Gm.preimageIsoSpecTensor q V hV).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          Γ(T, V) →ₐ[k] LaurentPolynomial k ⊗[k] Γ(T, V)).toRingHom) =
      (pullback.snd ((Gm k).asOver (Spec (CommRingCat.of k))).hom q ∣_ V) ≫ hV.isoSpec.hom :=
  IsPullback.isoIsPullback_hom_snd _ _ (Gm.isPullback_preimage q V hV) (Gm.isPullback_specTensor q V)

/-- The chart on `x ⊗ 1`: `E^♯(x ⊗ 1) = (ι ≫ pr₁)^♯(x)`. -/
theorem Gm.preimageIsoSpecTensor_appTop_tmul_one (x : LaurentPolynomial k) :
    letI := Gm.sectionsAlgebra q V
    (Gm.preimageIsoSpecTensor q V hV).hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k ⊗[k] Γ(T, V)))).inv.hom
          (x ⊗ₜ[k] (1 : Γ(T, V)))) =
      ((pullback.snd ((Gm k).asOver (Spec (CommRingCat.of k))).hom q ⁻¹ᵁ V).ι ≫
        pullback.fst ((Gm k).asOver (Spec (CommRingCat.of k))).hom q).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom x) := by
  letI := Gm.sectionsAlgebra q V
  have h := congrArg (fun m : _ ⟶ ((Gm k).asOver (Spec (CommRingCat.of k))).left =>
      m.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom x))
    (Gm.preimageIsoSpecTensor_hom_includeLeft q V hV)
  exact Eq.trans (congrArg (Gm.preimageIsoSpecTensor q V hV).hom.appTop.hom
    (Gm.Spec_map_appTop_ΓSpecIso_inv (R := CommRingCat.of (LaurentPolynomial k))
      (S := CommRingCat.of (LaurentPolynomial k ⊗[k] Γ(T, V)))
      (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) x).symm) h

/-- The chart on `1 ⊗ a`: `E^♯(1 ⊗ a) = ((pr₂ ∣_ V) ≫ isoSpec)^♯(a)`. -/
theorem Gm.preimageIsoSpecTensor_appTop_one_tmul (a : Γ(T, V)) :
    letI := Gm.sectionsAlgebra q V
    (Gm.preimageIsoSpecTensor q V hV).hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k ⊗[k] Γ(T, V)))).inv.hom
          ((1 : LaurentPolynomial k) ⊗ₜ[k] a)) =
      ((pullback.snd ((Gm k).asOver (Spec (CommRingCat.of k))).hom q ∣_ V) ≫ hV.isoSpec.hom).appTop.hom
        ((Scheme.ΓSpecIso Γ(T, V)).inv.hom a) := by
  letI := Gm.sectionsAlgebra q V
  have h := congrArg (fun m : _ ⟶ Spec Γ(T, V) =>
      m.appTop.hom ((Scheme.ΓSpecIso Γ(T, V)).inv.hom a))
    (Gm.preimageIsoSpecTensor_hom_includeRight q V hV)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h
  refine Eq.trans ?_ h
  congr 1
  exact (Gm.Spec_map_appTop_ΓSpecIso_inv (R := Γ(T, V))
    (S := CommRingCat.of (LaurentPolynomial k ⊗[k] Γ(T, V)))
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      Γ(T, V) →ₐ[k] LaurentPolynomial k ⊗[k] Γ(T, V)).toRingHom) a).symm

end GmChart

/-- The ring of sections of `G_m ×_k T` over an affine open is `k[λ^{±1}] ⊗_k Γ(T,V)`: there is a ring
    isomorphism `e` sending `pr₂^♯(a)` to `1 ⊗ a` and `λ|` (`Gm.lambdaOn`) to `T 1 ⊗ 1`.

    References: Mathlib's `CommRingCat.isPushout_tensorProduct` + `isPullback_SpecMap_of_isPushout`
    (the fibre product of affine schemes is `Spec(A ⊗_R B)`); Stacks Project, Tag 01HR / Mathlib's
    `isPullback_morphismRestrict` (base change of an open immersion: `pr₂⁻¹V → W` is an open immersion
    and `(pr₂⁻¹V, pr₂ ∣_ V)` is the fibre product of `pr₂` along `V.ι`).

    Proof (write `S = Spec k`, `L = k[λ^{±1}]`, `R = Γ(T,V)`, `W = G_m ×_S T`, `U = pr₂⁻¹V`):
    (1) `Gm.ι_comp_eq_isoSpec_hom_comp_specMap`: the `k`-structure morphism `V.ι ≫ q` of `V` equals
        `hV.isoSpec.hom ≫ Spec(algebraMap k R)`, where `algebraMap` is `Gm.sectionsAlgebra`
        (`Scheme.Opens.toSpecΓ_SpecMap_appLE`, `toSpecΓ_SpecMap_ΓSpecIso_inv`, `resLE_comp_ι`).
    (2) `Gm.isPullback_preimage`: `(U, ι ≫ pr₁, (pr₂ ∣_ V) ≫ isoSpec.hom)` is the fibre product of
        `G_m → S` and `Spec R → S`: paste `isPullback_morphismRestrict pr₂ V` horizontally with
        `IsPullback.of_hasPullback` (`IsPullback.paste_horiz`), then transport along `V ≅ Spec R` with
        `IsPullback.of_iso` and substitute (1).
    (3) `Gm.isPullback_specTensor`: `(Spec (L ⊗_k R), Spec inclL, Spec inclR)` is the same fibre product
        (`CommRingCat.isPushout_tensorProduct` via `isPullback_SpecMap_of_isPushout`; the structure
        morphism of `G_m` is by definition `Spec (k → L)`, `specOverSpec_over`).
    (4) `Gm.preimageIsoSpecTensor`: the canonical isomorphism `E : U ≅ Spec (L ⊗_k R)` of the two fibre
        products (`IsPullback.isoIsPullback`), with `E ≫ Spec inclL = ι ≫ pr₁` and
        `E ≫ Spec inclR = (pr₂ ∣_ V) ≫ isoSpec.hom`; taking `appTop` and using the naturality of `ΓSpecIso`
        gives `E^♯(x ⊗ 1) = (ι ≫ pr₁)^♯ x` and `E^♯(1 ⊗ a) = ((pr₂ ∣_ V) ≫ isoSpec)^♯ a`.
    (5) `e⁻¹ := ΓSpecIso⁻¹ ≫ E^♯ ≫ U.topIso : L ⊗ R ≅ Γ(W, U)`; the two compatibilities reduce to the
        morphism identities `ΓSpecIso⁻¹ ≫ ((pr₂ ∣_ V) ≫ isoSpec)^♯ ≫ topIso = pr₂.appLE V U`
        (`Scheme.Opens.toSpecΓ_naturality`) and `ι^♯ ≫ topIso = restriction Γ(W,⊤) → Γ(W,U)`
        (`Scheme.Opens.ι_appTop`, `topIso_hom`).
    Formalization remark: the target of `pullback.fst` is `((Gm k).asOver S).left`, which is only
    definitionally equal to `Spec L`; hence (3) rewrites the base morphism with `exact`, and the steps of
    (4), (5) involving this object use `Eq.trans`/`erw`.
    Edge cases: for `V = ⊥` both sides are the zero ring and the statement is trivial; for a finite field
    `k` the statement still holds (the proof uses the basis of `k[λ^{±1}]`, not a Vandermonde argument on
    `k`-points). -/
theorem Gm_pullback_sections_tensorEquiv (q : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (V : T.Opens) (hV : AlgebraicGeometry.IsAffineOpen V) :
    letI := Gm.sectionsAlgebra q V
    ∃ e : Γ(CategoryTheory.Limits.pullback
        ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom q,
        CategoryTheory.Limits.pullback.snd
          ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom q ⁻¹ᵁ V) ≃+*
      (LaurentPolynomial k ⊗[k] Γ(T, V)),
      (∀ a : Γ(T, V), e ((CategoryTheory.Limits.pullback.snd
            ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom q).appLE
          V _ le_rfl |>.hom a) = (1 : LaurentPolynomial k) ⊗ₜ[k] a) ∧
        e (Gm.lambdaOn q V) = (LaurentPolynomial.T 1 : LaurentPolynomial k) ⊗ₜ[k] (1 : Γ(T, V)) := by
  letI := Gm.sectionsAlgebra q V
  let E := Gm.preimageIsoSpecTensor q V hV
  haveI : IsIso E.hom.appTop := inferInstanceAs (IsIso (E.hom.app ⊤))
  let eInv :=
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k ⊗[k] Γ(T, V)))).symm ≪≫
      asIso E.hom.appTop ≪≫
      (CategoryTheory.Limits.pullback.snd
        ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom q ⁻¹ᵁ V).topIso).commRingCatIsoToRingEquiv
  have heInv : ∀ t, eInv t = (CategoryTheory.Limits.pullback.snd
        ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom q ⁻¹ᵁ V).topIso.hom.hom
      (E.hom.appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (LaurentPolynomial k ⊗[k] Γ(T, V)))).inv.hom t)) :=
    fun t => rfl
  refine ⟨eInv.symm, ?_, ?_⟩
  · intro a
    -- at the level of morphisms: ΓSpecIso⁻¹ ≫ ((pr₂ ∣_ V) ≫ isoSpec)^♯ ≫ topIso = pr₂.appLE V (pr₂⁻¹V)
    have keyA : (AlgebraicGeometry.Scheme.ΓSpecIso Γ(T, V)).inv ≫
        ((CategoryTheory.Limits.pullback.snd
          ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom q ∣_ V) ≫
            hV.isoSpec.hom).appTop ≫
        (CategoryTheory.Limits.pullback.snd
          ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom q ⁻¹ᵁ V).topIso.hom =
        (CategoryTheory.Limits.pullback.snd
          ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom q).appLE V _ le_rfl := by
      -- (pr₂ ∣_ V) ≫ V.toSpecΓ = (pr₂⁻¹V).toSpecΓ ≫ Spec (pr₂.app V) (`toSpecΓ_naturality`),
      -- then `toSpecΓ_appTop` and `ΓSpecIso_naturality`.
      rw [AlgebraicGeometry.IsAffineOpen.isoSpec_hom, ← AlgebraicGeometry.Scheme.Opens.toSpecΓ_naturality,
        AlgebraicGeometry.Scheme.Hom.comp_appTop, AlgebraicGeometry.Scheme.Opens.toSpecΓ_appTop]
      simp only [CategoryTheory.Category.assoc, CategoryTheory.Iso.inv_hom_id,
        CategoryTheory.Category.comp_id]
      rw [AlgebraicGeometry.Scheme.ΓSpecIso_naturality, CategoryTheory.Iso.inv_hom_id_assoc,
        AlgebraicGeometry.Scheme.Hom.app_eq_appLE]
    rw [RingEquiv.symm_apply_eq, heInv, Gm.preimageIsoSpecTensor_appTop_one_tmul, ← keyA]
    rfl
  · -- at the level of morphisms: ι^♯ ≫ topIso = restriction Γ(W, ⊤) → Γ(W, pr₂⁻¹V)
    have keyB : (CategoryTheory.Limits.pullback.snd
          ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom q ⁻¹ᵁ V).ι.appTop ≫
        (CategoryTheory.Limits.pullback.snd
          ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom q ⁻¹ᵁ V).topIso.hom =
        (CategoryTheory.Limits.pullback
          ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom q).presheaf.map
          (CategoryTheory.homOfLE le_top).op := by
      rw [AlgebraicGeometry.Scheme.Opens.ι_appTop, AlgebraicGeometry.Scheme.Opens.topIso_hom]
      -- the intermediate object is Γ(pr₂⁻¹V, ⊤), only definitionally equal to W.presheaf.obj (op (ι ''ᵁ ⊤)), hence erw
      erw [← CategoryTheory.Functor.map_comp]
      congr 1
    rw [RingEquiv.symm_apply_eq, heInv, Gm.preimageIsoSpecTensor_appTop_tmul_one]
    unfold Gm.lambdaOn Gm.lambda
    rw [← keyB]
    rfl

/-- The powers of `λ` are linearly independent over coefficients in `Γ(T,V)`:
    `Σ_n λ^n · pr₂^♯(y_n) = 0` in `Γ(G_m ×_k T, pr₂⁻¹V)` implies `y = 0`.

    This is the lemma needed to compare `λ`-coefficients in `BasedJet.symCoeffHom_jetPoint_partι_of_ne`.
    Proof: `Gm_pullback_sections_tensorEquiv` + `laurentTmulIndep`. -/
theorem Gm_pullback_lambda_pow_independent (q : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (V : T.Opens) (hV : AlgebraicGeometry.IsAffineOpen V) (y : ℕ →₀ Γ(T, V))
    (h : (y.sum fun n a => Gm.lambdaOn q V ^ n *
      ((CategoryTheory.Limits.pullback.snd
        ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom q).appLE
          V _ le_rfl).hom a) = 0) :
    y = 0 := by
  letI := Gm.sectionsAlgebra q V
  obtain ⟨e, hsnd, hlam⟩ := Gm_pullback_sections_tensorEquiv q V hV
  refine laurentTmulIndep (k := k) y ?_
  have h2 : e (y.sum fun n a => Gm.lambdaOn q V ^ n *
      ((CategoryTheory.Limits.pullback.snd
        ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom q).appLE
          V _ le_rfl).hom a) = 0 := by rw [h]; exact map_zero e
  rw [Finsupp.sum, map_sum] at h2
  rw [Finsupp.sum, ← h2]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [map_mul, map_pow, hlam, hsnd]
  rw [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, mul_one, LaurentPolynomial.T_pow, mul_one]

end
