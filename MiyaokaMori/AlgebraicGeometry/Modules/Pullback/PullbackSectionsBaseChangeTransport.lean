import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackSectionsNativeBaseChange
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjBaseChangeUnit

/-! # Injectivity statements transported through the base-change isomorphism (Stacks 01I9)

Let `g : Y → X`, `V ⊆ X` and `V' ⊆ g⁻¹V` affine opens, `M` quasi-coherent on `X`. Stacks 01I9
(`isIso_transpose_pullbackSectionsNative`) gives the
`Γ(Y, V')`-linear isomorphism `T : Γ(Y, V') ⊗_{Γ(X, V)} Γ(M, V) ≅ Γ(g^*M, V')`, `t ⊗ s ↦ t • (η s)|_{V'}`
(`baseChangeTranspose`, `baseChangeTranspose_tmul`). Two consequences:

* (i) `pullback_map_app_injective_of_flat`: for a morphism `i : N ⟶ M` of quasi-coherent modules with `i.app V`
  injective and `Γ(Y, V')` flat over `Γ(X, V)`, `(g^*i).app V'` is injective. Proof: `T_M ∘ (1 ⊗ i.app V) = (g^*i).app V' ∘ T_N`
  on pure tensors (`pullback_map_app_pullbackSectionsOn` from `RelativeProjBaseChangeUnit.lean`: the adjunction unit is
  natural in the module, and `(g^*i).app V'` is `Γ(Y, V')`-linear), and `1 ⊗ i.app V` is injective by flatness (`Module.Flat.lTensor_preserves_injective_linearMap`).
* (ii) `smul_injective_of_smul_injective_tensor`: if `r • ` is injective on `Γ(Y, V') ⊗_{Γ(X, V)} Γ(M, V)` for some
  `r ∈ Γ(Y, V')`, then `r •` is injective on `Γ(g^*M, V')` (`T` is `Γ(Y, V')`-linear and bijective).

Pure algebra used for (ii): on `B ⊗_A N`, `r •` is `rTensor N (r·)`; if `r·` has an `A`-linear left inverse `L` on `B`
(`L (r * b) = b`) then `rTensor N L` is a left inverse of `rTensor N (r·)`, so `r •` is injective
(`smul_injective_of_leftInverse`). For `B ≅ A[X]` (an `A`-algebra isomorphism `e` with `e r = X`) such an `L` is
`e⁻¹ ∘ divX ∘ e` (`Polynomial.divX (X * p) = p`; `exists_linear_leftInverse_of_algEquiv_mvPolynomial`), and `B` is flat
over `A` (`A[X]` is free: `flat_of_algEquiv_mvPolynomial`).

Edge cases: `V' = ∅` or `M = 0`: all modules are zero, every map is injective. `A` the zero ring: `A[X] = 0`, fine.

References: Stacks 01I9 (schemes-lemma-widetilde-pullback); Hartshorne II.5.2(e); flatness: Stacks 00HD
(free modules are flat).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace MiyaokaMori.AffineLinePullbackTorsionFree

/-! ## §1 Pure algebra: left inverses and injectivity of `r •` on `B ⊗_A N` -/

section Algebra

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {N : Type*} [AddCommGroup N] [Module A N]

/-- Left multiplication by `r : B` as an `A`-linear map `B → B`. -/
def mulLeftₗ (A : Type*) [CommRing A] {B : Type*} [CommRing B] [Algebra A B] (r : B) : B →ₗ[A] B where
  toFun b := r * b
  map_add' := mul_add r
  map_smul' a b := mul_smul_comm a r b

theorem mulLeftₗ_apply (r b : B) : mulLeftₗ A r b = r * b := rfl

/-- `r • z = rTensor N (r·) z` on `B ⊗[A] N`. -/
theorem smul_eq_rTensor_mulLeftₗ (r : B) (z : B ⊗[A] N) :
    r • z = LinearMap.rTensor N (mulLeftₗ A r) z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero]
  | tmul b n => rw [LinearMap.rTensor_tmul, TensorProduct.smul_tmul', mulLeftₗ_apply, smul_eq_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy]

/-- If `r·` has an `A`-linear left inverse on `B`, then `r •` is injective on `B ⊗[A] N`
(`rTensor N L` is a left inverse of `rTensor N (r·)`). -/
theorem smul_injective_of_leftInverse (r : B) (L : B →ₗ[A] B) (hL : ∀ b, L (r * b) = b) :
    Function.Injective (fun z : B ⊗[A] N => r • z) := by
  have hcomp : L ∘ₗ mulLeftₗ A r = LinearMap.id := LinearMap.ext hL
  have h1 : ∀ z : B ⊗[A] N, LinearMap.rTensor N L (r • z) = z := by
    intro z
    rw [smul_eq_rTensor_mulLeftₗ, ← LinearMap.rTensor_comp_apply, hcomp, LinearMap.rTensor_id,
      LinearMap.id_apply]
  intro z w hzw
  rw [← h1 z, ← h1 w]
  exact congrArg _ hzw

/-- `Polynomial.divX` as an `R`-linear map. -/
def divXₗ (R : Type*) [CommRing R] : Polynomial R →ₗ[R] Polynomial R where
  toFun := Polynomial.divX
  map_add' _ _ := Polynomial.divX_add
  map_smul' a p := by
    simp only [Polynomial.smul_eq_C_mul, Polynomial.divX_C_mul, RingHom.id_apply]

theorem divXₗ_apply {R : Type*} [CommRing R] (p : Polynomial R) : divXₗ R p = Polynomial.divX p := rfl

/-- `divX (X * p) = p` (coefficientwise). -/
theorem divX_X_mul {R : Type*} [CommRing R] (p : Polynomial R) :
    Polynomial.divX (Polynomial.X * p) = p := by
  ext n
  rw [Polynomial.coeff_divX, Polynomial.coeff_X_mul]

/-- **The variable of a polynomial ring in one variable has an `A`-linear left inverse.** If
`e : B ≃ₐ[A] MvPolynomial σ A` (`σ` a singleton) and `e b = X`, there is an `A`-linear `L : B → B` with `L (b * c) = c`
for all `c` (namely `e⁻¹ ∘ divX ∘ e`, through `MvPolynomial.uniqueAlgEquiv`). -/
theorem exists_linear_leftInverse_of_algEquiv_mvPolynomial {σ : Type*} [Unique σ]
    (e : B ≃ₐ[A] MvPolynomial σ A) (b : B) (hb : e b = MvPolynomial.X default) :
    ∃ L : B →ₗ[A] B, ∀ c, L (b * c) = c := by
  let ue := MvPolynomial.uniqueAlgEquiv A σ
  refine ⟨e.symm.toLinearMap ∘ₗ ue.symm.toLinearMap ∘ₗ divXₗ A ∘ₗ ue.toLinearMap ∘ₗ e.toLinearMap,
    fun c => ?_⟩
  have hX : ue (MvPolynomial.X (default : σ)) = Polynomial.X := by
    rw [MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.eval₂_X]
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, divXₗ_apply]
  rw [map_mul, hb, map_mul, hX, divX_X_mul, ue.symm_apply_apply, e.symm_apply_apply]

/-- **`B ≅ A[X]` is flat over `A`** (a polynomial ring is free, `Module.Free`, hence flat). -/
theorem flat_of_algEquiv_mvPolynomial {σ : Type*} (e : B ≃ₐ[A] MvPolynomial σ A) : Module.Flat A B :=
  Module.Flat.of_linearEquiv e.toLinearEquiv

end Algebra

end MiyaokaMori.AffineLinePullbackTorsionFree

/-! ## §2 Transport through the base-change isomorphism of Stacks 01I9 -/

namespace AlgebraicGeometry.Scheme.Modules

open MiyaokaMori.AffineLinePullbackTorsionFree

variable {X Y : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ X)

/-- The base-change transpose of Stacks 01I9: `Γ(Y, V') ⊗_{Γ(X, V)} Γ(M, V) ⟶ Γ(g^*M, V')`, `t ⊗ s ↦ t • (η s)|_{V'}`
(an isomorphism for `V`, `V'` affine and `M` quasi-coherent, `isIso_transpose_pullbackSectionsNative`). -/
abbrev baseChangeTranspose (M : X.Modules) (V : X.Opens) (V' : Y.Opens) (h : V' ≤ g ⁻¹ᵁ V) :
    (ModuleCat.extendScalars (g.appLE V V' h).hom).obj (ModuleCat.of Γ(X, V) Γ(M, V)) ⟶
      ModuleCat.of Γ(Y, V') Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M, V') :=
  ((ModuleCat.extendRestrictScalarsAdj (g.appLE V V' h).hom).homEquiv _ _).symm
    (pullbackSectionsNative g M V V' h)

/-- `T (t ⊗ s) = t • (η s)|_{V'}`. -/
theorem baseChangeTranspose_tmul (M : X.Modules) (V : X.Opens) (V' : Y.Opens) (h : V' ≤ g ⁻¹ᵁ V)
    (t : Γ(Y, V')) (s : Γ(M, V)) :
    letI : Algebra Γ(X, V) Γ(Y, V') := (g.appLE V V' h).hom.toAlgebra
    (baseChangeTranspose g M V V' h).hom (t ⊗ₜ[Γ(X, V)] s) = t • pullbackSectionsOn g M V V' h s := by
  letI : Algebra Γ(X, V) Γ(Y, V') := (g.appLE V V' h).hom.toAlgebra
  change (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (g.appLE V V' h).hom
      (pullbackSectionsNative g M V V' h)).hom (t ⊗ₜ[Γ(X, V)] s) = _
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply]
  change t • pullbackSectionsOn g M V V' h s = _
  rfl

/- Naturality of the section pullback in the module, `(g^*i).app V' ((η s)|_{V'}) = (η (i s))|_{V'}`, is
`Modules.pullback_map_app_pullbackSectionsOn` (`RelativeProjBaseChangeUnit.lean`). -/

section

variable (M : X.Modules) [M.IsQuasicoherent] (V : X.Opens) (V' : Y.Opens) (h : V' ≤ g ⁻¹ᵁ V)

/-- **(ii) Injectivity of `r •` on `Γ(g^*M, V')` from injectivity on the base-changed module**
`Γ(Y, V') ⊗_{Γ(X, V)} Γ(M, V)` (Stacks 01I9: the transpose is a `Γ(Y, V')`-linear isomorphism). -/
theorem smul_injective_of_smul_injective_tensor (hV : AlgebraicGeometry.IsAffineOpen V)
    (hV' : AlgebraicGeometry.IsAffineOpen V') (r : Γ(Y, V'))
    (hr : letI : Algebra Γ(X, V) Γ(Y, V') := (g.appLE V V' h).hom.toAlgebra
      Function.Injective (fun z : Γ(Y, V') ⊗[Γ(X, V)] Γ(M, V) => r • z)) :
    Function.Injective (fun x : Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M, V') => r • x) := by
  letI : Algebra Γ(X, V) Γ(Y, V') := (g.appLE V V' h).hom.toAlgebra
  haveI := isIso_transpose_pullbackSectionsNative g M V hV V' hV' h
  have hbij : Function.Bijective (baseChangeTranspose g M V V' h).hom :=
    ConcreteCategory.bijective_of_isIso (baseChangeTranspose g M V V' h)
  let e : (Γ(Y, V') ⊗[Γ(X, V)] Γ(M, V)) ≃ₗ[Γ(Y, V')]
      Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M, V') :=
    LinearEquiv.ofBijective (baseChangeTranspose g M V V' h).hom hbij
  intro x x' hxx'
  have h2 : e (r • e.symm x) = e (r • e.symm x') := by
    rw [LinearEquiv.map_smul, LinearEquiv.map_smul, e.apply_symm_apply, e.apply_symm_apply]
    exact hxx'
  have h3 : e.symm x = e.symm x' := hr (e.injective h2)
  rw [← e.apply_symm_apply x, ← e.apply_symm_apply x', h3]

/-- **(i) `g^*` preserves injectivity on sections over affine opens when `Γ(Y, V')` is flat over `Γ(X, V)`**:
for `i : N ⟶ M` quasi-coherent with `i.app V` injective, `(g^*i).app V'` is injective (Stacks 01I9 + flatness).
Proof: the square `T_M ∘ (extendScalars (i.app V)) = (g^*i).app V' ∘ T_N` commutes (checked on `1 ⊗ s`,
`ModuleCat.ExtendScalars.hom_ext`), `T_N`, `T_M` are bijective, and `extendScalars (i.app V) = 1 ⊗ i.app V` is
injective by flatness (`Module.Flat.lTensor_preserves_injective_linearMap`). -/
theorem pullback_map_app_injective_of_flat (hV : AlgebraicGeometry.IsAffineOpen V)
    (hV' : AlgebraicGeometry.IsAffineOpen V') {N : X.Modules} [N.IsQuasicoherent] (i : N ⟶ M)
    (hflat : letI : Algebra Γ(X, V) Γ(Y, V') := (g.appLE V V' h).hom.toAlgebra
      Module.Flat Γ(X, V) Γ(Y, V'))
    (hinj : Function.Injective (i.app V)) :
    Function.Injective (((AlgebraicGeometry.Scheme.Modules.pullback g).map i).app V') := by
  letI : Algebra Γ(X, V) Γ(Y, V') := (g.appLE V V' h).hom.toAlgebra
  haveI := isIso_transpose_pullbackSectionsNative g N V hV V' hV' h
  haveI := isIso_transpose_pullbackSectionsNative g M V hV V' hV' h
  have hN : Function.Bijective (baseChangeTranspose g N V V' h).hom :=
    ConcreteCategory.bijective_of_isIso (baseChangeTranspose g N V V' h)
  have hM : Function.Bijective (baseChangeTranspose g M V V' h).hom :=
    ConcreteCategory.bijective_of_isIso (baseChangeTranspose g M V V' h)
  -- `i.app V` and `(g^*i).app V'` as morphisms of module categories
  let ψ : ModuleCat.of Γ(X, V) Γ(N, V) ⟶ ModuleCat.of Γ(X, V) Γ(M, V) :=
    ModuleCat.ofHom
      { toFun := i.app V
        map_add' := fun a b => map_add _ a b
        map_smul' := fun r m => Hom.app_smul i r m }
  let φ' : ModuleCat.of Γ(Y, V') Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj N, V') ⟶
      ModuleCat.of Γ(Y, V') Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M, V') :=
    ModuleCat.ofHom
      { toFun := ((AlgebraicGeometry.Scheme.Modules.pullback g).map i).app V'
        map_add' := fun a b => map_add _ a b
        map_smul' := fun r m => Hom.app_smul ((AlgebraicGeometry.Scheme.Modules.pullback g).map i) r m }
  -- the commutative square, checked on `1 ⊗ s`
  have hsq : baseChangeTranspose g N V V' h ≫ φ' =
      (ModuleCat.extendScalars (g.appLE V V' h).hom).map ψ ≫ baseChangeTranspose g M V V' h := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro s
    have h1 := baseChangeTranspose_tmul g N V V' h 1 s
    have h2 := baseChangeTranspose_tmul g M V V' h 1 (i.app V s)
    dsimp only at h1 h2
    change ((AlgebraicGeometry.Scheme.Modules.pullback g).map i).app V'
        ((baseChangeTranspose g N V V' h).hom _) = (baseChangeTranspose g M V V' h).hom _
    refine (congrArg _ h1).trans (Eq.trans ?_ h2.symm)
    rw [one_smul, one_smul]
    exact pullback_map_app_pullbackSectionsOn g i V V' h s
  have hsq' : ∀ z, ((AlgebraicGeometry.Scheme.Modules.pullback g).map i).app V'
      ((baseChangeTranspose g N V V' h).hom z) =
      (baseChangeTranspose g M V V' h).hom (((ModuleCat.extendScalars (g.appLE V V' h).hom).map ψ).hom z) := by
    intro z
    have := congrArg (fun k => k.hom z) hsq
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    exact this
  -- `extendScalars (i.app V)` is injective by flatness
  have hinjL : Function.Injective ((ModuleCat.extendScalars (g.appLE V V' h).hom).map ψ).hom := by
    change Function.Injective (LinearMap.baseChange Γ(Y, V') ψ.hom)
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap ψ.hom hinj
  intro x x' hxx'
  obtain ⟨z, rfl⟩ := hN.2 x
  obtain ⟨z', rfl⟩ := hN.2 x'
  rw [hsq', hsq'] at hxx'
  rw [hinjL (hM.1 hxx')]

end

end AlgebraicGeometry.Scheme.Modules

end
