import MiyaokaMori.Prelude
import MiyaokaMori.Algebra.DetWedgeAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorTensorStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkCriteria
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleStalkIso

/-! # The wedge map of a short exact sequence, scheme-level form

The **general scheme-level form** (no `VectorBundle`) of steps 2 and 3 of `DetOfShortExact`: for a
short exact sequence `0 → A →i B →p C → 0` on any scheme `X` such that the stalks of `A` and `C` at
every point have bases indexed by `Fin a` and `Fin b` respectively,

* `exists_detWedgeMap_aux`: there is `μ : Λ^a A ⊗ Λ^b C ⟶ Λ^{a+b} B` with
  `(1 ⊗ Λ^b p) ≫ μ = (Λ^a i ⊗ 1) ≫ (wedge multiplication)`;
* `isIso_detWedgeMap_aux`: any `μ` satisfying this equation is an isomorphism.

**Proof (entirely on stalks)**

1. `X.Modules` is abelian (Mathlib's `Abelian` instance for `SheafOfModules`). Write
   `q := 1 ⊗ Λ^b p` and `c := (Λ^a i ⊗ 1) ≫ (wedge multiplication)`. `q` is an epimorphism (surjective on
   stalks, `epi_of_stalkMap_surjective`) and `ker q ≫ c = 0` (checked on stalks, `hom_ext_of_stalkMap`),
   so `μ := Abelian.epiDesc q c` satisfies `q ≫ μ = c`.
2. On the stalk at a point `x`, by the conjugation formulas of `ExteriorTensorStalk`, `q_x`, `c_x`, `μ_x`
   become the module-level `1 ⊗ ⋀^b p_x`, `(wedge multiplication) ∘ (⋀^a i_x ⊗ 1)`, `μ'`; the sequence of
   stalks is exact, injective on the left and surjective on the right (`stalkMap_exact_of_shortExact`
   etc.), and `C_x` is free so `p_x` has a section `σ`.
3. Then surjectivity of `q_x`, `ker q_x ⊆ ker c_x` and bijectivity of `μ'` are
   `exteriorPower_map_surjective`, `mul_map_eq_zero_of_map_eq_zero`, `bijective_of_comp_eq` of
   `DetWedgeAlgebra`; `μ` is an isomorphism by `AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective`.

Source: Stacks 0FJB, steps 2 and 3 of the proof.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace MiyaokaMori.DetWedgeMapAux

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules MiyaokaMori.ExteriorTensorStalk MiyaokaMori.ModulesStalkCriteria
  MiyaokaMori.DetWedgeAlgebra

set_option backward.isDefEq.respectTransparency false

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- A surjection onto a free module has a linear section (choose preimages of basis vectors). -/
theorem exists_section_of_surjective {R : Type*} [CommRing R] {M M'' ι : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M''] [Module R M'']
    {g : M →ₗ[R] M''} (hg : Function.Surjective g) (e'' : Module.Basis ι R M'') :
    ∃ σ : M'' →ₗ[R] M, g ∘ₗ σ = LinearMap.id := by
  refine ⟨e''.constr R (fun j => Function.surjInv hg (e'' j)), e''.ext fun j => ?_⟩
  simp only [LinearMap.comp_apply, Module.Basis.constr_basis, Function.surjInv_eq,
    LinearMap.id_apply]

/-- Conjugation on stalks of a tensor of morphisms of exterior power sheaves: if `φ'`, `ψ'` are
conjugate on stalks to `α`, `β`, then `φ' ⊗ ψ'` is conjugate to `α ⊗ β`. -/
theorem stalk_tensorMap_conj {A A' B B' : X.Modules} {a b : ℕ}
    (φ' : AlgebraicGeometry.Scheme.Modules.exteriorPower A a ⟶
      AlgebraicGeometry.Scheme.Modules.exteriorPower A' a)
    (ψ' : AlgebraicGeometry.Scheme.Modules.exteriorPower B b ⟶
      AlgebraicGeometry.Scheme.Modules.exteriorPower B' b) (x : X)
    (α : (⋀[X.presheaf.stalk x]^a (A.presheaf.stalk x)) →ₗ[X.presheaf.stalk x]
      (⋀[X.presheaf.stalk x]^a (A'.presheaf.stalk x)))
    (β : (⋀[X.presheaf.stalk x]^b (B.presheaf.stalk x)) →ₗ[X.presheaf.stalk x]
      (⋀[X.presheaf.stalk x]^b (B'.presheaf.stalk x)))
    (hφ : ∀ m, moduleExteriorPowerStalkEquiv X A' x a (moduleStalkMap X x φ' m) =
      α (moduleExteriorPowerStalkEquiv X A x a m))
    (hψ : ∀ n, moduleExteriorPowerStalkEquiv X B' x b (moduleStalkMap X x ψ' n) =
      β (moduleExteriorPowerStalkEquiv X B x b n))
    (z : (AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.exteriorPower A a)
        (AlgebraicGeometry.Scheme.Modules.exteriorPower B b)).presheaf.stalk x) :
    exteriorTensorStalkEquiv A' B' a b x
        (moduleStalkMap X x (AlgebraicGeometry.Scheme.Modules.tensorMap φ' ψ') z) =
      TensorProduct.map α β (exteriorTensorStalkEquiv A B a b x z) := by
  have h := stalkMap_tensorMap φ' ψ' x z
  unfold exteriorTensorStalkEquiv
  simp only [LinearEquiv.trans_apply]
  rw [h]
  induction tensorStalkEquiv' _ _ x z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m n =>
    rw [TensorProduct.map_tmul, TensorProduct.congr_tmul, TensorProduct.congr_tmul,
      TensorProduct.map_tmul]
    exact congrArg₂ (fun u v => u ⊗ₜ[X.presheaf.stalk x] v) (hφ m) (hψ n)
  | add s t hs ht => rw [map_add, map_add, map_add, map_add, hs, ht]

section Sequence

variable {A B C : X.Modules} {a b : ℕ} (i : A ⟶ B) (p : B ⟶ C)

/-- `q := 1 ⊗ Λ^b p` is conjugate on stalks to `1 ⊗ ⋀^b p_x`. -/
theorem stalk_q (x : X)
    (z : (AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.exteriorPower A a)
        (AlgebraicGeometry.Scheme.Modules.exteriorPower B b)).presheaf.stalk x) :
    exteriorTensorStalkEquiv A C a b x
        (moduleStalkMap X x (AlgebraicGeometry.Scheme.Modules.tensorMap (𝟙 _)
          (AlgebraicGeometry.Scheme.Modules.exteriorMap p b)) z) =
      TensorProduct.map LinearMap.id (exteriorPower.map b (moduleStalkMap X x p))
        (exteriorTensorStalkEquiv A B a b x z) := by
  refine stalk_tensorMap_conj _ _ x _ _ (fun m => ?_) (fun n => stalkMap_exteriorMap p b x n) z
  rw [moduleStalkMap_id_apply, LinearMap.id_apply]

/-- `c := (Λ^a i ⊗ 1) ≫ mul` is conjugate on stalks to `mul ∘ (⋀^a i_x ⊗ 1)`. -/
theorem stalk_c (x : X)
    (z : (AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.exteriorPower A a)
        (AlgebraicGeometry.Scheme.Modules.exteriorPower B b)).presheaf.stalk x) :
    moduleExteriorPowerStalkEquiv X B x (a + b)
        (moduleStalkMap X x (AlgebraicGeometry.Scheme.Modules.tensorMap
          (AlgebraicGeometry.Scheme.Modules.exteriorMap i a) (𝟙 _) ≫
            AlgebraicGeometry.Scheme.Modules.exteriorPowerMul B a b) z) =
      Module.exteriorPowerMul (X.presheaf.stalk x) (B.presheaf.stalk x) a b
        (TensorProduct.map (exteriorPower.map a (moduleStalkMap X x i)) LinearMap.id
          (exteriorTensorStalkEquiv A B a b x z)) := by
  rw [moduleStalkMap_comp_apply, stalkMap_exteriorPowerMul]
  congr 1
  refine stalk_tensorMap_conj _ _ x _ _ (fun m => stalkMap_exteriorMap i a x m) (fun n => ?_) z
  rw [moduleStalkMap_id_apply, LinearMap.id_apply]

variable (h0 : i ≫ p = 0) (hS : (CategoryTheory.ShortComplex.mk i p h0).ShortExact)
  (hA : ∀ x : X, Nonempty (Module.Basis (Fin a) (X.presheaf.stalk x) (A.presheaf.stalk x)))
  (hC : ∀ x : X, Nonempty (Module.Basis (Fin b) (X.presheaf.stalk x) (C.presheaf.stalk x)))

include hS hA hC

/-- **Step 2 (general form)**: the wedge map is well defined. -/
theorem exists_detWedgeMap_aux :
    ∃ μ : AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.exteriorPower A a)
        (AlgebraicGeometry.Scheme.Modules.exteriorPower C b) ⟶
      AlgebraicGeometry.Scheme.Modules.exteriorPower B (a + b),
      AlgebraicGeometry.Scheme.Modules.tensorMap (CategoryTheory.CategoryStruct.id _)
          (AlgebraicGeometry.Scheme.Modules.exteriorMap p b) ≫ μ =
        AlgebraicGeometry.Scheme.Modules.tensorMap
            (AlgebraicGeometry.Scheme.Modules.exteriorMap i a) (CategoryTheory.CategoryStruct.id _) ≫
          AlgebraicGeometry.Scheme.Modules.exteriorPowerMul B a b := by
  set q := AlgebraicGeometry.Scheme.Modules.tensorMap (𝟙 (AlgebraicGeometry.Scheme.Modules.exteriorPower A a))
    (AlgebraicGeometry.Scheme.Modules.exteriorMap p b) with hq
  set c := AlgebraicGeometry.Scheme.Modules.tensorMap (AlgebraicGeometry.Scheme.Modules.exteriorMap i a)
      (𝟙 (AlgebraicGeometry.Scheme.Modules.exteriorPower B b)) ≫
    AlgebraicGeometry.Scheme.Modules.exteriorPowerMul B a b with hc
  -- `q` is an epimorphism
  have hepi : Epi q := by
    apply epi_of_stalkMap_surjective
    intro x w
    have hp : Function.Surjective (moduleStalkMap X x p) := stalkMap_surjective_of_shortExact hS x
    have hsurj : Function.Surjective (TensorProduct.map
        (LinearMap.id : (⋀[X.presheaf.stalk x]^a (A.presheaf.stalk x)) →ₗ[X.presheaf.stalk x] _)
        (exteriorPower.map b (moduleStalkMap X x p))) :=
      LinearMap.lTensor_surjective _ (exteriorPower_map_surjective hp)
    obtain ⟨t', ht'⟩ := hsurj (exteriorTensorStalkEquiv A C a b x w)
    refine ⟨(exteriorTensorStalkEquiv A B a b x).symm t', ?_⟩
    apply (exteriorTensorStalkEquiv A C a b x).injective
    rw [hq, stalk_q, LinearEquiv.apply_symm_apply, ht']
  -- `ker q ≫ c = 0`
  have hker : kernel.ι q ≫ c = 0 := by
    apply hom_ext_of_stalkMap
    intro x
    refine LinearMap.ext fun z => ?_
    rw [moduleStalkMap_comp_apply, moduleStalkMap_zero_apply]
    set y := moduleStalkMap X x (kernel.ι q) z with hy
    have hqy : moduleStalkMap X x q y = 0 := by
      rw [hy, ← moduleStalkMap_comp_apply, kernel.condition, moduleStalkMap_zero_apply]
    obtain ⟨e'⟩ := hA x
    obtain ⟨e''⟩ := hC x
    have hexact := stalkMap_exact_of_shortExact hS x
    have hf := stalkMap_injective_of_shortExact hS x
    have hp : Function.Surjective (moduleStalkMap X x p) := stalkMap_surjective_of_shortExact hS x
    obtain ⟨σ, hσ⟩ := exists_section_of_surjective hp e''
    apply (moduleExteriorPowerStalkEquiv X B x (a + b)).injective
    rw [map_zero, hc, stalk_c]
    apply mul_map_eq_zero_of_map_eq_zero hexact hf σ hσ e' e''
    rw [← stalk_q, hqy, map_zero]
  exact ⟨Abelian.epiDesc q c hker, Abelian.comp_epiDesc q c hker⟩

/-- **Step 3 (general form)**: a `μ` satisfying the equation of step 2 is an isomorphism. -/
theorem isIso_detWedgeMap_aux
    (μ : AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.exteriorPower A a)
        (AlgebraicGeometry.Scheme.Modules.exteriorPower C b) ⟶
      AlgebraicGeometry.Scheme.Modules.exteriorPower B (a + b))
    (hμ : AlgebraicGeometry.Scheme.Modules.tensorMap (CategoryTheory.CategoryStruct.id _)
          (AlgebraicGeometry.Scheme.Modules.exteriorMap p b) ≫ μ =
        AlgebraicGeometry.Scheme.Modules.tensorMap
            (AlgebraicGeometry.Scheme.Modules.exteriorMap i a) (CategoryTheory.CategoryStruct.id _) ≫
          AlgebraicGeometry.Scheme.Modules.exteriorPowerMul B a b) :
    CategoryTheory.IsIso μ := by
  rw [moduleHom_isIso_iff_stalk_bijective]
  intro x
  obtain ⟨e'⟩ := hA x
  obtain ⟨e''⟩ := hC x
  have hexact := stalkMap_exact_of_shortExact hS x
  have hf := stalkMap_injective_of_shortExact hS x
  have hp : Function.Surjective (moduleStalkMap X x p) := stalkMap_surjective_of_shortExact hS x
  obtain ⟨σ, hσ⟩ := exists_section_of_surjective hp e''
  let μ' : ((⋀[X.presheaf.stalk x]^a (A.presheaf.stalk x)) ⊗[X.presheaf.stalk x]
      (⋀[X.presheaf.stalk x]^b (C.presheaf.stalk x))) →ₗ[X.presheaf.stalk x]
      ⋀[X.presheaf.stalk x]^(a + b) (B.presheaf.stalk x) :=
    (moduleExteriorPowerStalkEquiv X B x (a + b)).toLinearMap ∘ₗ moduleStalkMap X x μ ∘ₗ
      (exteriorTensorStalkEquiv A C a b x).symm.toLinearMap
  have hμ' : ∀ t, μ' (TensorProduct.map LinearMap.id (exteriorPower.map b (moduleStalkMap X x p)) t) =
      Module.exteriorPowerMul (X.presheaf.stalk x) (B.presheaf.stalk x) a b
        (TensorProduct.map (exteriorPower.map a (moduleStalkMap X x i)) LinearMap.id t) := by
    intro t
    set y := (exteriorTensorStalkEquiv A B a b x).symm t with hy
    have ht : t = exteriorTensorStalkEquiv A B a b x y := by rw [hy, LinearEquiv.apply_symm_apply]
    rw [ht, ← stalk_q, ← stalk_c]
    simp only [μ', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [← moduleStalkMap_comp_apply, hμ]
  have hbij := bijective_of_comp_eq hexact hf σ hσ e' e'' hp μ' hμ'
  have hcomp : ⇑(moduleStalkMap X x μ) = ⇑(moduleExteriorPowerStalkEquiv X B x (a + b)).symm ∘
      ⇑μ' ∘ ⇑(exteriorTensorStalkEquiv A C a b x) := by
    funext z
    simp only [μ', Function.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  rw [hcomp]
  exact (moduleExteriorPowerStalkEquiv X B x (a + b)).symm.bijective.comp
    (hbij.comp (exteriorTensorStalkEquiv A C a b x).bijective)

end Sequence

end MiyaokaMori.DetWedgeMapAux

end
