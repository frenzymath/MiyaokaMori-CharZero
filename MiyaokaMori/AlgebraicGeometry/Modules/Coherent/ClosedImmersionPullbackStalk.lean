import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.ModulesAssociatedPoints
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.RingTheory.Localization.AssociatedPrimesComapSurjective
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulePullbackStalkTensorBijective

/-! # Stalks of the pullback along a closed immersion

Stalks of `ι^* F` for a closed immersion `ι : Z → X` and a sheaf `F` on `X` whose stalk at `ι z` is killed by
`ker(O_{X,ι z} → O_{Z,z})` (step 2 of Stacks 02OM, applied to `F` and its annihilator
subscheme):

* `exists_pullback_stalk_addEquiv`:
  `(ι^*F)_z ≅ F_{ι z}` additively, semilinearly for `φ = ι.stalkMap z` (`e (φ a • g) = a • e g`);
* `isAssociatedPoint_pullback_iff`: `z ∈ Ass(ι^*F) ↔ ι z ∈ Ass(F)`;
* `mem_support_pullback_iff`: `z ∈ Supp(ι^*F) ↔ ι z ∈ Supp F`.

The two consequences follow from the semilinear equivalence: `φ` is surjective (closed immersions are
surjective on stalks) and local, so `Ass_A(F_{ι z}) = Ass_A((ι^*F)_z) = φ⁻¹(Ass_B((ι^*F)_z))`
(`LinearEquiv.AssociatedPrimes.eq`, `associatedPrimes_eq_comap_image`), and `φ⁻¹(𝔪_B) = 𝔪_A`
(`IsLocalRing.maximalIdeal_comap`) with `φ⁻¹` injective (`Ideal.comap_injective_of_surjective`).

Source: Stacks 02OM; Stacks 01HS (pullback stalk `(ι^*F)_z = O_{Z,z} ⊗ F_{ι z}`); `(A/K) ⊗_A M ≅ M/KM`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {Z X : AlgebraicGeometry.Scheme.{u}} (ι : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion ι]
  (F : X.Modules) (z : Z)

/-- **Stalk of the pullback along a closed immersion when the kernel kills the stalk** (Stacks 01HS +
`(A/K) ⊗_A M = M` for `KM = 0`). Let `A = O_{X,ι z}`, `B = O_{Z,z}`, `φ = ι.stalkMap z : A → B`
(surjective, kernel `K`), `M = F_{ι z}` with `K M = 0`. Then `(ι^*F)_z ≃+ M` by an equivalence `e` with
`e (φ a • g) = a • e g`.

Proof. `MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv ι F z` is a `B`-linear equivalence
`B ⊗_A M ≃ (ι^*F)_z` (with `B` an `A`-algebra through `φ`). Since `φ` is surjective with kernel `K` and
`K M = 0`, the map `M → B ⊗_A M`, `m ↦ 1 ⊗ m`, is bijective: surjective because `φ a ⊗ m = 1 ⊗ a m`
(`TensorProduct.tmul_eq_smul_one_tmul`-type rewriting through `algebraMap = φ`), injective because
`B ⊗_A M ≅ (A ⧸ K) ⊗_A M ≅ M ⧸ K M ≅ M` (`Ideal.Quotient.tensorProductEquiv`-style: Mathlib
`TensorProduct.quotTensorEquivQuotSMul` / `Ideal.quotientKerAlgEquivOfSurjective`), and `K • M = ⊥` by
hypothesis. Compose to get `e`; `e (φ a • g) = a • e g` follows from `φ a • (1 ⊗ m) = φ a ⊗ m = 1 ⊗ a m`. -/
theorem exists_pullback_stalk_addEquiv
    (hker : ∀ a ∈ RingHom.ker (ι.stalkMap z).hom, ∀ m : F.stalk (ι.base z), a • m = 0) :
    ∃ e : ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj F).stalk z ≃+ F.stalk (ι.base z),
      ∀ (a : X.presheaf.stalk (ι.base z)) (g : ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj F).stalk z),
        e (ι.stalkMap z a • g) = a • e g := by
  letI := AlgebraicGeometry.Scheme.Modules.modulePullbackStalkAlgebra ι z
  set φ : X.presheaf.stalk (ι.base z) →+* Z.presheaf.stalk z := (ι.stalkMap z).hom with hφdef
  have hφ : Function.Surjective φ := ι.stalkMap_surjective z
  have halg : ∀ a : X.presheaf.stalk (ι.base z),
      algebraMap (X.presheaf.stalk (ι.base z)) (Z.presheaf.stalk z) a = φ a :=
    fun a => DFunLike.congr_fun (RingHom.algebraMap_toAlgebra φ) a
  let T := MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv ι F z
  -- ψ m := T (1 ⊗ m)
  let ψ : F.presheaf.stalk (ι.base z) →+ ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj F).stalk z :=
    { toFun := fun m => T ((1 : Z.presheaf.stalk z) ⊗ₜ[X.presheaf.stalk (ι.base z)] m)
      map_zero' := by rw [TensorProduct.tmul_zero, map_zero]; try rfl
      map_add' := fun m m' => by rw [TensorProduct.tmul_add, map_add]; try rfl }
  -- key rewriting: φ a • (1 ⊗ m) = 1 ⊗ (a • m)
  have hsm : ∀ (a : X.presheaf.stalk (ι.base z)) (m : F.presheaf.stalk (ι.base z)),
      φ a • ((1 : Z.presheaf.stalk z) ⊗ₜ[X.presheaf.stalk (ι.base z)] m) =
        (1 : Z.presheaf.stalk z) ⊗ₜ[X.presheaf.stalk (ι.base z)] (a • m) := fun a m => by
    rw [TensorProduct.smul_tmul', smul_eq_mul, ← halg, ← Algebra.smul_def, TensorProduct.smul_tmul]
  -- surjective
  have hsurj : Function.Surjective ψ := by
    intro n
    obtain ⟨t, rfl⟩ := T.surjective n
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero]; try rfl⟩
    | tmul b m =>
      obtain ⟨a, rfl⟩ := hφ b
      refine ⟨a • m, ?_⟩
      show T ((1 : Z.presheaf.stalk z) ⊗ₜ[X.presheaf.stalk (ι.base z)] (a • m)) =
        T (φ a ⊗ₜ[X.presheaf.stalk (ι.base z)] m)
      rw [← hsm, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add t₁ t₂ h₁ h₂ =>
      obtain ⟨m₁, hm₁⟩ := h₁
      obtain ⟨m₂, hm₂⟩ := h₂
      exact ⟨m₁ + m₂, by rw [map_add, hm₁, hm₂, map_add]; try rfl⟩
  -- injective, via `B ⊗ M ≅ (A ⧸ K) ⊗ M ≅ M ⧸ K•M = M`
  have hinj : Function.Injective ψ := by
    have hφ' : Function.Surjective (Algebra.ofId (X.presheaf.stalk (ι.base z)) (Z.presheaf.stalk z)) := hφ
    let eAK := (Ideal.quotientKerAlgEquivOfSurjective hφ').toLinearEquiv
    set K : Ideal (X.presheaf.stalk (ι.base z)) :=
      RingHom.ker (Algebra.ofId (X.presheaf.stalk (ι.base z)) (Z.presheaf.stalk z)) with hK
    have hKM : (K • (⊤ : Submodule (X.presheaf.stalk (ι.base z)) (F.presheaf.stalk (ι.base z)))) = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun m hm => ?_
      refine Submodule.smul_induction_on hm (fun k hk m _ => hker k hk m) (fun x y hx hy => ?_)
      rw [hx, hy, add_zero]
    let Q : (Z.presheaf.stalk z ⊗[X.presheaf.stalk (ι.base z)] F.presheaf.stalk (ι.base z)) ≃ₗ[X.presheaf.stalk (ι.base z)]
        F.presheaf.stalk (ι.base z) ⧸ (K • (⊤ : Submodule (X.presheaf.stalk (ι.base z)) (F.presheaf.stalk (ι.base z)))) :=
      (TensorProduct.congr eAK.symm (LinearEquiv.refl (X.presheaf.stalk (ι.base z)) (F.presheaf.stalk (ι.base z)))).trans
        (TensorProduct.quotTensorEquivQuotSMul (F.presheaf.stalk (ι.base z)) K)
    have hQ : ∀ m : F.presheaf.stalk (ι.base z),
        Q ((1 : Z.presheaf.stalk z) ⊗ₜ[X.presheaf.stalk (ι.base z)] m) = Submodule.Quotient.mk m := by
      intro m
      have h1 : eAK.symm (1 : Z.presheaf.stalk z) = Ideal.Quotient.mk K 1 := by
        rw [LinearEquiv.symm_apply_eq]
        show (1 : Z.presheaf.stalk z) = Ideal.quotientKerAlgEquivOfSurjective hφ' (Ideal.Quotient.mk K 1)
        rw [map_one, map_one]
      simp only [Q, LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply, h1,
        TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
    intro m m' h
    have h' : T ((1 : Z.presheaf.stalk z) ⊗ₜ[X.presheaf.stalk (ι.base z)] m) =
        T ((1 : Z.presheaf.stalk z) ⊗ₜ[X.presheaf.stalk (ι.base z)] m') := h
    have h'' := congrArg Q (T.injective h')
    rw [hQ, hQ, Submodule.Quotient.eq, hKM] at h''
    exact sub_eq_zero.mp ((Submodule.mem_bot _).mp h'')
  have hbij : Function.Bijective ψ := ⟨hinj, hsurj⟩
  set e := AddEquiv.ofBijective ψ hbij with he
  refine ⟨e.symm, fun a g => ?_⟩
  obtain ⟨m, rfl⟩ := hsurj g
  have hg' : φ a • ψ m = ψ (a • m) := by
    show φ a • T ((1 : Z.presheaf.stalk z) ⊗ₜ[X.presheaf.stalk (ι.base z)] m) =
      T ((1 : Z.presheaf.stalk z) ⊗ₜ[X.presheaf.stalk (ι.base z)] (a • m))
    rw [← _root_.map_smul T (φ a), hsm]
  have h1 : e.symm (ψ (a • m)) = a • m := e.symm_apply_apply (a • m)
  have h2 : e.symm (ψ m) = m := e.symm_apply_apply m
  show e.symm (φ a • ψ m) = a • e.symm (ψ m)
  rw [hg', h1, h2]

/-- `z` is an associated point of `ι^*F` iff `ι z` is an associated point of `F` (when the kernel of
`O_{X,ι z} → O_{Z,z}` kills `F_{ι z}`). -/
theorem isAssociatedPoint_pullback_iff
    (hker : ∀ a ∈ RingHom.ker (ι.stalkMap z).hom, ∀ m : F.stalk (ι.base z), a • m = 0) :
    ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj F).IsAssociatedPoint z ↔
      F.IsAssociatedPoint (ι.base z) := by
  obtain ⟨e, he⟩ := exists_pullback_stalk_addEquiv ι F z hker
  set φ : X.presheaf.stalk (ι.base z) →+* Z.presheaf.stalk z := (ι.stalkMap z).hom with hφdef
  have hφ : Function.Surjective φ := ι.stalkMap_surjective z
  let N : Type u := (((AlgebraicGeometry.Scheme.Modules.pullback ι).obj F).stalk z : Type u)
  let _ : Module (X.presheaf.stalk (ι.base z)) N := Module.compHom N φ
  have hsmul : ∀ (a : X.presheaf.stalk (ι.base z)) (n : N), a • n = φ a • n :=
    fun _ _ => rfl
  let eA : N ≃ₗ[X.presheaf.stalk (ι.base z)] F.stalk (ι.base z) :=
    { e with map_smul' := fun a n => he a n }
  have hAss := LinearEquiv.AssociatedPrimes.eq eA
  have hcomap := MiyaokaMori.AssociatedPrimesComap.associatedPrimes_eq_comap_image φ hφ hsmul
  unfold AlgebraicGeometry.Scheme.Modules.IsAssociatedPoint
  rw [← hAss, hcomap]
  constructor
  · intro h
    exact ⟨_, h, IsLocalRing.maximalIdeal_comap φ⟩
  · rintro ⟨J, hJ, hJeq⟩
    rw [← IsLocalRing.maximalIdeal_comap φ] at hJeq
    rwa [Ideal.comap_injective_of_surjective φ hφ hJeq] at hJ

/-- `z ∈ Supp(ι^*F) ↔ ι z ∈ Supp F` (when the kernel of `O_{X,ι z} → O_{Z,z}` kills `F_{ι z}`). -/
theorem mem_support_pullback_iff
    (hker : ∀ a ∈ RingHom.ker (ι.stalkMap z).hom, ∀ m : F.stalk (ι.base z), a • m = 0) :
    z ∈ ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj F).support ↔ ι.base z ∈ F.support := by
  obtain ⟨e, -⟩ := exists_pullback_stalk_addEquiv ι F z hker
  exact e.toEquiv.nontrivial_congr

end AlgebraicGeometry.Scheme.Modules

end
