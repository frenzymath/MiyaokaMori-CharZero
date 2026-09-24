import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulePullbackStalkTensorBijective
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.Stacks00ae
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleStalkIso

/-! # The unit `F → ι_* ι^* F` is an isomorphism for sheaves killed by the ideal of `Z`

A sheaf of modules `F` on `X` supported on a closed subscheme `ι : Z → X` and killed, stalkwise, by the
kernel of `O_X → ι_* O_Z` is the pushforward of its pullback: `ι_* ι^* F ≅ F` (step 2 of Stacks 02OM,
the unit of the adjunction `ι^* ⊣ ι_*` is an isomorphism).

Edge cases: `F = 0` (both sides zero); `Z = ∅` (then `Supp F = ∅`, `F = 0`, and `ι_* ι^* F` is the zero
sheaf).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {Z X : AlgebraicGeometry.Scheme.{u}} (ι : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion ι]
  (F : X.Modules)

/-- **The pullback stalk unit `F_{ι z} → (ι^*F)_z` is bijective when `ker(O_{X,ι z} → O_{Z,z})` kills
`F_{ι z}`** (Stacks 01HS + `(A/K) ⊗_A M = M` for `KM = 0`).

Proof. Let `A = O_{X,ι z}`, `B = O_{Z,z}`, `φ = ι.stalkMap z : A → B` (surjective, kernel `K`), `M = F_{ι z}`.
The unit is `m ↦ 1 ⊗ m` followed by the bijection `B ⊗_A M → (ι^*F)_z`
(`MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorMap_bijective`, `modulePullbackStalkTensorMap_unit`).
`m ↦ 1 ⊗ m` is surjective since `φ a ⊗ m = 1 ⊗ a m`, and injective since
`B ⊗_A M ≅ (A ⧸ K) ⊗_A M ≅ M ⧸ K M` (`Ideal.quotientKerAlgEquivOfSurjective`,
`TensorProduct.quotTensorEquivQuotSMul`) and `K M = 0`. This is the computation of
`exists_pullback_stalk_addEquiv` (`Stacks02omPullbackStalk`) with the map made explicit. -/
theorem modulePullbackStalkUnit_bijective_of_ker_smul_eq_zero (z : Z)
    (hker : ∀ a ∈ RingHom.ker (ι.stalkMap z).hom, ∀ m : F.stalk (ι.base z), a • m = 0) :
    Function.Bijective (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit ι F z) := by
  let _ := AlgebraicGeometry.Scheme.Modules.modulePullbackStalkAlgebra ι z
  set φ : X.presheaf.stalk (ι.base z) →+* Z.presheaf.stalk z := (ι.stalkMap z).hom with hφdef
  have hφ : Function.Surjective φ := ι.stalkMap_surjective z
  have halg : ∀ a : X.presheaf.stalk (ι.base z),
      algebraMap (X.presheaf.stalk (ι.base z)) (Z.presheaf.stalk z) a = φ a :=
    fun a => DFunLike.congr_fun (RingHom.algebraMap_toAlgebra φ) a
  set T := AlgebraicGeometry.Scheme.Modules.modulePullbackStalkTensorMap ι F z with hT
  have hTbij : Function.Bijective T :=
    MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorMap_bijective ι F z
  -- the unit factors as `T ∘ (m ↦ 1 ⊗ m)`
  have hcomp : (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit ι F z : F.presheaf.stalk (ι.base z) → _) =
      T ∘ (fun m : F.presheaf.stalk (ι.base z) =>
        (1 : Z.presheaf.stalk z) ⊗ₜ[X.presheaf.stalk (ι.base z)] m) := by
    funext m
    exact (MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorMap_unit ι F z m).symm
  rw [hcomp, Function.Bijective.of_comp_iff' hTbij]
  -- key rewriting: φ a • (1 ⊗ m) = 1 ⊗ (a • m)
  have hsm : ∀ (a : X.presheaf.stalk (ι.base z)) (m : F.presheaf.stalk (ι.base z)),
      φ a • ((1 : Z.presheaf.stalk z) ⊗ₜ[X.presheaf.stalk (ι.base z)] m) =
        (1 : Z.presheaf.stalk z) ⊗ₜ[X.presheaf.stalk (ι.base z)] (a • m) := fun a m => by
    rw [TensorProduct.smul_tmul', smul_eq_mul, ← halg, ← Algebra.smul_def, TensorProduct.smul_tmul]
  refine ⟨?_, ?_⟩
  · -- injective, via `B ⊗ M ≅ (A ⧸ K) ⊗ M ≅ M ⧸ K•M = M`
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
    have h'' := congrArg Q h
    rw [hQ, hQ, Submodule.Quotient.eq, hKM] at h''
    exact sub_eq_zero.mp ((Submodule.mem_bot _).mp h'')
  · -- surjective
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
    | tmul b m =>
      obtain ⟨a, rfl⟩ := hφ b
      refine ⟨a • m, ?_⟩
      show (1 : Z.presheaf.stalk z) ⊗ₜ[X.presheaf.stalk (ι.base z)] (a • m) =
        φ a ⊗ₜ[X.presheaf.stalk (ι.base z)] m
      rw [← hsm, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add t₁ t₂ h₁ h₂ =>
      obtain ⟨m₁, hm₁⟩ := h₁
      obtain ⟨m₂, hm₂⟩ := h₂
      refine ⟨m₁ + m₂, ?_⟩
      show (1 : Z.presheaf.stalk z) ⊗ₜ[X.presheaf.stalk (ι.base z)] (m₁ + m₂) = t₁ + t₂
      rw [TensorProduct.tmul_add]
      exact congrArg₂ (· + ·) hm₁ hm₂

/-- **Stalks of `ι_* G` vanish off `ι(Z)`** for a closed immersion `ι` and `G` on `Z` (Stacks 00AE,
`TopCat.Sheaf.isZero_stalk_pushforward_of_notMem_range` applied to the underlying abelian sheaf). -/
theorem subsingleton_pushforward_stalk_of_notMem_range (G : Z.Modules) (x : X)
    (hx : x ∉ Set.range ι.base) :
    Subsingleton (((AlgebraicGeometry.Scheme.Modules.pushforward ι).obj G).presheaf.stalk x) :=
  AddCommGrpCat.subsingleton_of_isZero
    (TopCat.Sheaf.isZero_stalk_pushforward_of_notMem_range ι.base ι.isClosedEmbedding
      ⟨G.presheaf, G.isSheaf⟩ x hx)

omit [AlgebraicGeometry.IsClosedImmersion ι] in
set_option backward.isDefEq.respectTransparency false in
/-- The stalk map of the adjunction unit `F → ι_* ι^* F` at `ι z`, followed by the stalk-pushforward map
`(ι_* ι^* F)_{ι z} → (ι^* F)_z`, is the pullback stalk unit `AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit ι F z`
(definitional: this composite is how `AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom` is defined). -/
theorem stalkPushforward_moduleStalkMap_unit (z : Z) (m : F.presheaf.stalk (ι.base z)) :
    TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} ι.base
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj F).presheaf z
      (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X (ι.base z)
        ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app F) m) =
      AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit ι F z m := rfl

/-- **`ι_* ι^* F ≅ F` for a sheaf killed by the ideal of a closed subscheme** (Stacks 02OM, step 2).
Hypotheses: for every `z`, `ker(O_{X,ι z} → O_{Z,z})` kills `F_{ι z}`; and `Supp F ⊆ ι(Z)`.

Proof. Let `u : F → ι_* ι^* F` be the unit of `pullbackPushforwardAdjunction ι` at `F`; it suffices that `u`
is bijective on every stalk (`AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective`).
* `x ∉ ι(Z)`: `(ι_* G)_x = 0` for every `G` on `Z` (Stacks 00AE, `TopCat.Sheaf.isZero_stalk_pushforward_of_notMem_range`,
  applied to the underlying abelian sheaf), and `F_x = 0` because `x ∉ Supp F`; a map between zero modules is
  bijective.
* `x = ι z`: the stalk map of `u` at `ι z` followed by the stalk-pushforward isomorphism
  `(ι_* ι^* F)_{ι z} ≅ (ι^* F)_z` (Stacks 00AE for the closed embedding `ι`,
  `TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing`) is
  `AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit ι F z : F_{ι z} → (ι^* F)_z` (definitionally: that is how
  `modulePullbackStalkUnitAddHom` is defined), i.e. `m ↦ 1 ⊗ m` under
  `(ι^* F)_z ≅ O_{Z,z} ⊗_{O_{X,ι z}} F_{ι z}` (`modulePullbackStalkTensorMap_bijective`,
  `modulePullbackStalkTensorMap_unit`). Since `O_{X,ι z} → O_{Z,z}` is surjective with kernel `K` and
  `K F_{ι z} = 0`, `m ↦ 1 ⊗ m` is bijective (`(A/K) ⊗_A M ≅ M/KM = M`;
  `modulePullbackStalkUnit_bijective_of_ker_smul_eq_zero`). -/
theorem nonempty_pushforward_pullback_iso
    (hker : ∀ z : Z, ∀ a ∈ RingHom.ker (ι.stalkMap z).hom, ∀ m : F.stalk (ι.base z), a • m = 0)
    (hsupp : F.support ⊆ Set.range ι.base) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pushforward ι).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj F) ≅ F) := by
  set u := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app F with hu
  have hiso : IsIso u := by
    rw [AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective]
    intro x
    by_cases hx : x ∈ Set.range ι.base
    · obtain ⟨z, rfl⟩ := hx
      -- compose with the stalk-pushforward bijection `(ι_* ι^* F)_{ι z} → (ι^* F)_z`
      set S := TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} ι.base
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj F).presheaf z with hS
      have hSbij : Function.Bijective S := by
        have := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{u}
          ι.isClosedEmbedding.isInducing ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj F).presheaf z
        exact ConcreteCategory.bijective_of_isIso _
      have key : Function.Bijective (fun m => S (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X (ι.base z) u m)) := by
        have hcomp : (fun m => S (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X (ι.base z) u m)) =
            AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit ι F z := by
          funext m
          exact stalkPushforward_moduleStalkMap_unit ι F z m
        rw [hcomp]
        exact modulePullbackStalkUnit_bijective_of_ker_smul_eq_zero ι F z (hker z)
      exact (Function.Bijective.of_comp_iff' hSbij (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X (ι.base z) u)).mp key
    · -- both stalks vanish
      have h1 : Subsingleton (F.presheaf.stalk x) := by
        have : ¬ Nontrivial (F.stalk x) := fun h => hx (hsupp h)
        exact not_nontrivial_iff_subsingleton.mp this
      have h2 := subsingleton_pushforward_stalk_of_notMem_range ι
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj F) x hx
      exact ⟨fun a b _ => @Subsingleton.elim _ h1 a b, fun b => ⟨0, @Subsingleton.elim _ h2 _ _⟩⟩
  exact ⟨(asIso u).symm⟩

end AlgebraicGeometry.Scheme.Modules

end
