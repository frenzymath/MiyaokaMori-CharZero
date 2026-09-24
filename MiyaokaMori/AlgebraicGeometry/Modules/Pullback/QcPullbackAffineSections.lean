import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.AffineTildeAdjunction

/-! # Pullback of quasi-coherent sheaves between affine schemes and base change of sections

Stacks 01I9: for a morphism `g : V → U` of affine schemes and `F` quasi-coherent on `U`,
`Γ(V, g^*F) ≅ O(V) ⊗_{O(U)} Γ(U, F)`, naturally in `F`. The mathematical content
(`pullbackSectionsTensorMap_bijective`) is proved with the tilde–Γ adjunction transported to
affine schemes (`AffineTildeAdjunction.lean`); see the docstring of that theorem for the argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped AlgebraicGeometry

/-- The canonical map `Γ(V) ⊗_{Γ(U)} Γ(F) → Γ(g^*F)`, `v ⊗ s ↦ v · g^*s`, where `g^*s` is the value at
`⊤` of the unit of the pullback–pushforward adjunction (`AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback`); it is
semilinear along `g.appTop` (the unit is a morphism of `O_U`-modules), so it extends to the tensor
product (`liftBaseChange`). The algebra structure `Γ(U,⊤) → Γ(V,⊤)` is `g.appTop`, and sections
of modules are written `Γ(M, W)`. Defined for arbitrary `g`, `F`; no affineness or
quasi-coherence is needed. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.pullbackSectionsTensorMap {V U : AlgebraicGeometry.Scheme.{u}}
    (g : V ⟶ U) (F : U.Modules) :
    letI : Algebra Γ(U, ⊤) Γ(V, ⊤) := g.appTop.hom.toAlgebra
    TensorProduct Γ(U, ⊤) Γ(V, ⊤) Γ(F, ⊤) →ₗ[Γ(V, ⊤)]
      Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj F, ⊤) :=
  letI : Algebra Γ(U, ⊤) Γ(V, ⊤) := g.appTop.hom.toAlgebra
  letI := Module.compHom Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj F, ⊤)
    (algebraMap Γ(U, ⊤) Γ(V, ⊤))
  letI : IsScalarTower Γ(U, ⊤) Γ(V, ⊤) Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj F, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  LinearMap.liftBaseChange Γ(V, ⊤)
    { toFun := AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback g
      map_add' := map_add _
      map_smul' := fun r s ↦
        AlgebraicGeometry.Scheme.Modules.Hom.app_smul
          ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F) r s }

open AlgebraicGeometry.Scheme.Modules.AffineTilde in
/-- **Stacks 01I9, global affine version.**
`V = Spec B`, `U = Spec A` affine, `F` quasi-coherent: the canonical map
`B ⊗_A Γ(U, F) → Γ(V, g^*F)` (`pullbackSectionsTensorMap`) is bijective.

Proof (adjunctions only; no computation of `g^*` is needed). Write `R = Γ(U,⊤)`, `S = Γ(V,⊤)`,
`M = Γ(F,⊤)`, `N = g^*F`, `W = S ⊗_R M`, `Φ : W → Γ(N,⊤)` the canonical map, and use the tilde–Γ
adjunction on the affine schemes `V` and `U` (`AffineTilde.adj`, Mathlib's `tilde.adjunction` transported
along `isoSpec`; unit elements `η(w) = unitEl W w ∈ Γ(V, T_V W)`):
1. `Ψ : T_V W ⟶ N` is the adjoint of `Φ`; on global sections `Ψ(η(w)) = Φ w` (`homEquiv_apply`).
2. `θ₀ : M → Γ(V, T_V W)`, `m ↦ η(1 ⊗ m)`, is `R`-linear (`R` acting through `g^♯`); since `F` is
   quasi-coherent on the affine `U`, it is induced by a morphism `θ' : F ⟶ g_* T_V W`
   (`exists_hom_of_linear`), whose adjoint is `Θ : N ⟶ T_V W`; the unit formula gives `Θ(g^*m) = η(1 ⊗ m)`.
3. `Ψ ≫ Θ = 𝟙`: maps out of `T_V W` are determined by their values on the `η(w)` (`T_hom_ext`); by
   `S`-linearity it suffices to take `w = 1 ⊗ m`, where both sides give `η(1 ⊗ m)`.
4. `Θ ≫ Ψ = 𝟙`: by the pullback–pushforward adjunction compare the adjoints `F ⟶ g_* N`; maps out of the
   quasi-coherent `F` on the affine `U` are determined on global sections (`hom_ext_of_app_top`), where both
   give `m ↦ g^*m`.
5. Hence `Ψ` is an isomorphism, `Ψ.app ⊤` is bijective, and `Φ = Ψ.app ⊤ ∘ η` with `η` bijective
   (`unitEl_bijective`). -/
theorem AlgebraicGeometry.Scheme.Modules.pullbackSectionsTensorMap_bijective
    {V U : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsAffine V] [AlgebraicGeometry.IsAffine U] (g : V ⟶ U) (F : U.Modules)
    [F.IsQuasicoherent] :
    letI : Algebra Γ(U, ⊤) Γ(V, ⊤) := g.appTop.hom.toAlgebra
    Function.Bijective (AlgebraicGeometry.Scheme.Modules.pullbackSectionsTensorMap g F) := by
  let _ : Algebra Γ(U, ⊤) Γ(V, ⊤) := g.appTop.hom.toAlgebra
  -- notation: N = g^*F, W = S ⊗_R M as an S-module, Φ the canonical map
  let N : V.Modules := (AlgebraicGeometry.Scheme.Modules.pullback g).obj F
  let W : ModuleCat.{u} Γ(V, ⊤) :=
    ModuleCat.of Γ(V, ⊤) (TensorProduct Γ(U, ⊤) Γ(V, ⊤) Γ(F, ⊤))
  let Φ : TensorProduct Γ(U, ⊤) Γ(V, ⊤) Γ(F, ⊤) →ₗ[Γ(V, ⊤)] Γ(N, ⊤) :=
    AlgebraicGeometry.Scheme.Modules.pullbackSectionsTensorMap g F
  have hΦ1 : ∀ m : Γ(F, ⊤), Φ (1 ⊗ₜ m) = AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback g m := fun m => by
    change (1 : Γ(V, ⊤)) • AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback g m = _
    exact one_smul _ _
  -- Ψ : T W ⟶ N, the adjoint of Φ
  let Φ' : W ⟶ ΓS N :=
    ModuleCat.ofHom (R := Γ(V, ⊤)) (X := TensorProduct Γ(U, ⊤) Γ(V, ⊤) Γ(F, ⊤)) (Y := ΓS N)
      ((secTop N).symm.toLinearMap ∘ₗ Φ)
  let Ψ : T W ⟶ N := (adj.homEquiv W N).symm Φ'
  have hΨ : ∀ w : TensorProduct Γ(U, ⊤) Γ(V, ⊤) Γ(F, ⊤), Ψ.app ⊤ (unitEl W w) = Φ w := fun w => by
    rw [← homEquiv_apply]
    show toTop N ((adj.homEquiv W N ((adj.homEquiv W N).symm Φ')).hom w) = Φ w
    rw [Equiv.apply_symm_apply]
    rfl
  -- θ₀ : M → Γ(V, T W), m ↦ unit (1 ⊗ m), R-linear for the R-structure through g^♯
  let θ₀ : Γ(F, ⊤) →ₗ[Γ(U, ⊤)] Γ((AlgebraicGeometry.Scheme.Modules.pushforward g).obj (T W), ⊤) :=
    { toFun := fun m => unitEl W (1 ⊗ₜ m)
      map_add' := fun m m' => by
        show unitEl W (1 ⊗ₜ (m + m')) = unitEl W (1 ⊗ₜ m) + unitEl W (1 ⊗ₜ m')
        rw [TensorProduct.tmul_add, unitEl_add]
      map_smul' := fun r m => by
        show unitEl W (1 ⊗ₜ (r • m)) = (g.appTop r : Γ(V, ⊤)) • unitEl W (1 ⊗ₜ m)
        rw [← unitEl_smul]
        congr 1
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul,
          Algebra.smul_def, mul_one]
        rfl }
  obtain ⟨θ', hθ'⟩ := exists_hom_of_linear (X := U) θ₀
  let Θ : N ⟶ T W :=
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv F (T W)).symm θ'
  have hΘ : ∀ m : Γ(F, ⊤), Θ.app ⊤ (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback g m) = unitEl W (1 ⊗ₜ m) :=
    fun m => by
    have h1 : (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv F (T W) Θ =
        θ' := Equiv.apply_symm_apply _ _
    rw [Adjunction.homEquiv_unit] at h1
    have h2 : ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward g).map Θ).app ⊤ m = θ'.app ⊤ m := by rw [h1]
    have h3 : ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward g).map Θ).app ⊤ m =
        Θ.app ⊤ (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback g m) := rfl
    rw [← h3, h2, hθ']
    rfl
  -- (a) Ψ ≫ Θ = 𝟙 : both sides agree on the unit elements, by S-linearity reduce to 1 ⊗ m
  have ha : Ψ ≫ Θ = 𝟙 (T W) := by
    apply T_hom_ext
    intro w
    rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app, AlgebraicGeometry.Scheme.Modules.Hom.id_app]
    change Θ.app ⊤ (Ψ.app ⊤ (unitEl W w)) = unitEl W w
    rw [hΨ]
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, unitEl_zero]
    | tmul s m =>
      have e : (s ⊗ₜ m : TensorProduct Γ(U, ⊤) Γ(V, ⊤) Γ(F, ⊤)) = s • ((1 : Γ(V, ⊤)) ⊗ₜ m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e, LinearMap.map_smul, AlgebraicGeometry.Scheme.Modules.Hom.app_smul, hΦ1, hΘ, unitEl_smul]
    | add x y hx hy => rw [map_add, map_add, unitEl_add, hx, hy]
  -- (b) Θ ≫ Ψ = 𝟙 : by the pullback adjunction it suffices to compare F ⟶ g_* N on global sections
  have hb : Θ ≫ Ψ = 𝟙 N := by
    apply ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv F N).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
    apply hom_ext_of_app_top (X := U)
    intro m
    change Ψ.app ⊤ (Θ.app ⊤ (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback g m)) =
      AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback g m
    rw [hΘ, hΨ, hΦ1]
  have : IsIso Ψ := ⟨Θ, ha, hb⟩
  have hΨbij : Function.Bijective (Ψ.app ⊤) := ConcreteCategory.bijective_of_isIso (Ψ.app ⊤)
  have hfun : (⇑Φ : TensorProduct Γ(U, ⊤) Γ(V, ⊤) Γ(F, ⊤) → Γ(N, ⊤)) = (Ψ.app ⊤) ∘ unitEl W :=
    funext fun w => (hΨ w).symm
  show Function.Bijective Φ
  rw [hfun]
  exact hΨbij.comp (unitEl_bijective W)

/-- Stacks 01I9: for `V`, `U` affine and `F` quasi-coherent, the canonical map above is bijective;
the isomorphism `Γ(V, g^*F) ≃ₗ Γ(V) ⊗_{Γ(U)} Γ(U, F)` is its inverse. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.pullbackSectionsIsoTensor {V U : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsAffine V] [AlgebraicGeometry.IsAffine U] (g : V ⟶ U) (F : U.Modules) [F.IsQuasicoherent] :
    letI : Algebra Γ(U, ⊤) Γ(V, ⊤) := g.appTop.hom.toAlgebra
    Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj F, ⊤) ≃ₗ[Γ(V, ⊤)]
      TensorProduct Γ(U, ⊤) Γ(V, ⊤) Γ(F, ⊤) :=
  letI : Algebra Γ(U, ⊤) Γ(V, ⊤) := g.appTop.hom.toAlgebra
  (LinearEquiv.ofBijective (AlgebraicGeometry.Scheme.Modules.pullbackSectionsTensorMap g F)
    (AlgebraicGeometry.Scheme.Modules.pullbackSectionsTensorMap_bijective g F)).symm

/- The version for affine opens `W ⊆ f⁻¹U` (with the canonical map) is
   `isIso_transpose_pullbackSectionsNative` in `PullbackSectionsNativeBaseChange.lean`. -/

end
