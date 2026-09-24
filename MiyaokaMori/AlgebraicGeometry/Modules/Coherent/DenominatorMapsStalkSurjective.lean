import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.DenominatorMapsOnTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineGenericCoordinates

/-! # Stalkwise surjectivity of the denominator maps

Stalkwise surjectivity of the two denominator maps of Stacks 02P2 off the bad set (step 5 of the 0BEM
denominator trick).

With `a : I ⟶ O_X`, `b : I ⟶ L`, `F` arbitrary, and the maps
`Φ = denomMulMap a F : I ⊗ F ⟶ F` (`h ⊗ t ↦ a(h)•t`) and `Ψ = denomSectionMap b F : I ⊗ F ⟶ F ⊗ L`
(`h ⊗ t ↦ t ⊗ b(h)`):

* `stalkMap_denomMulMap_surjective_of_surjective`: if `a_x : I_x → O_{X,x}` is surjective then so is
  `Φ_x`. Proof: pick `h ∈ I_x` with `a_x h = 1` (the germ of the global section `1`, transported through
  `unitStalkLinearEquiv : (O_X)_x ≃ O_{X,x}`, `unitStalkLinearEquiv_germ`); write `h`, `t` as germs of
  sections `h'`, `t'` on a common open `W`; then `Φ_x(germ(h' ⊗ t')) = a(h')_x • t'_x = 1 • t = t`
  (`stalkMap_denomMulMap_germ`).
* `stalkMap_denomSectionMap_surjective_of_surjective`: if `b_x : I_x → L_x` is surjective then so is `Ψ_x`.
  Proof: through `ε : (F ⊗ L)_x ≃ F_x ⊗ L_x` (`tensorStalkLinearEquiv`, Stacks 01CB) the target is generated
  by pure tensors `t ⊗ l`; write `l = b_x h`, `h = h'_x`, `t = t'_x` on a common open `W`; then
  `ε(Ψ_x(germ(h' ⊗ t'))) = t'_x ⊗ b_x(h'_x) = t ⊗ l` (`tensorStalkLinearEquiv_stalkMap_denomSectionMap_germ`);
  the range of a linear map is a submodule, so `TensorProduct.induction_on` finishes.

In the application (`Stacks0bemDenominator`), `a_x` and `b_x` are surjective at `x ∉ T` because the cokernels
of `a` and `b` are supported in `T` (Stacks 02P0, `exists_denominatorIdeal`, via `notMem_support_cokernel_iff`).

Source: Stacks 02P2 (proof), 02P0.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Naturality of `Hom.app` for a map into `O_X`, in germ form in `O_{X,x}`:
`(a.app W (s|_W))_x = (a.app U s)_x`. -/
theorem germ_app_res_unit {M : X.Modules} (a : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    {U W : X.Opens} (hWU : W ≤ U) (x : X) (hxW : x ∈ W) (s : Γ(M, U)) :
    X.presheaf.germ W x hxW
        (show Γ(X, W) from a.app W (M.presheaf.map (CategoryTheory.homOfLE hWU).op s)) =
      X.presheaf.germ U x (hWU hxW) (show Γ(X, U) from a.app U s) := by
  have hnat : (show Γ(X, W) from a.app W (M.presheaf.map (CategoryTheory.homOfLE hWU).op s)) =
      X.presheaf.map (CategoryTheory.homOfLE hWU).op (show Γ(X, U) from a.app U s) :=
    _root_.PresheafOfModules.naturality_apply a.val (CategoryTheory.homOfLE hWU).op s
  rw [hnat]
  exact X.presheaf.germ_res_apply (CategoryTheory.homOfLE hWU) x hxW _

/-- **`Φ_x` is surjective when `a_x` is** (see the module docstring). -/
theorem stalkMap_denomMulMap_surjective_of_surjective {I : X.Modules}
    (a : I ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (F : X.Modules) (x : X)
    (ha : Function.Surjective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x a)) :
    Function.Surjective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (denomMulMap a F)) := by
  intro t
  -- a germ `h ∈ I_x` with `a_x h = 1`
  obtain ⟨h, hh⟩ := ha ((AlgebraicGeometry.Scheme.Modules.presheaf
    (SheafOfModules.unit X.ringCatSheaf)).germ ⊤ x trivial (1 : Γ(X, ⊤)))
  obtain ⟨V, hxV, h', rfl⟩ := I.presheaf.exists_germ_eq h
  obtain ⟨W, hxW, t', rfl⟩ := F.presheaf.exists_germ_eq t
  have hone : X.presheaf.germ V x hxV (show Γ(X, V) from a.app V h') = 1 := by
    have hh' : (AlgebraicGeometry.Scheme.Modules.presheaf
          (SheafOfModules.unit X.ringCatSheaf)).germ ⊤ x trivial (1 : Γ(X, ⊤)) =
        (AlgebraicGeometry.Scheme.Modules.presheaf
          (SheafOfModules.unit X.ringCatSheaf)).germ V x hxV (show Γ(X, V) from a.app V h') :=
      hh.symm.trans (AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ X x a V hxV h')
    have h1 : X.presheaf.germ ⊤ x trivial (1 : Γ(X, ⊤)) =
        X.presheaf.germ V x hxV (show Γ(X, V) from a.app V h') :=
      (AlgebraicGeometry.Divisors.LineGenericCoordinates.unitStalkLinearEquiv_germ X x ⊤ trivial 1).symm.trans
        ((congrArg (AlgebraicGeometry.Divisors.LineGenericCoordinates.unitStalkLinearEquiv X x) hh').trans
          (AlgebraicGeometry.Divisors.LineGenericCoordinates.unitStalkLinearEquiv_germ X x V hxV _))
    rw [← h1]
    exact map_one (X.presheaf.germ ⊤ x trivial).hom
  let W' : X.Opens := V ⊓ W
  have hxW' : x ∈ W' := ⟨hxV, hxW⟩
  have hV : W' ≤ V := inf_le_left
  have hW : W' ≤ W := inf_le_right
  refine ⟨(AlgebraicGeometry.Scheme.Modules.tensor I F).presheaf.germ W' x hxW'
    (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (I.presheaf.map (CategoryTheory.homOfLE hV).op h')
      (F.presheaf.map (CategoryTheory.homOfLE hW).op t')), ?_⟩
  rw [stalkMap_denomMulMap_germ, F.presheaf.germ_res_apply (CategoryTheory.homOfLE hW) x hxW' t']
  have h2 : X.presheaf.germ W' x hxW'
      (show Γ(X, W') from a.app W' (I.presheaf.map (CategoryTheory.homOfLE hV).op h')) =
      X.presheaf.germ V x hxV (show Γ(X, V) from a.app V h') :=
    germ_app_res_unit a hV x hxW' h'
  rw [h2, hone, one_smul]

/-- **`Ψ_x` is surjective when `b_x` is** (see the module docstring). -/
theorem stalkMap_denomSectionMap_surjective_of_surjective {I L : X.Modules} (b : I ⟶ L)
    (F : X.Modules) (x : X) (hb : Function.Surjective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x b)) :
    Function.Surjective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (denomSectionMap b F)) := by
  let ε := AlgebraicGeometry.Scheme.Modules.tensorStalkLinearEquiv F L x
  let Ψ := AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (denomSectionMap b F)
  -- every pure tensor `t ⊗ l` is in the range of `ε ∘ Ψ`
  have hrange : ∀ w : F.presheaf.stalk x ⊗[X.presheaf.stalk x] L.presheaf.stalk x,
      w ∈ LinearMap.range ((ε : _ →ₗ[X.presheaf.stalk x] _) ∘ₗ Ψ) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul t l =>
      obtain ⟨h, rfl⟩ := hb l
      obtain ⟨W, hxW, h', t', rfl, rfl⟩ :=
        AlgebraicGeometry.Scheme.Modules.exists_germ_pair I F x h t
      refine ⟨(AlgebraicGeometry.Scheme.Modules.tensor I F).presheaf.germ W x hxW
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection h' t'), ?_⟩
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ε, Ψ]
      exact tensorStalkLinearEquiv_stalkMap_denomSectionMap_germ b F x W hxW h' t'
    | add w₁ w₂ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  intro w
  obtain ⟨z, hz⟩ := hrange (ε w)
  refine ⟨z, ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hz
  exact ε.injective hz

end AlgebraicGeometry.Scheme.Modules

end
