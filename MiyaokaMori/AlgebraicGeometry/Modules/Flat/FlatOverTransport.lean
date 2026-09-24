import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.PullbackStalkOpenImmersion
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt

/-! # Transporting relative flatness

Three transport statements for flatness.

* Algebra: if `e : S ≃+* S'` is a ring isomorphism and `u : M ≃+ M'` is an additive
  isomorphism with `u (a • m) = e a • u m`, then `M` flat over `S` implies `M'` flat over `S'`.
  Proof: view `M'` as an `S`-module through `e`; then `u` is `S`-linear, so `M'` is flat over `S`
  (`Module.Flat.of_linearEquiv`), hence `S' ⊗[S] M'` is flat over `S'`, and
  `S' ⊗[S] M' ≃ₗ[S'] M'` via `t ⊗ m ↦ t • m`.
* Geometry: `FlatOver` (relative flatness, defined stalkwise) is transported along an
  isomorphism `ι : T ⟶ T'` of the base: `FlatOver g N → FlatOver (g ≫ ι) N`, using
  `Scheme.Hom.stalkMap_comp` and the previous item with `e` the inverse of `ι.stalkMap`.
* Geometry: `FlatOver` restricts to an open `V ⊆ T` of the base: `FlatOver f M` implies
  `FlatOver (f ∣_ V) ((f⁻¹V).ι^* M)`. Here `morphismRestrictStalkMap` gives the commutative
  square relating the stalk maps of `f` and `f ∣_ V`, `Scheme.Opens.stalkIso_inv` identifies the
  inverse of one side with the stalk map of the open immersion `j = (f⁻¹V).ι`, and the stalks
  of `j^* M` and `M` are identified by `modulePullbackStalkEquivOfIsIso`.

References: Stacks 00HD, Stacks 01XZ (flatness is local).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open CategoryTheory
open scoped AlgebraicGeometry TensorProduct

namespace MiyaokaMori.FlatOverTransport

universe u

/-- Flatness is transported along a ring isomorphism and a compatible additive isomorphism. -/
theorem flat_of_ringEquiv {S S' M M' : Type u} [CommRing S] [CommRing S']
    [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S' M']
    (e : S ≃+* S') (u : M ≃+ M') (hu : ∀ (a : S) (m : M), u (a • m) = e a • u m)
    (hflat : Module.Flat S M) : Module.Flat S' M' := by
  letI : Algebra S S' := (e : S →+* S').toAlgebra
  letI : Module S M' := Module.compHom M' (e : S →+* S')
  have hsmulS : ∀ (a : S) (m : M'), a • m = e a • m := fun _ _ ↦ rfl
  haveI : IsScalarTower S S' M' := ⟨fun a b m ↦ by
    show (e a * b) • m = e a • b • m
    rw [mul_smul]⟩
  haveI : SMulCommClass S S' M' := ⟨fun a b m ↦ by
    show e a • b • m = b • e a • m
    rw [smul_comm]⟩
  haveI : Module.Flat S M := hflat
  -- `M'` as an `S`-module is linearly isomorphic to `M`, hence flat over `S`
  haveI : Module.Flat S M' := by
    let uS : M ≃ₗ[S] M' :=
      { u with map_smul' := fun a m ↦ hu a m }
    exact Module.Flat.of_linearEquiv uS.symm
  -- after extending scalars it is flat over `S'`
  haveI : Module.Flat S' (S' ⊗[S] M') := inferInstance
  -- S' ⊗_S M' ≅ M'
  have hone : ∀ (t : S') (m : M'), (1 : S') ⊗ₜ[S] (t • m) = t ⊗ₜ[S] m := by
    intro t m
    have ht : t = e (e.symm t) := (e.apply_symm_apply t).symm
    rw [ht, ← hsmulS (e.symm t) m, ← TensorProduct.smul_tmul]
    congr 1
    show e (e.symm t) • (1 : S') = e (e.symm t)
    rw [smul_eq_mul, mul_one]
  let ψ : S' ⊗[S] M' →ₗ[S'] M' :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun t ↦ t • (LinearMap.id : M' →ₗ[S] M')
        map_add' := fun s t ↦ by ext m; simp [add_smul]
        map_smul' := fun s t ↦ by ext m; simp [mul_smul] }
  have hψ : ∀ (t : S') (m : M'), ψ (t ⊗ₜ[S] m) = t • m := fun _ _ ↦ rfl
  let ψinv : M' →ₗ[S'] S' ⊗[S] M' :=
    { toFun := fun m ↦ (1 : S') ⊗ₜ[S] m
      map_add' := fun m n ↦ TensorProduct.tmul_add _ m n
      map_smul' := fun t m ↦ by
        show (1 : S') ⊗ₜ[S] (t • m) = t • ((1 : S') ⊗ₜ[S] m)
        rw [hone, TensorProduct.smul_tmul', smul_eq_mul, mul_one] }
  let E : S' ⊗[S] M' ≃ₗ[S'] M' :=
    { ψ with
      invFun := ψinv
      left_inv := fun z ↦ by
        show ψinv (ψ z) = z
        induction z using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | tmul t m => show (1 : S') ⊗ₜ[S] (t • m) = t ⊗ₜ[S] m; exact hone t m
        | add z w hz hw => rw [map_add, map_add, hz, hw]
      right_inv := by
        intro m
        show ψ ((1 : S') ⊗ₜ[S] m) = m
        rw [hψ, one_smul] }
  exact Module.Flat.of_linearEquiv E.symm

/-- Relative flatness is transported along an isomorphism of the base scheme. -/
theorem isFlatOver_comp_iso {Y T T' : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ T) (ι : T ⟶ T')
    [IsIso ι] (N : Y.Modules)
    (h : AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.FlatOver g N) :
    AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.FlatOver (g ≫ ι) N := by
  intro y
  letI instT : Module (T.presheaf.stalk (g.base y)) (N.presheaf.stalk y) :=
    AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.relativeStalkModule g N y
  letI instT' : Module (T'.presheaf.stalk ((g ≫ ι).base y)) (N.presheaf.stalk y) :=
    AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.relativeStalkModule (g ≫ ι) N y
  have hstalk : Function.Bijective (ι.stalkMap (g.base y)).hom :=
    ConcreteCategory.bijective_of_isIso (ι.stalkMap (g.base y))
  let ε : T'.presheaf.stalk (ι.base (g.base y)) ≃+* T.presheaf.stalk (g.base y) :=
    RingEquiv.ofBijective (ι.stalkMap (g.base y)).hom hstalk
  refine flat_of_ringEquiv ε.symm (AddEquiv.refl (N.presheaf.stalk y)) ?_ (h y)
  intro a m
  show (g.stalkMap y).hom a • m = ((g ≫ ι).stalkMap y).hom (ε.symm a) • m
  congr 1
  rw [AlgebraicGeometry.Scheme.Hom.stalkMap_comp]
  show (g.stalkMap y).hom a = (g.stalkMap y).hom ((ι.stalkMap (g.base y)).hom (ε.symm a))
  congr 1
  exact (ε.apply_symm_apply a).symm

/-- Relative flatness restricts to an open subset of the base: if `M` is flat over `T`
(along `f`), then the pullback of `M` along the open immersion `f⁻¹V ⟶ Y` is flat over `V`
(along `f ∣_ V`). -/
theorem isFlatOver_morphismRestrict {Y T : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ T)
    (M : Y.Modules) (hM : AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.FlatOver f M) (V : T.Opens) :
    AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.FlatOver (f ∣_ V)
      ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj M) := by
  intro y
  letI instS : Module (T.presheaf.stalk (f.base ((f ⁻¹ᵁ V).ι.base y)))
      (M.presheaf.stalk ((f ⁻¹ᵁ V).ι.base y)) :=
    AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.relativeStalkModule f M ((f ⁻¹ᵁ V).ι.base y)
  letI instS' : Module (V.toScheme.presheaf.stalk ((f ∣_ V).base y))
      (((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj M).presheaf.stalk y) :=
    AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.relativeStalkModule (f ∣_ V)
      ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj M) y
  let hiso := AlgebraicGeometry.morphismRestrictStalkMap f V y
  have hw : hiso.hom.left ≫ f.stalkMap ((f ⁻¹ᵁ V).ι.base y) =
      (f ∣_ V).stalkMap y ≫ hiso.hom.right := hiso.hom.w
  haveI hLiso : IsIso hiso.hom.left :=
    ⟨hiso.inv.left, congrArg CommaMorphism.left hiso.hom_inv_id,
      congrArg CommaMorphism.left hiso.inv_hom_id⟩
  have hR : hiso.hom.right ≫ (f ⁻¹ᵁ V).ι.stalkMap y = 𝟙 _ := by
    have hinv : ((f ⁻¹ᵁ V).stalkIso y).inv = (f ⁻¹ᵁ V).ι.stalkMap y :=
      AlgebraicGeometry.Scheme.Opens.stalkIso_inv _ _
    have hid := ((f ⁻¹ᵁ V).stalkIso y).hom_inv_id
    rw [hinv] at hid
    exact hid
  have hbij : Function.Bijective (hiso.hom.left).hom :=
    ConcreteCategory.bijective_of_isIso hiso.hom.left
  let ε : V.toScheme.presheaf.stalk ((f ∣_ V).base y) ≃+*
      T.presheaf.stalk (f.base ((f ⁻¹ᵁ V).ι.base y)) :=
    RingEquiv.ofBijective (hiso.hom.left).hom hbij
  -- key identity: the two paths give the same scalar in `O_{f⁻¹V,y}`
  have hkeyMor : hiso.hom.left ≫
      (f.stalkMap ((f ⁻¹ᵁ V).ι y) ≫ (f ⁻¹ᵁ V).ι.stalkMap y) = (f ∣_ V).stalkMap y :=
    calc hiso.hom.left ≫ (f.stalkMap ((f ⁻¹ᵁ V).ι y) ≫ (f ⁻¹ᵁ V).ι.stalkMap y)
        = (hiso.hom.left ≫ f.stalkMap ((f ⁻¹ᵁ V).ι y)) ≫ (f ⁻¹ᵁ V).ι.stalkMap y :=
          (Category.assoc _ _ _).symm
      _ = ((f ∣_ V).stalkMap y ≫ hiso.hom.right) ≫ (f ⁻¹ᵁ V).ι.stalkMap y :=
          congrArg (fun φ ↦ φ ≫ (f ⁻¹ᵁ V).ι.stalkMap y) hw
      _ = (f ∣_ V).stalkMap y ≫ (hiso.hom.right ≫ (f ⁻¹ᵁ V).ι.stalkMap y) :=
          Category.assoc _ _ _
      _ = (f ∣_ V).stalkMap y ≫ 𝟙 _ :=
          congrArg (fun φ ↦ (f ∣_ V).stalkMap y ≫ φ) hR
      _ = (f ∣_ V).stalkMap y := Category.comp_id _
  have hkey : ∀ a, ((f ⁻¹ᵁ V).ι.stalkMap y) ((f.stalkMap ((f ⁻¹ᵁ V).ι y)) a) =
      ((f ∣_ V).stalkMap y) (ε.symm a) := by
    intro a
    have hc := congrArg (fun φ ↦ φ (ε.symm a)) hkeyMor
    simp only [CommRingCat.comp_apply] at hc
    have h2 : (hiso.hom.left) (ε.symm a) = a := ε.apply_symm_apply a
    rw [h2] at hc
    exact hc
  refine flat_of_ringEquiv ε.symm
    (MiyaokaMori.PullbackStalkOpenImmersion.modulePullbackStalkEquivOfIsIso
      (f ⁻¹ᵁ V).ι M y) ?_ (hM ((f ⁻¹ᵁ V).ι y))
  intro a m
  show AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom (f ⁻¹ᵁ V).ι M y
      ((f.stalkMap ((f ⁻¹ᵁ V).ι y)) a • m) =
    ((f ∣_ V).stalkMap y) (ε.symm a) •
      AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom (f ⁻¹ᵁ V).ι M y m
  rw [AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom_smul, hkey a]

end MiyaokaMori.FlatOverTransport

end
