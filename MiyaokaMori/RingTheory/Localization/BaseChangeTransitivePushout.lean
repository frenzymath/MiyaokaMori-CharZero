import MiyaokaMori.Prelude
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.IsTensorProduct

/-! # Transitivity of base change along a pushout square

On a pushout square of rings `B' = A' ⊗_A B`, the base change of a `B`-module `N` to a `B'`-module `N'`
(`B' ⊗_B N ≅ N'`), regarded as a map from an `A`-module to an `A'`-module, is still a base change
(`A' ⊗_A N ≅ N'`). Proof: `A' ⊗_A N ≅ (A' ⊗_A B) ⊗_B N ≅ B' ⊗_B N ≅ N'` (see the docstring of the
declaration).

Reference: Stacks 05G5; the step "`(A' ⊗_A B) ⊗_B N = A' ⊗_A N`" in the proof of Hartshorne III.9.3.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- **Transitivity of base change along a pushout square** (pure commutative algebra, at the level of
variables). Given a commutative square of rings `φ : A → A'`, `β : A → B`, `β' : A' → B'`, `γ : B → B'` which
is a pushout (`B' = A' ⊗_A B`), `N` a `B`-module, `N'` a `B'`-module, and `ψ_B : N → N'` `γ`-semilinear and a
base change (`B' ⊗_B N ≅ N'`), the same map `ψ_A`, with `N`, `N'` regarded as an `A`- and an `A'`-module, is
a base change along `φ` (`A' ⊗_A N ≅ N'`). To avoid depending on "two spellings of the same module", `N_A`,
`N'_A` are arbitrary `A`-, `A'`-modules identified with `N`, `N'` through additive isomorphisms `eN`, `eN'`,
with scalar actions compatible through `β`, `β'` (in the applications `eN = eN' = AddEquiv.refl`).

Proof (as in the Lean proof): `A' ⊗_A N_A ≅ A' ⊗_A N ≅ B' ⊗_B N ≅ N' ≅ N'_A`, the steps being `eN` (an
`A`-linear isomorphism by `heN`, `TensorProduct.congr`), the cancellation isomorphism given by the pushout
square (`hpo` is turned into `Algebra.IsPushout A A' B B'` by `CommRingCat.isPushout_iff_isPushout`; Mathlib
`Algebra.IsPushout.cancelBaseChange : B' ⊗_B N ≃ₗ[A'] A' ⊗_A N`, whose inverse is `s ⊗ x ↦ β'(s) ⊗ x` on pure
tensors), `hB` (the transpose `t ⊗ x ↦ t • ψ_B x` of `ψ_B` is bijective,
`ConcreteCategory.isIso_iff_bijective`), `eN'.symm`. The composite on pure tensors is
`s ⊗ x ↦ eN'⁻¹(β'(s) • ψ_B(eN x)) = s • ψ_A x` (by `hψ`, `heN'`), which is exactly the transpose of `ψ_A`
(formula `Adjunction.homEquiv_symm_apply` + `fromExtendScalars`: `s ⊗ x ↦ s • ψ x`); both are additive, so they
agree by `TensorProduct.induction_on`; a composite of bijections is bijective, and
`ConcreteCategory.isIso_iff_bijective` concludes.
Technical point: the carrier of `ModuleCat.extendScalars` uses `Module.compHom` for its `A`-module structure,
whereas `RingHom.toAlgebra` gives `Algebra.toModule`; the two are definitionally equal only at default
transparency, so both transposes are first moved to the ordinary tensor product via
`let TAl : (A' ⊗[A] N_A) →ₗ[A'] N'_A := TA.hom`.
Reference: Stacks 05G5 (associativity of tensor products and transitivity of base change).

Edge cases: `A' = 0 ⇒ B' = 0 ⇒ N' = 0`, both sides zero; `N = 0 ⇒ N' = 0`. -/
theorem isIso_transpose_of_isPushout {A A' B B' : CommRingCat.{u}} (φ : A ⟶ A') (β : A ⟶ B)
    (β' : A' ⟶ B') (γ : B ⟶ B') (hpo : IsPushout φ β β' γ)
    {N_A : ModuleCat.{u} A} {N'_A : ModuleCat.{u} A'} {N : ModuleCat.{u} B} {N' : ModuleCat.{u} B'}
    (eN : N_A ≃+ N) (heN : ∀ (r : A) (x : N_A), eN (r • x) = β.hom r • eN x)
    (eN' : N'_A ≃+ N') (heN' : ∀ (r : A') (x : N'_A), eN' (r • x) = β'.hom r • eN' x)
    (ψA : N_A ⟶ (ModuleCat.restrictScalars φ.hom).obj N'_A)
    (ψB : N ⟶ (ModuleCat.restrictScalars γ.hom).obj N')
    (hψ : ∀ x : N_A, eN' (ψA.hom x) = ψB.hom (eN x))
    (hB : IsIso (((ModuleCat.extendRestrictScalarsAdj γ.hom).homEquiv _ _).symm ψB)) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).symm ψA) := by
  -- Algebra structures on the pushout square.
  let : Algebra A A' := φ.hom.toAlgebra
  let : Algebra A B := β.hom.toAlgebra
  let : Algebra A' B' := β'.hom.toAlgebra
  let : Algebra B B' := γ.hom.toAlgebra
  let : Algebra A B' := (φ ≫ β').hom.toAlgebra
  have : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq fun x => rfl
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq fun x => by
    change (φ ≫ β').hom x = (β ≫ γ).hom x
    rw [hpo.w]
  have hApo : Algebra.IsPushout A A' B B' := CommRingCat.isPushout_iff_isPushout.mp hpo
  -- Module structures on N over A (through β).
  let : Module A N := Module.compHom N β.hom
  have : IsScalarTower A B N := ⟨fun a b x => by
    change (β.hom a * b) • x = β.hom a • b • x
    rw [mul_smul]⟩
  -- The cancellation isomorphism  B' ⊗[B] N ≃ A' ⊗[A] N.
  let c : (B' ⊗[B] N) ≃ₗ[A'] (A' ⊗[A] N) := Algebra.IsPushout.cancelBaseChange A A' B B' N
  -- eN as an A-linear equivalence.
  let eNl : N_A ≃ₗ[A] N :=
    { eN with
      map_smul' := fun r x => by
        change eN (r • x) = β.hom r • eN x
        exact heN r x }
  -- the transposes as functions
  set TA := ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).symm ψA with hTA
  set TB := ((ModuleCat.extendRestrictScalarsAdj γ.hom).homEquiv _ _).symm ψB with hTB
  have hTAt : ∀ (s : A') (x : N_A), TA (s ⊗ₜ[A] x) = s • ψA.hom x := fun s x => by
    rw [hTA, Adjunction.homEquiv_symm_apply]; rfl
  have hTBt : ∀ (t : B') (x : N), TB (t ⊗ₜ[B] x) = t • ψB.hom x := fun t x => by
    rw [hTB, Adjunction.homEquiv_symm_apply]; rfl
  have hTBbij : Function.Bijective TB := (ConcreteCategory.isIso_iff_bijective _).mp hB
  rw [ConcreteCategory.isIso_iff_bijective]
  -- View the two transposes as linear maps on the plain tensor products
  -- (the module structures `Module.compHom` and `RingHom.toAlgebra` are definitionally equal).
  let TAl : (A' ⊗[A] N_A) →ₗ[A'] N'_A := TA.hom
  let TBl : (B' ⊗[B] N) →ₗ[B'] N' := TB.hom
  have hTAlt : ∀ (s : A') (x : N_A), TAl (s ⊗ₜ[A] x) = s • ψA.hom x := hTAt
  have hTBlt : ∀ (t : B') (x : N), TBl (t ⊗ₜ[B] x) = t • ψB.hom x := hTBt
  have hTBlbij : Function.Bijective TBl := hTBbij
  -- TAl agrees with the composite eN'.symm ∘ TBl ∘ c.symm ∘ (id ⊗ eN).
  let g : A' ⊗[A] N_A → N'_A := fun z =>
    eN'.symm (TBl (c.symm (TensorProduct.congr (LinearEquiv.refl A A') eNl z)))
  have key : ∀ z : A' ⊗[A] N_A, TAl z = g z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [g]
    | tmul s x =>
      rw [hTAlt]
      simp only [g, c, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
        Algebra.IsPushout.cancelBaseChange_symm_tmul, hTBlt]
      change s • ψA.hom x = eN'.symm (β'.hom s • ψB.hom (eN x))
      rw [← hψ]
      exact ((eN'.symm_apply_apply (s • ψA.hom x)).symm.trans
        (congrArg eN'.symm (heN' s (ψA.hom x))))
    | add x y hx hy => simp only [g, map_add, hx, hy]
  have hg : Function.Bijective g :=
    eN'.symm.bijective.comp (hTBlbij.comp (c.symm.bijective.comp
      (TensorProduct.congr (LinearEquiv.refl A A') eNl).bijective))
  have hTAl : Function.Bijective TAl := by
    have : ⇑TAl = g := funext key
    rw [this]; exact hg
  exact hTAl

end AlgebraicGeometry.Scheme.Modules

end
