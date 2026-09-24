import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjBaseChangeUnit
import MiyaokaMori.AlgebraicGeometry.Morphisms.IsBaseChangeDirectSum
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.OfGradedQCAlgebra

/-! # The algebra behind the base change of a relative Proj

**The algebra behind Stacks 01N2 for the base change of a relative Proj** (`RelativeProjBaseChangeLocal.lean`).

For `S : X.GradedQCAlgebra` and an open `U`, the section ring `S.sectionsRing U = ⊕_m Γ(U, S_m)` is a
`Γ(X,U)`-module componentwise (`sectionsPieceModuleBC`, `sectionsModuleBC`); scalar multiplication is
multiplication by the structure map (`smul_eq_sectionsUnitHom_mul`), so this module structure comes
from a `Γ(X,U)`-algebra structure `sectionsAlgebraBC` (`Algebra.ofModule`) whose `algebraMap` is
`sectionsUnitHom` (`algebraMap_eq_sectionsUnitHom`). The grading becomes `Submodule`-valued
(`sectionsSubmodule`, a `GradedAlgebra`), as needed by `Proj.isPullback_of_isBaseChange` (01N2).

For `g : S' ⟶ S`, `𝒜 : S.GradedQCAlgebra`, opens `U ⊆ S`, `V ⊆ S'` with `V ≤ g⁻¹U`, write
`R = Γ(S,U)`, `R' = Γ(S',V)`, `φ = g^♯ : R → R'`, `A = 𝒜(U)`, `B = (g^*𝒜)(V)`. `B` is an `R`-module through
`φ` (`Module.compHom`, componentwise: `baseChangePieceModule`, `baseChangeModule`) and an `R`-algebra
(`baseChangeAlgebra`), the unit `A → B` (`baseChangeUnitRingHom`, `RelativeProjBaseChangeUnit.lean`)
is an `R`-algebra hom (`baseChangeUnitAlgHom`), and — for affine `U`, `V` — it is a **base change**:
`R' ⊗_R A ≅ B` (`isBaseChange_baseChangeUnit`). Proof: piecewise it is Stacks 01I9
(`Modules.isIso_transpose_pullbackSectionsNative`,
turned into `IsBaseChange` by `IsBaseChange.of_isIso_extendRestrictScalars_transpose`), and a direct
sum of base changes is a base change (Mathlib `IsBaseChange.directSum`).

All instances are `def`s used through `letI` (no global instances; they depend on `g`, `hV`).

Source: Stacks 01N2, 01I9, 01O3; the base change of `P(O ⊕ L)` in Corollary 4.3 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry DirectSum

noncomputable section

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

/-! ## The `Γ(X,U)`-algebra structure on the section ring -/

section SectionsAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (U : X.Opens)

/-- `Γ(X,U)`-module structure on the pieces `Γ(U, S_m)` (Mathlib's instance, respelled for
`S.sectionsPiece U m`; cf. the local instance in `OfGradedQCAlgebra.lean`). -/
@[instance_reducible] def sectionsPieceModuleBC (m : ℕ) : Module Γ(X, U) (S.sectionsPiece U m) :=
  inferInstanceAs (Module Γ(X, U) Γ(S.part m, U))

attribute [local instance] sectionsPieceModuleBC

/-- The componentwise `Γ(X,U)`-module structure on `⊕_m Γ(U, S_m)`. -/
@[instance_reducible] def sectionsModuleBC : Module Γ(X, U) (S.sectionsRing U) :=
  inferInstanceAs (Module Γ(X, U) (⨁ m, S.sectionsPiece U m))

attribute [local instance] sectionsModuleBC

/-- Scalar multiplication is multiplication by the structure map (`sectionsUnitHom_mul_ofPiece`,
extended from the pieces by additivity). -/
theorem smul_eq_sectionsUnitHom_mul (r : Γ(X, U)) (x : S.sectionsRing U) :
    r • x = S.sectionsUnitHom U r * x := by
  let cast : (⨁ m, S.sectionsPiece U m) → S.sectionsRing U := fun y => y
  refine DirectSum.induction_on (motive := fun y : ⨁ m, S.sectionsPiece U m =>
    r • cast y = S.sectionsUnitHom U r * cast y) x ?_ ?_ ?_
  · show r • (0 : S.sectionsRing U) = S.sectionsUnitHom U r * 0
    rw [smul_zero, mul_zero]
  · intro m a
    have e : r • cast (DirectSum.of (S.sectionsPiece U) m a) =
        cast (DirectSum.of (S.sectionsPiece U) m (r • a)) :=
      (DirectSum.of_smul (R := Γ(X, U)) (ι := ℕ) (M := S.sectionsPiece U) m r a).symm
    rw [e]
    exact (S.sectionsUnitHom_mul_ofPiece U r a).symm
  · intro y z hy hz
    show r • (cast y + cast z) = S.sectionsUnitHom U r * (cast y + cast z)
    rw [smul_add, mul_add, hy, hz]

/-- The `Γ(X,U)`-algebra structure on the section ring whose module structure is the componentwise
one (`Algebra.ofModule`). -/
@[instance_reducible] def sectionsAlgebraBC : Algebra Γ(X, U) (S.sectionsRing U) :=
  Algebra.ofModule
    (fun r x y => by
      rw [smul_eq_sectionsUnitHom_mul, smul_eq_sectionsUnitHom_mul, _root_.mul_assoc])
    (fun r x y => by
      rw [smul_eq_sectionsUnitHom_mul, smul_eq_sectionsUnitHom_mul, _root_.mul_left_comm])

attribute [local instance] sectionsAlgebraBC

theorem algebraMap_eq_sectionsUnitHom (r : Γ(X, U)) :
    algebraMap Γ(X, U) (S.sectionsRing U) r = S.sectionsUnitHom U r := by
  show r • (1 : S.sectionsRing U) = _
  have e : r • (1 : S.sectionsRing U) = S.sectionsUnitHom U r * 1 :=
    S.smul_eq_sectionsUnitHom_mul U r 1
  rw [e, mul_one]

/-- The grading of the section ring as `Γ(X,U)`-submodules (the structure map lands in degree 0). -/
def sectionsSubmodule (m : ℕ) : Submodule Γ(X, U) (S.sectionsRing U) where
  carrier := S.sectionsGrading U m
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c x hx := by
    show c • x ∈ S.sectionsGrading U m
    have e : c • x = S.sectionsUnitHom U c * x := S.smul_eq_sectionsUnitHom_mul U c x
    rw [e]
    have h := SetLike.mul_mem_graded (A := S.sectionsGrading U) (S.sectionsUnit U c).2 hx
    rw [zero_add] at h
    exact h

@[simp] theorem mem_sectionsSubmodule {m : ℕ} {x : S.sectionsRing U} :
    x ∈ S.sectionsSubmodule U m ↔ x ∈ S.sectionsGrading U m := Iff.rfl

/-- The `Submodule`-valued grading is a graded algebra (same decomposition data). -/
@[instance_reducible] def gradedAlgebraSectionsSubmodule : GradedAlgebra (S.sectionsSubmodule U) where
  one_mem := S.sectionsGrading_one_mem U
  mul_mem := S.sectionsGrading_mul_mem U
  decompose' := DirectSum.decompose (S.sectionsGrading U)
  left_inv _ := (DirectSum.decompose (S.sectionsGrading U)).left_inv _
  right_inv _ := (DirectSum.decompose (S.sectionsGrading U)).right_inv _

end SectionsAlgebra

/-! ## The base change situation -/

section BaseChange

variable {S S' : AlgebraicGeometry.Scheme.{u}} (g : S' ⟶ S) (𝒜 : S.GradedQCAlgebra)
  (U : S.Opens) (V : S'.Opens) (hV : V ≤ g ⁻¹ᵁ U)

/-- `Γ(S',V)` as a `Γ(S,U)`-algebra via `g^♯ = g.appLE U V hV`. -/
@[instance_reducible] def baseAlgebra : Algebra Γ(S, U) Γ(S', V) := (g.appLE U V hV).hom.toAlgebra

/-- `Γ(V, g^*𝒜_m)` as a `Γ(S,U)`-module via `g^♯` (`Module.compHom`, the module structure of
`ModuleCat.restrictScalars`). -/
@[instance_reducible] def baseChangePieceModule (m : ℕ) : Module Γ(S, U) ((𝒜.pullback g).sectionsPiece V m) :=
  letI := (𝒜.pullback g).sectionsPieceModuleBC V m
  Module.compHom ((𝒜.pullback g).sectionsPiece V m) (g.appLE U V hV).hom

theorem baseChangePieceTower (m : ℕ) :
    letI := baseAlgebra g U V hV
    letI := (𝒜.pullback g).sectionsPieceModuleBC V m
    letI := baseChangePieceModule g 𝒜 U V hV m
    IsScalarTower Γ(S, U) Γ(S', V) ((𝒜.pullback g).sectionsPiece V m) := by
  letI := baseAlgebra g U V hV
  letI := (𝒜.pullback g).sectionsPieceModuleBC V m
  letI := baseChangePieceModule g 𝒜 U V hV m
  exact ⟨fun r s n => by
    change ((g.appLE U V hV).hom r * s) • n = (g.appLE U V hV).hom r • s • n
    exact mul_smul _ _ _⟩

/-- `(g^*𝒜)(V) = ⊕_m Γ(V, g^*𝒜_m)` as a `Γ(S,U)`-module (componentwise). -/
@[instance_reducible] def baseChangeModule : Module Γ(S, U) ((𝒜.pullback g).sectionsRing V) :=
  letI := baseChangePieceModule g 𝒜 U V hV
  inferInstanceAs (Module Γ(S, U) (⨁ m, (𝒜.pullback g).sectionsPiece V m))

theorem baseChangeModule_smul (r : Γ(S, U)) (x : (𝒜.pullback g).sectionsRing V) :
    letI := (𝒜.pullback g).sectionsModuleBC V
    letI := baseChangeModule g 𝒜 U V hV
    r • x = (g.appLE U V hV).hom r • x := rfl

theorem baseChangeTower :
    letI := baseAlgebra g U V hV
    letI := (𝒜.pullback g).sectionsModuleBC V
    letI := baseChangeModule g 𝒜 U V hV
    IsScalarTower Γ(S, U) Γ(S', V) ((𝒜.pullback g).sectionsRing V) := by
  letI := baseAlgebra g U V hV
  letI := (𝒜.pullback g).sectionsModuleBC V
  letI := baseChangeModule g 𝒜 U V hV
  exact ⟨fun r s x => by
    rw [baseChangeModule_smul]
    change ((g.appLE U V hV).hom r * s) • x = (g.appLE U V hV).hom r • s • x
    exact mul_smul _ _ _⟩

/-- `(g^*𝒜)(V)` as a `Γ(S,U)`-algebra (`Algebra.ofModule` over `baseChangeModule`). -/
@[instance_reducible] def baseChangeAlgebra : Algebra Γ(S, U) ((𝒜.pullback g).sectionsRing V) :=
  letI := (𝒜.pullback g).sectionsModuleBC V
  letI := baseChangeModule g 𝒜 U V hV
  Algebra.ofModule
    (fun r x y => by
      rw [baseChangeModule_smul, baseChangeModule_smul, smul_eq_sectionsUnitHom_mul,
        smul_eq_sectionsUnitHom_mul, _root_.mul_assoc])
    (fun r x y => by
      rw [baseChangeModule_smul, baseChangeModule_smul, smul_eq_sectionsUnitHom_mul,
        smul_eq_sectionsUnitHom_mul, _root_.mul_left_comm])

theorem baseChangeAlgebra_algebraMap (r : Γ(S, U)) :
    letI := baseChangeAlgebra g 𝒜 U V hV
    algebraMap Γ(S, U) ((𝒜.pullback g).sectionsRing V) r =
      (𝒜.pullback g).sectionsUnitHom V ((g.appLE U V hV).hom r) := by
  letI := (𝒜.pullback g).sectionsModuleBC V
  letI := baseChangeModule g 𝒜 U V hV
  letI := baseChangeAlgebra g 𝒜 U V hV
  show r • (1 : (𝒜.pullback g).sectionsRing V) = _
  rw [baseChangeModule_smul, smul_eq_sectionsUnitHom_mul, mul_one]

/-- The unit `𝒜(U) → (g^*𝒜)(V)` as a `Γ(S,U)`-algebra homomorphism. -/
def baseChangeUnitAlgHom :
    letI := 𝒜.sectionsAlgebraBC U
    letI := baseChangeAlgebra g 𝒜 U V hV
    𝒜.sectionsRing U →ₐ[Γ(S, U)] (𝒜.pullback g).sectionsRing V :=
  letI := 𝒜.sectionsAlgebraBC U
  letI := baseChangeAlgebra g 𝒜 U V hV
  { baseChangeUnitRingHom g 𝒜 U V hV with
    commutes' := fun r => by
      show baseChangeUnitRingHom g 𝒜 U V hV (algebraMap Γ(S, U) (𝒜.sectionsRing U) r) =
        algebraMap Γ(S, U) ((𝒜.pullback g).sectionsRing V) r
      rw [𝒜.algebraMap_eq_sectionsUnitHom U, baseChangeUnitRingHom_sectionsUnitHom,
        baseChangeAlgebra_algebraMap] }

theorem baseChangeUnitAlgHom_apply (x : 𝒜.sectionsRing U) :
    letI := 𝒜.sectionsAlgebraBC U
    letI := baseChangeAlgebra g 𝒜 U V hV
    baseChangeUnitAlgHom g 𝒜 U V hV x = baseChangeUnitGraded g 𝒜 U V hV x := rfl

/-- The `m`-th piece of the unit as a `Γ(S,U)`-linear map (semilinearity of the section pullback,
`pullbackSectionsOn_smul_native`). -/
def baseChangeUnitPieceLinear (m : ℕ) :
    letI := 𝒜.sectionsPieceModuleBC U m
    letI := baseChangePieceModule g 𝒜 U V hV m
    𝒜.sectionsPiece U m →ₗ[Γ(S, U)] (𝒜.pullback g).sectionsPiece V m :=
  letI := 𝒜.sectionsPieceModuleBC U m
  letI := baseChangePieceModule g 𝒜 U V hV m
  { toFun := baseChangeUnitPiece g 𝒜 U V hV m
    map_add' := map_add _
    map_smul' := fun r a =>
      AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_smul_native g (𝒜.part m) U V hV r a }

/-- **Stacks 01I9 on a piece**: for affine `U`, `V`, `Γ(U, 𝒜_m) → Γ(V, g^*𝒜_m)` is a base change
along `g^♯`. -/
theorem isBaseChange_baseChangeUnitPieceLinear (hU : AlgebraicGeometry.IsAffineOpen U)
    (hVa : AlgebraicGeometry.IsAffineOpen V) (m : ℕ) :
    letI := baseAlgebra g U V hV
    letI := 𝒜.sectionsPieceModuleBC U m
    letI := (𝒜.pullback g).sectionsPieceModuleBC V m
    letI := baseChangePieceModule g 𝒜 U V hV m
    letI := baseChangePieceTower g 𝒜 U V hV m
    IsBaseChange Γ(S', V) (baseChangeUnitPieceLinear g 𝒜 U V hV m) := by
  letI := baseAlgebra g U V hV
  letI := 𝒜.sectionsPieceModuleBC U m
  letI := (𝒜.pullback g).sectionsPieceModuleBC V m
  letI := baseChangePieceModule g 𝒜 U V hV m
  letI := baseChangePieceTower g 𝒜 U V hV m
  haveI := 𝒜.quasicoherent m
  haveI := AlgebraicGeometry.Scheme.Modules.isIso_transpose_pullbackSectionsNative g (𝒜.part m)
    U hU V hVa hV
  exact IsBaseChange.of_isIso_extendRestrictScalars_transpose (g.appLE U V hV).hom
    (AlgebraicGeometry.Scheme.Modules.pullbackSectionsNative g (𝒜.part m) U V hV)
    (baseChangeUnitPieceLinear g 𝒜 U V hV m) (fun _ => rfl)

/-- The unit as a linear map is the direct sum of its pieces. -/
theorem baseChangeUnitAlgHom_toLinearMap :
    letI := 𝒜.sectionsAlgebraBC U
    letI := baseChangeAlgebra g 𝒜 U V hV
    letI := 𝒜.sectionsPieceModuleBC U
    letI := baseChangePieceModule g 𝒜 U V hV
    (baseChangeUnitAlgHom g 𝒜 U V hV).toLinearMap =
      DirectSum.lmap (baseChangeUnitPieceLinear g 𝒜 U V hV) := by
  letI := 𝒜.sectionsAlgebraBC U
  letI := baseChangeAlgebra g 𝒜 U V hV
  letI := 𝒜.sectionsPieceModuleBC U
  letI := baseChangePieceModule g 𝒜 U V hV
  refine DirectSum.linearMap_ext _ fun m => LinearMap.ext fun a => ?_
  show baseChangeUnitRingHom g 𝒜 U V hV (DirectSum.of (𝒜.sectionsPiece U) m a) =
    DirectSum.lmap (baseChangeUnitPieceLinear g 𝒜 U V hV) (DirectSum.of (𝒜.sectionsPiece U) m a)
  rw [baseChangeUnitRingHom_of, DirectSum.lmap_of]
  rfl

/-- **Stacks 01I9 for the section rings**: for affine `U`, `V`, the unit `𝒜(U) → (g^*𝒜)(V)` is a base
change along `g^♯ : Γ(S,U) → Γ(S',V)`, i.e. `Γ(S',V) ⊗_{Γ(S,U)} 𝒜(U) ≅ (g^*𝒜)(V)`. -/
theorem isBaseChange_baseChangeUnit (hU : AlgebraicGeometry.IsAffineOpen U)
    (hVa : AlgebraicGeometry.IsAffineOpen V) :
    letI := baseAlgebra g U V hV
    letI := 𝒜.sectionsAlgebraBC U
    letI := (𝒜.pullback g).sectionsAlgebraBC V
    letI := baseChangeAlgebra g 𝒜 U V hV
    letI := baseChangeTower g 𝒜 U V hV
    IsBaseChange Γ(S', V) (baseChangeUnitAlgHom g 𝒜 U V hV).toLinearMap := by
  letI := baseAlgebra g U V hV
  letI := 𝒜.sectionsAlgebraBC U
  letI := (𝒜.pullback g).sectionsAlgebraBC V
  letI := baseChangeAlgebra g 𝒜 U V hV
  letI := baseChangeTower g 𝒜 U V hV
  letI := 𝒜.sectionsPieceModuleBC U
  letI := (𝒜.pullback g).sectionsPieceModuleBC V
  letI := baseChangePieceModule g 𝒜 U V hV
  letI := baseChangePieceTower g 𝒜 U V hV
  rw [baseChangeUnitAlgHom_toLinearMap]
  exact IsBaseChange.directSum fun m => isBaseChange_baseChangeUnitPieceLinear g 𝒜 U V hV hU hVa m

end BaseChange

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
