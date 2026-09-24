import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.HomogeneousEquationSectionAtTotalSpaceSectionCoordinate
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesPowLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesFiniteTypeInstances

/-! # The section of the total space given by a tuple of sections, and its coordinates

`N+1` global sections `f` of a line bundle `A` give a section `σ_f` of the total space of `A^{⊕(N+1)}`
(`tupleTotSection`, the same term as `seedSection.totSection`); the canonical isomorphism
`σ_f^*π^*A ≅ A` (`tupleTotSection.pullbackIso`); the `i`-th coordinate `τ_i` of the tautological
section (`tautologicalCoordinate`, the same term as the coordinates in the definition of
`homogeneousEquationSection`).
Statement (`tupleTotSection_coordinate_pullback`): `σ_f^*(τ_i)` equals `f_i` under `pullbackIso`.
Proof: the special case `A_ℓ ≡ A`, `s₀ = Σ_j ι_j(f_j)` of the coordinate formula for
`totalSpaceSectionEquiv`, together with `pr_i(Σ_j ι_j(f_j)) = f_i`
(`Modules.biproduct_π_app_sum_ι_app`, from `biproduct.ι_π_self` / `ι_π_ne`).
Source: Definition 2.1 of the paper (the seed section `s = (f_0, …, f_N)`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The section `σ_f : C → Tot(A^{⊕(N+1)})` given by the tuple `f` (together with `σ_f ≫ π = 𝟙`); the same
term as `seedSection.totSection`. -/
noncomputable def AlgebraicGeometry.Scheme.tupleTotSection {C : AlgebraicGeometry.Scheme.{u}}
    (A : C.Modules) [A.IsLineBundle] (N : ℕ)
    (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u)) :
    { σ : C ⟶ (AlgebraicGeometry.Scheme.totalSpace
        (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).left //
      σ ≫ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom =
        CategoryTheory.CategoryStruct.id C } :=
  AlgebraicGeometry.Scheme.totalSpaceSectionEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
    (∑ i : Fin (N + 1),
      ((CategoryTheory.Limits.biproduct.ι (fun _ : Fin (N + 1) => A) i).val.app (Opposite.op ⊤)).hom (f i))

/-- The canonical isomorphism `σ_f^* π^* A ≅ A`: `pullbackComp`, `pullbackCongr` along `σ_f ≫ π = 𝟙`,
`pullbackId`. -/
noncomputable def AlgebraicGeometry.Scheme.tupleTotSection.pullbackIso {C : AlgebraicGeometry.Scheme.{u}}
    (A : C.Modules) [A.IsLineBundle] (N : ℕ)
    (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u)) :
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.tupleTotSection A N f).1).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom).obj A) ≅
      A :=
  (AlgebraicGeometry.Scheme.Modules.pullbackComp (AlgebraicGeometry.Scheme.tupleTotSection A N f).1
      (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom).app A ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr (AlgebraicGeometry.Scheme.tupleTotSection A N f).2).app A ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackId C).app A

/-- The `i`-th coordinate `τ_i ∈ Γ(Tot, π^*A)` of the tautological section. -/
noncomputable def AlgebraicGeometry.Scheme.tautologicalCoordinate {C : AlgebraicGeometry.Scheme.{u}}
    (A : C.Modules) [A.IsLineBundle] (N : ℕ) (i : Fin (N + 1)) :
    (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom).obj A).val.obj
      (Opposite.op ⊤) : Type u) :=
  ((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom).map
        (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)
    (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
      (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)))
      (CategoryTheory.CategoryStruct.id _))

/-- Pulling the tautological coordinate `τ_i` back along the section `σ_f` given by the tuple `f` and
applying the canonical isomorphism `σ^*π^*A ≅ A` gives `f_i`. -/
theorem AlgebraicGeometry.Scheme.tupleTotSection_coordinate_pullback {C : AlgebraicGeometry.Scheme.{u}}
    (A : C.Modules) [A.IsLineBundle] (N : ℕ)
    (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u)) (i : Fin (N + 1)) :
    (AlgebraicGeometry.Scheme.tupleTotSection.pullbackIso A N f).hom.app ⊤
      (sectionPullbackAlong (AlgebraicGeometry.Scheme.tupleTotSection A N f).1
        (AlgebraicGeometry.Scheme.tautologicalCoordinate A N i)) = f i := by
  have h := AlgebraicGeometry.Scheme.totalSpaceSectionEquiv_coordinate (fun _ : Fin (N + 1) => A)
    (∑ j : Fin (N + 1), ((biproduct.ι (fun _ : Fin (N + 1) => A) j).val.app (Opposite.op ⊤)).hom (f j)) i
  rw [AlgebraicGeometry.Scheme.Modules.biproduct_π_app_sum_ι_app] at h
  exact h

end
