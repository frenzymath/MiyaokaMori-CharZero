import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiprodLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.SheafDualLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesFiniteTypeInstances
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAdditiveShortExact
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkOfIsLineBundle

/-! # The rank of `O_X ⊕ L` for a line bundle `L`

For a line bundle `L` on a scheme `X`, the rank of `O_X ⊕ L` (the `biprod` in `X.Modules`) at every
point is `2`, and so is the rank of its dual `(O_X ⊕ L)^∨`.

Proof sketch:
1. The short complex `O_X → O_X ⊕ L → L` (`biprod.inl`, `biprod.snd`) is split
   (`ShortComplex.Splitting.ofHasBinaryBiproduct`), hence short exact (`Splitting.shortExact`).
2. Rank is additive on short exact sequences of finite type locally free sheaves
   (`rankAtStalk_add_of_shortExact`): `rank(O ⊕ L) = rank O + rank L`.
3. `O_X` and `L` are line bundles (`IsLineBundle.unit`), so both ranks are `1`
   (`rankAtStalk_eq_one_of_isLineBundle`): `rank(O ⊕ L) = 2`.
4. The dual of a finite type locally free sheaf of constant rank `r` is locally free of the same rank
   (`isLocallyFree_dual`): `rank((O ⊕ L)^∨) = 2`.

References: Hartshorne II Ex. 5.16 / Stacks 01CB (rank is additive; the dual of a finite locally free
module has the same rank). Used for the geometry of the projective bundle `P(O_X ⊕ L)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- rank(O_X ⊕ L) = 2 for a line bundle L. -/
theorem AlgebraicGeometry.Scheme.Modules.rankAtStalk_unit_biprod_of_isLineBundle
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle] (x : X) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk
      (CategoryTheory.Limits.biprod (C := X.Modules)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L) x = 2 := by
  have hS : (CategoryTheory.ShortComplex.mk
      (CategoryTheory.Limits.biprod.inl :
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
          CategoryTheory.Limits.biprod (C := X.Modules)
            (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)
      (CategoryTheory.Limits.biprod.snd : _ ⟶ L) CategoryTheory.Limits.biprod.inl_snd).ShortExact :=
    (CategoryTheory.ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact
  have h := AlgebraicGeometry.Scheme.Modules.rankAtStalk_add_of_shortExact hS x
  change AlgebraicGeometry.Scheme.Modules.rankAtStalk
      (CategoryTheory.Limits.biprod (C := X.Modules)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L) x =
    AlgebraicGeometry.Scheme.Modules.rankAtStalk
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) x +
      AlgebraicGeometry.Scheme.Modules.rankAtStalk L x at h
  rw [h, AlgebraicGeometry.Scheme.Modules.rankAtStalk_eq_one_of_isLineBundle,
    AlgebraicGeometry.Scheme.Modules.rankAtStalk_eq_one_of_isLineBundle]

/-- rank((O_X ⊕ L)^∨) = 2 for a line bundle L. -/
theorem AlgebraicGeometry.Scheme.Modules.rankAtStalk_dual_unit_biprod_of_isLineBundle
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle] (x : X) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk
      (AlgebraicGeometry.Scheme.Modules.dual
        (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)) x = 2 :=
  (AlgebraicGeometry.Scheme.Modules.isLocallyFree_dual _ 2 inferInstance
    (AlgebraicGeometry.Scheme.Modules.rankAtStalk_unit_biprod_of_isLineBundle L)).2 x

end
