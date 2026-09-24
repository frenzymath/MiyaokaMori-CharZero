import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.OmegaPullbackMap
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentialsLocallyFree
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.TangentBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualPullbackCommute
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeTangentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualFunctor

/-! # The relative tangent sheaf of a product

The relative tangent sheaf of a product: `T_{(C×_k X)/C} ≃ pr_2^*T_X` (`C ×_k X → C` is the base
change of `X → Spec k`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The relative tangent sheaf of a product: `T_{(C×_k X)/C} ≅ pr₂^*T_X`.

Reference: Stacks 01V0 (base change of `Ω`).

Proof: write `f = X → Spec k`, `g = C → Spec k`, `P = C ×_k X`, `pr₁ : P → C`, `pr₂ : P → X`.
The square `(pr₂, pr₁, f, g)` is a fibre-product square (`IsPullback.of_hasPullback g f` flipped),
so Stacks 01V0 shows that `Omega.pullbackMap pr₂ f pr₁ g : pr₂^*Ω_{X/k} ⟶ Ω_{P/C}` is an isomorphism
(`Omega.pullbackMap_isIso_of_isPullback`). Dualize:
`T_{P/C} = (Ω_{P/C})^∨ ≅ (pr₂^*Ω_{X/k})^∨` (functoriality of the dual, `moduleSheafDualIso`)
`≅ pr₂^*(Ω_{X/k}^∨)` (the dual of a locally free sheaf of finite rank commutes with pullback,
`Modules.dual_pullback`; `Ω_{X/k}` is locally free of finite type since `X` is smooth)
`= pr₂^*T_X` (the underlying module of `tangentBundle X` is by definition `Ω_{X/k}^∨`). -/
theorem relativeTangent_prod_fst {k : Type u} [Field k] (C : SmoothProjectiveCurve k)
    (X : SmoothProjectiveVariety k) :
    Nonempty (AlgebraicGeometry.relativeTangent
        (CategoryTheory.Limits.pullback.fst (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback
        (CategoryTheory.Limits.pullback.snd (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj (tangentBundle X).toModules) := by
  let f := X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
  let g := C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
  -- the square (pr₂, pr₁, f, g) is a fibre-product square
  have hsq : CategoryTheory.IsPullback (CategoryTheory.Limits.pullback.snd g f)
      (CategoryTheory.Limits.pullback.fst g f) f g :=
    (CategoryTheory.IsPullback.of_hasPullback g f).flip
  -- Stacks 01V0: pr₂^*Ω_{X/k} ⟶ Ω_{P/C} is an isomorphism
  let m := AlgebraicGeometry.Omega.pullbackMap (CategoryTheory.Limits.pullback.snd g f) f
    (CategoryTheory.Limits.pullback.fst g f) g hsq.w
  have : CategoryTheory.IsIso m :=
    AlgebraicGeometry.Omega.pullbackMap_isIso_of_isPullback _ _ _ _ hsq
  -- Ω_{X/k} is locally free of finite type (X smooth)
  have : AlgebraicGeometry.Smooth f := X.smooth
  have := AlgebraicGeometry.Omega_isFiniteType f
  have := AlgebraicGeometry.isLocallyFree_omega_of_smooth f
  obtain ⟨d⟩ := AlgebraicGeometry.Scheme.Modules.dual_pullback
    (CategoryTheory.Limits.pullback.snd g f) (AlgebraicGeometry.Omega f)
  exact ⟨AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso (CategoryTheory.asIso m) ≪≫ d⟩

end
