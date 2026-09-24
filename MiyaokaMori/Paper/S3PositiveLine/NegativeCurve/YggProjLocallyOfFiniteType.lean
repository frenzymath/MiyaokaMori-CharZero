import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.YggGeometry

/-! # The structure morphism of `Y_κ^GG` is locally of finite type

Statement: for every field `K` and every `κ`, the structure morphism `π_κ = YGG.proj f κ : Y_κ^GG = Proj_C S → C`
is locally of finite type (registered as an instance).

Proof: `YGG.proj_isProper` (`YggGeometry`) shows that `π_κ` is proper (take `hn := rfl` for `n := dim X`); Mathlib's
class `AlgebraicGeometry.IsProper` `extends … LocallyOfFiniteType` (Stacks 01W0: proper = separated + universally
closed + finite type), so `IsProper.toLocallyOfFiniteType` gives the conclusion.

The route inside `YGG.proj_isProper`:
1. Let `Z = MMSetup.cone f`, `s = (MMSetup.seed f).1`, `Z^× = MMSetup.punctured f`. `s` is a section of the affine
   (hence separated) morphism `Z → C`, so it is a closed immersion (`AlgebraicGeometry.IsClosedImmersion.of_section`);
   `s` lands in `Z^×` by `seedSection_mem_punctured`; `X` is smooth and connected over `K`, so for `n = dim X` we have
   `SmoothOfRelativeDimension n (X ↘ Spec K)` (`IsSmoothOver.isLocallyFree_omega` gives that `Ω` has constant rank
   `dim X`), and `puncturedCone_smoothOfRelativeDimension` gives that `Z^× → C` is smooth of relative dimension `n+1`.
2. By `jetGradedAlgebra_isLocallyWeightedPolynomial` (for every `r = κ`, including `κ = 0`, where the variable set
   is empty and `S = O_C`), `S = jetAlgebra f κ` is locally the weighted polynomial algebra `O_U[x_{i,q}]` with weights
   `(1,…,1,…,κ,…,κ)` in finitely many variables.
3. By `relativeProj_locallyWeighted_localProduct` there is an open cover `𝒰` of `C` with `Y ×_C U_i ≅ U_i ×_K P(w)`,
   compatibly with the projections to `U_i`.
4. `P(w) = Proj K[x_{i,q}] → Spec K` is proper (`local_weightedProjToSpec_isProper`); properness is stable under base
   change, so `U_i ×_K P(w) → U_i` is proper.
5. Properness is Zariski-local on the target (`IsZariskiLocalAtTarget`, `iff_of_openCover` for `𝒰`) and invariant
   under composition with isomorphisms, so `π_κ` is proper, in particular locally of finite type.

Source: Proposition 2.4 of the paper ("`S` is locally a weighted polynomial algebra", "`Y_k^GG` is
projective over `C`"); Stacks 01O4, 01T8, 01W0.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem YGG.proj_locallyOfFiniteType {K : Type u} [Field K] {X : SmoothProjectiveVariety K}
    {C : SmoothProjectiveCurve K} (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) :
    AlgebraicGeometry.LocallyOfFiniteType (YGG.proj f κ) :=
  (YGG.proj_isProper f rfl κ).toLocallyOfFiniteType

instance YGG.proj_locallyOfFiniteType_inst {K : Type u} [Field K] {X : SmoothProjectiveVariety K}
    {C : SmoothProjectiveCurve K} (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) :
    AlgebraicGeometry.LocallyOfFiniteType (YGG.proj f κ) :=
  YGG.proj_locallyOfFiniteType f κ

end
