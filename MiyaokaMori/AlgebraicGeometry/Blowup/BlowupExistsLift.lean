import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLift
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks01og
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupReesLiftMaps
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0806_ReesLiftMapsMapOne
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0806_ReesLiftMapsMapMul
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffCartierLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback

/-! # Existence of the lift to the blowup

Existence half of the universal property of the blowup (Stacks 0806, second assertion):
if `f : Y → X` makes `f⁻¹I·O_Y` invertible, then `f` factors through `b : Bl_I X → X`.

Source: Stacks 0806 (proof: Stacks 01O4 / 01N8, morphisms into a relative Proj).

The lift is built from a `relativeProj.LiftData` of the Rees algebra, whose pieces are proved in
sibling modules:
* `blowup_exists_reesLiftMaps`: the graded maps `Ψ_n : f^*(Iⁿ) ⟶ J^{⊗n}` with `Ψ_n ≫ μ_n = θ_n`
  and `Ψ_1` an epimorphism;
* `blowup_reesLiftMaps_map_one`: the degree-`0` condition;
* `blowup_reesLiftMaps_map_mul`: multiplicativity, reduced to `monoidalPowToUnit_mono`.
The `generates` field (`Ψ_1` epi on `Y`) and the line-bundle instance on `J.toModules`
(`EffCartier.ideal_isLineBundle`) are supplied here.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Stacks 0806, existence of the factorization.** Let `J := I.comap f` (the ideal sheaf `f⁻¹I·O_Y`) be
invertible. Then there is `g : Y ⟶ Bl_I X` with `g ≫ b = f`.

Proof (the route of Stacks 0806 via morphisms into a relative Proj, Stacks 01O4):

1. **The graded map.** For every `n`, the pullback `θ_n : f^*(Iⁿ) → f^*O_X = O_Y` of the inclusion `Iⁿ ⊆ O_X`
   has image `Jⁿ` (affine-locally `J(V) = I(U)·Γ(V)` (`comap_ideal_eq_map_appLE`) and
   `I(U)ⁿ·Γ(V) = (I(U)·Γ(V))ⁿ`), and since `J` is invertible the multiplication `μ_n : J^{⊗n} → O_Y` is a
   monomorphism with image `Jⁿ` (locally `J = (g)`, `g` a nonzerodivisor). Factoring gives `O_Y`-linear maps
   `Ψ_n : f^*(Iⁿ) → J^{⊗n}` with `Ψ_n ≫ μ_n = θ_n`, and `Ψ_1` is an epimorphism
   (`blowup_exists_reesLiftMaps`). These form a `relativeProj.LiftData I.reesAlgebra f J.toModules`:
   `map_one` (`blowup_reesLiftMaps_map_one`: degree `0` is the unit isomorphism), `map_mul`
   (`blowup_reesLiftMaps_map_mul`: both sides multiply sections; cancel the mono `μ_{m+n}`), and `generates`
   (take `U = ⊤`, `m = 1`: the pullback functor along `⊤.ι` preserves epimorphisms).
2. **The lift.** `J.toModules` is a line bundle (`EffCartier.ideal_isLineBundle`, Stacks 01WQ), so
   `relativeProj.lift I.reesAlgebra f J.toModules D` is a morphism
   `Y ⟶ (relativeProj I.reesAlgebra).left = (blowup I).left`, and `relativeProj.lift_hom` gives
   `lift ≫ π = f`. Here `blowup I = relativeProj I.reesAlgebra` by definition.

Edge cases: `I = ⊥`: `J = ⊥` is invertible only if `Y = ∅`, and the empty scheme maps to anything. `I = ⊤`:
`J = ⊤`, `Ψ_n` are the unit maps, the lift is `f` followed by the inverse of `Bl_⊤ X ≅ X`. `Y = ∅`: trivial. -/
theorem AlgebraicGeometry.Scheme.blowup_exists_lift {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) {Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
    (hf : MiyaokaMori.Statement.IsInvertibleIdeal (I.comap f)) :
    ∃ g : Y ⟶ (AlgebraicGeometry.Scheme.blowup I).left,
      g ≫ (AlgebraicGeometry.Scheme.blowup I).hom = f := by
  obtain ⟨Ψ, hΨ, hepi⟩ := AlgebraicGeometry.Scheme.blowup_exists_reesLiftMaps I f hf
  let D : AlgebraicGeometry.Scheme.relativeProj.LiftData I.reesAlgebra f (I.comap f).toModules :=
    { Ψ := Ψ
      map_one := AlgebraicGeometry.Scheme.blowup_reesLiftMaps_map_one I f Ψ hΨ
      map_mul := AlgebraicGeometry.Scheme.blowup_reesLiftMaps_map_mul I f hf Ψ hΨ
      generates := fun t => ⟨⊤, trivial, 1, Nat.one_pos,
        (AlgebraicGeometry.Scheme.Modules.pullback (⊤ : Y.Opens).ι).map_epi (Ψ 1)⟩ }
  have : (I.comap f).toModules.IsLineBundle :=
    AlgebraicGeometry.Scheme.EffCartier.ideal_isLineBundle (⟨I.comap f, hf⟩ : Y.EffCartier)
  exact ⟨AlgebraicGeometry.Scheme.relativeProj.lift I.reesAlgebra f (I.comap f).toModules D,
    AlgebraicGeometry.Scheme.relativeProj.lift_hom I.reesAlgebra f (I.comap f).toModules D⟩

end
