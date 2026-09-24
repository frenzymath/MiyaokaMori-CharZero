import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.OmegaPullbackMap
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechPullbackMap
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaOpenImmersionSquare

/-! # The maps of the first fundamental sequence of relative differentials

The two canonical maps of the first fundamental sequence of relative differentials
(Stacks 01UX / 02K4) for `f : X ⟶ Y`, `g : Y ⟶ S`:

* `Omega.baseChangeMap f g : f^*Ω_{Y/S} ⟶ Ω_{X/S}` — the pullback map of differentials
  (`Omega.pullbackMap`) for the trivially commuting square `f ≫ g = (f ≫ g) ≫ 𝟙 S`;
  on generators it sends `f^*(d_{Y/S} b)` to `d_{X/S}(f^♯ b)` (`baseChangeMap_app_pullbackSectionsOn_d`);
* `Omega.compMap f g : Ω_{X/S} ⟶ Ω_{X/Y}` — obtained from the universal property of `Ω_{X/S}`
  (`Omega.homEquivDerivation`) applied to `d_{X/Y}`, which is an `(f ≫ g)⁻¹O_S`-derivation because
  `(f ≫ g)^♯ = f^♯ ∘ g^♯` lands in the image of `f⁻¹O_Y`; on generators `d_{X/S} a ↦ d_{X/Y} a`
  (`compMap_app_d`);
* `baseChangeMap ≫ compMap = 0` (`baseChangeMap_comp_compMap`): by the adjunction
  `pullback f ⊣ pushforward f` and `Omega.hom_ext` it suffices to check on `d_{Y/S} b`, where the
  composite is `d_{X/Y}(f^♯ b) = 0`.

Source: Stacks 01UV (functoriality of `Ω`), 01UX (the sequence); the tangent sequence
(2.2) in §2.1 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

local notation "dΩ[" f "]" => Omega.homEquivDerivation f (Omega f) (𝟙 (Omega f))

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- `d_{X/Y} : O_X → Ω_{X/Y}` viewed as an `(f ≫ g)⁻¹O_S`-derivation: it kills the image of
`(f ≫ g)⁻¹O_S` because `(f ≫ g).appLE V U e = g.app V ≫ f.appLE (g⁻¹V) U e` factors through `f⁻¹O_Y`. -/
def Omega.compDerivation :
    ((Omega f).val).Derivation' (Scheme.inverseImageStructureMap (f ≫ g)) where
  d {U} := (dΩ[f]).d (X := U)
  d_mul {U} a b := (dΩ[f]).d_mul (X := U) a b
  d_map {U V} i x := (dΩ[f]).d_map (X := U) i x
  d_app {U} a := by
    obtain ⟨V, e, r, hr⟩ := Scheme.inverseImageStructureMap_app_eq_appLE (f ≫ g) U.unop a
    have hk : ((f ≫ g).appLE V U.unop e).hom r =
        (f.appLE (g ⁻¹ᵁ V) U.unop e).hom ((g.app V).hom r) :=
      congrArg (fun t => t.hom r) (Scheme.Hom.comp_appLE f g V U.unop e)
    exact (congrArg ((dΩ[f]).d (X := U)) (hr.trans hk)).trans
      (Omega.derivation_appLE f (dΩ[f]) (g ⁻¹ᵁ V) U.unop e ((g.app V).hom r))

/-- `β : Ω_{X/S} ⟶ Ω_{X/Y}`, the second map of the first fundamental sequence (Stacks 01UX). -/
def Omega.compMap : Omega (f ≫ g) ⟶ Omega f :=
  (Omega.homEquivDerivation (f ≫ g) (Omega f)).symm (Omega.compDerivation f g)

/-- `β (d_{X/S} a) = d_{X/Y} a`. -/
theorem Omega.compMap_app_d (U : X.Opens) (a : Γ(X, U)) :
    (Omega.compMap f g).app U ((dΩ[f ≫ g]).d (X := op U) a) = (dΩ[f]).d (X := op U) a :=
  Omega.homEquivDerivation_symm_d (f ≫ g) (Omega.compDerivation f g) U a

/-- `α : f^*Ω_{Y/S} ⟶ Ω_{X/S}`, the first map of the first fundamental sequence (Stacks 01UX):
the pullback map of differentials for the square `f ≫ g = (f ≫ g) ≫ 𝟙 S`. -/
def Omega.baseChangeMap : (Scheme.Modules.pullback f).obj (Omega g) ⟶ Omega (f ≫ g) :=
  Omega.pullbackMap f g (f ≫ g) (𝟙 S) (Category.comp_id _).symm

/-- `α (f^*(d_{Y/S} b)|_U) = d_{X/S} (f.appLE V U e b)` for `U ⊆ f⁻¹V`. -/
theorem Omega.baseChangeMap_app_pullbackSectionsOn_d (V : Y.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V)
    (b : Γ(Y, V)) :
    (Omega.baseChangeMap f g).app U
        (Scheme.Modules.pullbackSectionsOn f (Omega g) V U e ((dΩ[g]).d (X := op V) b)) =
      (dΩ[f ≫ g]).d (X := op U) ((f.appLE V U e).hom b) := by
  have h1 := Omega.pullbackMap_unit_app_d f g (f ≫ g) (𝟙 S) (Category.comp_id _).symm V b
  have h2 := congr($((Omega.baseChangeMap f g).mapPresheaf.naturality (homOfLE e).op)
    (Scheme.Modules.pullbackUnitHom f (Omega g) V ((dΩ[g]).d (X := op V) b)))
  refine h2.trans ?_
  refine (congrArg ((Omega (f ≫ g)).presheaf.map (homOfLE e).op) h1).trans ?_
  exact ((dΩ[f ≫ g]).d_map (X := op (f ⁻¹ᵁ V)) (homOfLE e).op _).symm

/-- The pushforward functor sends the zero morphism to the zero morphism. -/
theorem Scheme.Modules.pushforward_map_zero {M N : X.Modules} :
    (Scheme.Modules.pushforward f).map (0 : M ⟶ N) = 0 :=
  Scheme.Modules.hom_ext _ _ fun _ => rfl

/-- `α ≫ β = 0`: the first fundamental sequence is a complex (Stacks 01UX). -/
theorem Omega.baseChangeMap_comp_compMap :
    Omega.baseChangeMap f g ≫ Omega.compMap f g = 0 := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_apply, Adjunction.homEquiv_apply,
    Scheme.Modules.pushforward_map_zero, comp_zero]
  apply Omega.hom_ext g
  intro V b
  change (Omega.compMap f g).app (f ⁻¹ᵁ V)
    (((Scheme.Modules.pushforward f).map (Omega.baseChangeMap f g)).app V
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (Omega g)).app V
        ((dΩ[g]).d (X := op V) b))) =
      (0 : Omega g ⟶ (Scheme.Modules.pushforward f).obj (Omega f)).app V ((dΩ[g]).d (X := op V) b)
  have h1 := Omega.pullbackMap_unit_app_d f g (f ≫ g) (𝟙 S) (Category.comp_id _).symm V b
  refine (congrArg ((Omega.compMap f g).app (f ⁻¹ᵁ V)) h1).trans ?_
  refine (Omega.compMap_app_d f g (f ⁻¹ᵁ V) _).trans ?_
  have h3 : (f.app V).hom b = (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom b :=
    congrArg (fun t => t.hom b) (Scheme.Hom.app_eq_appLE f)
  exact (congrArg ((dΩ[f]).d (X := op (f ⁻¹ᵁ V))) h3).trans
    (Omega.derivation_appLE f (dΩ[f]) V (f ⁻¹ᵁ V) le_rfl b)

end AlgebraicGeometry

end
