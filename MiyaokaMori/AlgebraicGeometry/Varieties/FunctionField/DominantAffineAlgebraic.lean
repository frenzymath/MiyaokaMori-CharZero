import MiyaokaMori.Prelude

/-! # Section maps of a dominant morphism are injective and algebraic

Let `X`, `Y` be integral schemes and `f : X → Y` a morphism sending the generic point `η_X` to
the generic point `η_Y`. Let `U ⊆ Y` be open and `V ⊆ f⁻¹U` a nonempty open of `X`. Then (1) the
map of section rings `f.appLE : Γ(Y,U) → Γ(X,V)` is injective; (2) if moreover `U` is affine and
the residue field map `κ(f η_X) → κ(η_X)` at the generic point is finite, then `Γ(X,V)` is
algebraic over `Γ(Y,U)`.

Proof sketch:
1. The evaluation map `ev : Γ(X,V) → κ(η_X)` at the generic point is injective: the germ map is
   injective (`X` integral, `germ_injective_of_isIntegral`) and the stalk at the generic point is
   a field, so the residue map is injective.
2. Naturality of evaluation (`Scheme.Hom.evaluation_naturality`): `κ(f η_X) → κ(η_X)` sends
   `ev_Y(a)` to `ev_X(f.appLE a)`.
3. (1): `f.appLE a = 0` gives `ev_Y(a) = 0` (field maps are injective), so `η_Y = f η_X ∉ D(a)`,
   so `D(a) = ∅` (the generic point lies in every nonempty open), so `a = 0` (`Y` is reduced,
   `basicOpen_eq_bot_iff`).
4. (2): `κ(y)` (`y = f η_X ∈ U`) is algebraic over `Γ(Y,U)`: the stalk `O_{Y,y}` is a localization
   of `Γ(Y,U)` (`IsAffineOpen.isLocalization_stalk`), localizations are algebraic
   (`IsLocalization.isAlgebraic`), and the residue map is surjective. `κ(η_X)/κ(y)` is finite,
   hence algebraic; transitivity makes `κ(η_X)` algebraic over `Γ(Y,U)`; `ev_X` is an injective
   `Γ(Y,U)`-algebra map, so every element of `Γ(X,V)` is algebraic (`isAlgebraic_algHom_iff`).

Source: the sentence "`R → A_i` is an injective finite type map of domains with finite extension
of fraction fields" in the proof of Stacks 02RM.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

open CategoryTheory TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)

theorem genericPoint_mem_of_nonempty (V : X.Opens) (hV : (V : Set X).Nonempty) :
    genericPoint X ∈ V := by
  refine ((genericPoint_spec X).mem_open_set_iff V.2).mpr ?_
  simpa using hV

theorem evaluation_genericPoint_injective (V : X.Opens) (hV : genericPoint X ∈ V) :
    Function.Injective (X.evaluation V (genericPoint X) hV) := by
  have h1 : Function.Injective (X.presheaf.germ V (genericPoint X) hV) :=
    germ_injective_of_isIntegral _ _ hV
  have h2 : Function.Injective (X.residue (genericPoint X)) :=
    (IsLocalRing.residue (X.functionField)).injective
  exact h2.comp h1

theorem residueFieldMap_evaluation_eq_evaluation_appLE (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (x : X) (hx : x ∈ V) (a : Γ(Y, U)) :
    f.residueFieldMap x (Y.evaluation U (f x) (e hx) a) =
      X.evaluation V x hx (f.appLE U V e a) := by
  refine (Scheme.evaluation_naturality_apply f x (e hx) a).trans ?_
  simp only [Scheme.Hom.appLE, Scheme.evaluation, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_res_apply]

theorem appLE_injective_of_genericPoint (hf : f (genericPoint X) = genericPoint Y)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (hV : genericPoint X ∈ V) :
    Function.Injective (f.appLE U V e).hom := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h1 := residueFieldMap_evaluation_eq_evaluation_appLE f U V e _ hV a
  rw [show (f.appLE U V e) a = 0 from ha, map_zero] at h1
  have h2 : Y.evaluation U (f (genericPoint X)) (e hV) a = 0 :=
    (f.residueFieldMap (genericPoint X)).hom.injective (by simpa using h1)
  replace h2 := (Y.evaluation_eq_zero_iff_notMem_basicOpen _ (e hV) a).mp h2
  rw [← basicOpen_eq_bot_iff]
  by_contra hne
  apply h2
  rw [hf]
  apply genericPoint_mem_of_nonempty
  exact Set.nonempty_iff_ne_empty.mpr fun h ↦ hne (Opens.ext (h.trans Opens.coe_bot.symm))

theorem residueField_isAlgebraic_of_isAffineOpen {U : Y.Opens} (hU : IsAffineOpen U) (y : Y)
    (hy : y ∈ U) :
    letI := (Y.evaluation U y hy).hom.toAlgebra
    Algebra.IsAlgebraic Γ(Y, U) (Y.residueField y) := by
  letI := (Y.evaluation U y hy).hom.toAlgebra
  letI := Y.presheaf.algebra_section_stalk ⟨y, hy⟩
  have hloc := hU.isLocalization_stalk ⟨y, hy⟩
  have : Nontrivial Γ(Y, U) := by
    have : Nonempty U := ⟨⟨y, hy⟩⟩
    infer_instance
  have halg : Algebra.IsAlgebraic Γ(Y, U) (Y.presheaf.stalk y) :=
    IsLocalization.isAlgebraic _ (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
  let φ : Y.presheaf.stalk y →ₐ[Γ(Y, U)] Y.residueField y :=
    { (Y.residue y).hom with commutes' := fun _ ↦ rfl }
  refine ⟨fun t ↦ ?_⟩
  obtain ⟨s, rfl⟩ := Y.residue_surjective y t
  exact (halg.isAlgebraic s).algHom φ

theorem appLE_isAlgebraic_of_genericPoint
    (hfin : (f.residueFieldMap (genericPoint X)).hom.Finite)
    {U : Y.Opens} (hU : IsAffineOpen U) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
    (hV : genericPoint X ∈ V) :
    letI := (f.appLE U V e).hom.toAlgebra
    Algebra.IsAlgebraic Γ(Y, U) Γ(X, V) := by
  letI algRC := (f.appLE U V e).hom.toAlgebra
  letI algRk := (Y.evaluation U (f (genericPoint X)) (e hV)).hom.toAlgebra
  letI algkl := (f.residueFieldMap (genericPoint X)).hom.toAlgebra
  letI algCl := (X.evaluation V (genericPoint X) hV).hom.toAlgebra
  letI algRl : Algebra Γ(Y, U) (X.residueField (genericPoint X)) :=
    ((f.residueFieldMap (genericPoint X)).hom.comp
      (Y.evaluation U (f (genericPoint X)) (e hV)).hom).toAlgebra
  have t1 : IsScalarTower Γ(Y, U) (Y.residueField (f (genericPoint X)))
      (X.residueField (genericPoint X)) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have t2 : IsScalarTower Γ(Y, U) Γ(X, V) (X.residueField (genericPoint X)) :=
    IsScalarTower.of_algebraMap_eq fun a ↦
      residueFieldMap_evaluation_eq_evaluation_appLE f U V e _ hV a
  have a1 : Algebra.IsAlgebraic Γ(Y, U) (Y.residueField (f (genericPoint X))) :=
    residueField_isAlgebraic_of_isAffineOpen hU _ (e hV)
  have hfin' : Module.Finite (Y.residueField (f (genericPoint X)))
      (X.residueField (genericPoint X)) := hfin
  have a2 : Algebra.IsAlgebraic (Y.residueField (f (genericPoint X)))
      (X.residueField (genericPoint X)) := Algebra.IsAlgebraic.of_finite _ _
  have a3 : Algebra.IsAlgebraic Γ(Y, U) (X.residueField (genericPoint X)) :=
    Algebra.IsAlgebraic.trans _ (Y.residueField (f (genericPoint X))) _
  refine ⟨fun c ↦ ?_⟩
  exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom Γ(Y, U) Γ(X, V)
    (X.residueField (genericPoint X))) (evaluation_genericPoint_injective V hV)).mp
    (a3.isAlgebraic _)

end AlgebraicGeometry

end
