import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Sections from stalkwise representatives of a rational function

On an integral scheme, local sections with the same image in its actual function field agree
on their overlaps. Thus stalkwise lifts of one fixed rational function glue to a section on
the prescribed open. If the stalkwise lifts are units, the resulting section is a unit on
that whole open, by the structure sheaf's stalkwise criterion for units.

This supplies a gluing step for the local equations of a possibly non-effective divisor on a
curve. The hypotheses use actual stalk elements or units, not
orders of vanishing; no regularity criterion on a singular curve is assumed. Constructing
the local equations from the divisor coefficients remains a separate step.

Sources: Stacks Project, `morphisms.tex`, `lemma-integral-scheme-rational-functions`, and
`sheaves.tex`, `lemma-condition-star-sections`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [hU : Nonempty U]

/-- A rational function represented in every stalk on an open comes from a section there. -/
theorem exists_section_of_stalkwise_lift (f : X.functionField)
    (h : ∀ x : U, ∃ a : X.presheaf.stalk x.1,
      algebraMap (X.presheaf.stalk x.1) X.functionField a = f) :
    ∃ s : Γ(X, U), X.germToFunctionField U s = f := by
  classical
  choose a ha using h
  choose V hVU hxV s hs using fun x : U ↦ X.presheaf.exists_le_germ_eq (a x) x.2
  have (x : U) : Nonempty (V x) := ⟨⟨x.1, hxV x⟩⟩
  have hsf (x : U) : X.germToFunctionField (V x) (s x) = f := by
    rw [← X.algebraMap_germ_eq_germToFunctionField (hxV x) (s x), hs x, ha x]
  have hgeneric (x : U) : genericPoint X ∈ V x :=
    ((genericPoint_spec X).mem_open_set_iff (V x).isOpen).mpr
      (by simpa using (inferInstance : Nonempty (V x)))
  have hcompatible : TopCat.Presheaf.IsCompatible X.presheaf V s := by
    intro x y
    have : Nonempty ↑(V x ⊓ V y) := ⟨⟨genericPoint X, hgeneric x, hgeneric y⟩⟩
    apply X.germToFunctionField_injective (V x ⊓ V y)
    calc
      _ = X.germToFunctionField (V x) (s x) :=
        X.presheaf.germ_res_apply (Opens.infLELeft (V x) (V y)) (genericPoint X) _ (s x)
      _ = f := hsf x
      _ = X.germToFunctionField (V y) (s y) := (hsf y).symm
      _ = _ :=
        (X.presheaf.germ_res_apply (Opens.infLERight (V x) (V y))
          (genericPoint X) _ (s y)).symm
  have hcover : U ≤ iSup V := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨sU, hsU, _⟩ :=
    X.sheaf.existsUnique_gluing' V U (fun x ↦ CategoryTheory.homOfLE (hVU x)) hcover s hcompatible
  let x : U := Classical.choice hU
  refine ⟨sU, ?_⟩
  calc
    X.germToFunctionField U sU =
        X.germToFunctionField (V x) (X.presheaf.map (CategoryTheory.homOfLE (hVU x)).op sU) :=
      (X.presheaf.germ_res_apply (CategoryTheory.homOfLE (hVU x)) (genericPoint X) _ sU).symm
    _ = X.germToFunctionField (V x) (s x) := congrArg _ (hsU x)
    _ = f := hsf x

/-- A rational function represented by a unit in every stalk is a unit on the whole open. -/
theorem exists_unit_section_of_stalkwise_unit (f : X.functionField)
    (h : ∀ x : U, ∃ a : (X.presheaf.stalk x.1)ˣ,
      algebraMap (X.presheaf.stalk x.1) X.functionField
        (a : X.presheaf.stalk x.1) = f) :
    ∃ s : Γ(X, U)ˣ, X.germToFunctionField U (s : Γ(X, U)) = f := by
  obtain ⟨s, hs⟩ := exists_section_of_stalkwise_lift X U f fun x ↦ by
    obtain ⟨a, ha⟩ := h x
    exact ⟨a, ha⟩
  have hunit : IsUnit s := X.toRingedSpace.isUnit_of_isUnit_germ U s fun x hx ↦ by
    obtain ⟨a, ha⟩ := h ⟨x, hx⟩
    have hstalk : X.presheaf.germ U x hx s = (a : X.presheaf.stalk x) := by
      apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
      rw [X.algebraMap_germ_eq_germToFunctionField hx s, hs, ha]
    rw [hstalk]
    exact a.isUnit
  obtain ⟨a, rfl⟩ := hunit
  exact ⟨a, hs⟩

end AlgebraicGeometry.Scheme
