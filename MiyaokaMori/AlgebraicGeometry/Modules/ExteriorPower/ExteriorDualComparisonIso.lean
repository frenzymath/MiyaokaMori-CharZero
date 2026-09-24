import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorDualComparisonNaturality
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorDualComparisonIsoRestrict
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorDualComparisonIsoFree

/-!
# The exterior-dual comparison is invertible for finite locally free modules

For a module sheaf that is locally free of finite rank `r`, the canonical comparison
`exteriorDualComparison M n : ⋀ⁿ(M^∨) ⟶ (⋀ⁿ M)^∨` is an isomorphism, for every exterior
degree `n` (including `0` and `n > r`) and without any hypothesis on the characteristic.

The assembly proved here is:
* invertibility is local (`moduleHom_isIso_of_locally_isIso`);
* on a frame neighbourhood the restricted comparison is, up to the exterior-power and dual
  restriction isomorphisms, the comparison of the restriction
  (`exteriorDualComparison_restrict_isIso`, proved in `ExteriorDualComparisonIsoRestrict`);
* the comparison is natural in module isomorphisms
  (`ExteriorDualComparisonNaturality.isIso_iff`), reducing to the free module;
* the free case (`exteriorDualComparison_free_isIso`, proved in `ExteriorDualComparisonIsoFree`
  for every module sheaf with compatible section bases), whose algebraic core is
  `exteriorPowerPairingDual_bijective` in `ExteriorPowerDualPairing`.

Sources: Stacks Project, `modules.tex`,
Internal Hom and Symmetric and exterior powers.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} (M : X.Modules) (n : ℕ)

/-- Restricting the comparison to an open subscheme gives an invertible morphism as soon as
the comparison of the restricted module is invertible. -/
theorem exteriorDualComparison_restrict_isIso (U : X.Opens)
    (h : IsIso (exteriorDualComparison (M.restrict U.ι) n)) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (exteriorDualComparison M n)) :=
  ExteriorDualComparisonRestrict.restrict_isIso M n U h

/-- The comparison is invertible for a free module sheaf of finite rank. -/
theorem exteriorDualComparison_free_isIso (X : Scheme.{u}) (r n : ℕ) :
    IsIso (exteriorDualComparison
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))) n) :=
  exteriorDualComparison_isIso_of_isFrameOn (freeIsFrameOn X r) n

/-- The exterior-dual comparison is invertible for every module sheaf admitting local frames
of a fixed finite rank. -/
theorem exteriorDualComparison_isIso_of_local_frames (r : ℕ)
    (hM : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (M.restrict U.ι ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))) :
    IsIso (exteriorDualComparison M n) := by
  refine moduleHom_isIso_of_locally_isIso _ fun x ↦ ?_
  obtain ⟨U, hxU, ⟨e⟩⟩ := hM x
  exact ⟨U, hxU, exteriorDualComparison_restrict_isIso M n U
    ((ExteriorDualComparisonNaturality.isIso_iff e n).mpr
      (exteriorDualComparison_free_isIso U.toScheme r n))⟩

end AlgebraicGeometry.Scheme.Modules
