import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Exactness after forgetting the module structure

The existing functor `SheafOfModules.toSheaf` sends a sheaf of modules on a
scheme to its underlying abelian sheaf. It preserves finite limits. To obtain
finite colimits as well, precompose with module sheafification and use its
comparison with abelian sheafification. The module-sheafification adjunction is
reflective, so preservation of colimits descends from that composite.

Consequently an actual short exact sequence of modules gives a short exact
sequence of the same underlying abelian sheaves. This is the comparison needed
to apply `Sheaf.H` to the principal-parts restriction sequence of the paper. Short exactness of
that restriction sequence and vanishing of its kernel's first cohomology are
separate obligations. No new sheaf or cohomology object is introduced.

Reference: Stacks Project, Modules, the abelian category of sheaves of modules;
kernels are computed on sections and cokernels by sheafification.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable instance module_toSheaf_preservesZeroMorphisms (X : Scheme.{u}) :
    (SheafOfModules.toSheaf.{u} X.ringCatSheaf).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

private theorem module_toSheaf_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf) := by
  constructor
  intro J _ _
  apply (Adjunction.preservesColimitsOfShape_iff
    (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj))
    (SheafOfModules.toSheaf.{u} X.ringCatSheaf) J).mpr
  exact preservesColimitsOfShape_of_natIso
    (PresheafOfModules.sheafificationCompToSheaf.{u} (𝟙 X.ringCatSheaf.obj)).symm

/-- Forgetting the module structure preserves the actual short exact sequence of sheaves. -/
theorem module_shortExact_toSheaf (X : Scheme.{u})
    {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (@ShortComplex.map _ _ _ _ _ _ S (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
      (module_toSheaf_preservesZeroMorphisms X)).ShortExact := by
  have hlim : PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf) := inferInstance
  exact @ShortComplex.ShortExact.map_of_exact _ _ _ _ _ _ S hS
    (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
    (module_toSheaf_preservesZeroMorphisms X) hlim
    (module_toSheaf_preservesFiniteColimits X)

end AlgebraicGeometry.Scheme.Modules
