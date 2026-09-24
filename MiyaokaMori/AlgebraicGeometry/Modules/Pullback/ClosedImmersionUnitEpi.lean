import MiyaokaMori.Prelude

/-! # The unit `O_X → i_*O_Z` of a closed immersion is an epimorphism

If `i : Z → X` is a closed immersion of schemes, the canonical morphism of `O_X`-modules
`O_X → i_*O_Z` (`SheafOfModules.unitToPushforwardObjUnit`) is an epimorphism. In particular, for
an ideal sheaf `I` the sequence `0 → I.toModules → O_X → i_*O_{V(I)}` is exact on the right.

Proof: the forgetful functor `SheafOfModules.toSheaf` to sheaves of abelian groups is faithful and
so reflects epimorphisms; a morphism of sheaves of abelian groups is an epimorphism iff it is
locally surjective (`Sheaf.isLocallySurjective_iff_epi'`). Local surjectivity: for `U` and
`s ∈ Γ(Z, i⁻¹U)` and `x ∈ U`, choose an affine open `V` with `x ∈ V ⊆ U`; a closed immersion is
surjective on sections over affine opens (`Scheme.Hom.app_surjective`), so `s|_V` has a preimage.

Reference: Stacks 01QN (characterization of closed immersions).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- For a closed immersion `f`, the unit `O_X → f_*O_Z` is an epimorphism of sheaves of modules. -/
theorem epi_unitToPushforwardObjUnit_of_isClosedImmersion {Z X : Scheme.{u}} (f : Z ⟶ X)
    [IsClosedImmersion f] :
    Epi (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  have hF : (SheafOfModules.toSheaf X.ringCatSheaf).Faithful := inferInstance
  have hR : (SheafOfModules.toSheaf X.ringCatSheaf).ReflectsEpimorphisms :=
    Functor.reflectsEpimorphisms_of_faithful _
  refine (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map ?_
  refine (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} _).mp ?_
  constructor
  intro U s x hx
  obtain ⟨V, hV, hxV, hVU⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ U from hx)
  obtain ⟨t, ht⟩ := f.app_surjective V hV
    ((Z.presheaf.map (homOfLE ((Opens.map f.base).monotone hVU)).op).hom s)
  exact ⟨V, homOfLE hVU, ⟨t, ht⟩, hxV⟩

/-- The short exact sequence of an ideal sheaf, `0 → I → O_X → i_*O_{V(I)} → 0` (`I.toModules` is by
definition this kernel). -/
theorem Scheme.IdealSheafData.shortExact_kernel_unit {X : Scheme.{u}} (I : X.IdealSheafData) :
    (ShortComplex.mk
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom))
      (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)
      (kernel.condition _)).ShortExact := by
  have := epi_unitToPushforwardObjUnit_of_isClosedImmersion I.subschemeι
  exact { exact := ShortComplex.exact_kernel _ }

end AlgebraicGeometry

end
