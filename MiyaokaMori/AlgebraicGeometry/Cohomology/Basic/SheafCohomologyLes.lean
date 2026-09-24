import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafHasextInstance
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesExactIffLocallyLift

/-! # Sheaf cohomology as `Ext`, and short exact sequences of modules

Bridge lemmas: the unfolding `Sheaf.H F n = Ext(constant sheaf ℤ, F, n)`, and the transport of a
short exact sequence of `O_X`-modules to a short exact sequence of abelian sheaves.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `Sheaf.H F n` is by definition `Ext^n` from the constant sheaf `ℤ` to `F`. -/
theorem bridge_sheafCohomology_eq_ext {C : Type u} [CategoryTheory.Category.{v} C]
    {J : CategoryTheory.GrothendieckTopology C}
    [CategoryTheory.HasSheafify J AddCommGrpCat.{w}]
    [CategoryTheory.HasExt.{v'} (CategoryTheory.Sheaf J AddCommGrpCat.{w})]
    (F : CategoryTheory.Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    CategoryTheory.Sheaf.H F n =
      CategoryTheory.Abelian.Ext
        ((CategoryTheory.constantSheaf J AddCommGrpCat.{w}).obj
          (AddCommGrpCat.of (ULift ℤ))) F n :=
  rfl

/-- A short exact sequence of `O_X`-modules stays short exact after forgetting to abelian sheaves.
The short complex is taken in `SheafOfModules X.ringCatSheaf` (definitionally equal to `X.Modules`,
but the `PreservesZeroMorphisms` instance of `toSheaf` is attached to `SheafOfModules`).

Proof: (a) mono: `SheafOfModules.toSheaf` preserves finite limits, hence monomorphisms;
(b) epi: an epimorphism of `O_X`-modules is locally surjective on sections (`locSurj_of_epi`),
and local surjectivity implies epi for abelian sheaves (`TopCat.Sheaf.isLocallySurjective_iff_epi`);
the two notions of local surjectivity agree (`locSurj_iff`);
(c) exactness: `S.f` is the kernel of `S.g`, and a functor preserving finite limits preserves kernels
(`ShortComplex.Exact.map_of_mono_of_preservesKernel`). -/
theorem bridge_shortExact_toSheaf {X : AlgebraicGeometry.Scheme.{u}}
    (S : CategoryTheory.ShortComplex (SheafOfModules.{u} X.ringCatSheaf)) (hS : S.ShortExact) :
    (S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)).ShortExact := by
  have hmono : CategoryTheory.Mono S.f := hS.mono_f
  have hepiM : CategoryTheory.Mono (C := X.Modules) S.f := hS.mono_f
  have hepiG : CategoryTheory.Epi (C := X.Modules) S.g := hS.epi_g
  have hloc : ModulesLocLiftAux.LocSurj (X := X) (M := S.X₂) (N := S.X₃) S.g :=
    @ModulesLocLiftAux.locSurj_of_epi X S.X₂ S.X₃ S.g hepiG
  have hepi' : CategoryTheory.Epi ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map S.g) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
      ((ModulesLocLiftAux.locSurj_iff (X := X) (M := S.X₂) (N := S.X₃) S.g).mp hloc)
  have hmono' : CategoryTheory.Mono ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map S.f) :=
    (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map_mono S.f
  exact
    { exact := CategoryTheory.ShortComplex.Exact.map_of_mono_of_preservesKernel hS.exact
        (SheafOfModules.toSheaf.{u} X.ringCatSheaf) hmono inferInstance
      mono_f := hmono'
      epi_g := hepi' }

end
