import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.FreeModuleStalkBasisSpan
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf

/-! # Stalks of coherent sheaves are finitely generated

On a locally Noetherian scheme, the stalk of a coherent sheaf is a finitely generated module over the
local ring.

Proof (only finite type is used; neither local Noetherianity nor quasi-coherence; the definition of
Stacks 01B4 taken directly on stalks):
1. Coherent ⇒ finite type (`IsCoherent.finiteType`). `exists_epi_free_pullback_of_isFiniteType`
   (`LocalTrivializationPullback`) gives an open neighbourhood `U` of `x`, a finite index set `J` and an
   epimorphism `π : O_U^{⊕J} → (U.ι)^* M`; composing with the inverse of `restrictFunctorIsoPullback`
   gives an epimorphism `π' : O_U^{⊕J} → M|_U`.
2. An epimorphism of sheaves of modules is surjective on stalks (`FreeStalk.stalkMap_surjective_of_epi`,
   `FreeModuleStalkBasisSpan`), and `(O_U^{⊕J})_y` is spanned by finitely many germs `b_j`
   (`FreeStalk.span_b_eq_top`), so `(M|_U)_y` is a finite `O_{U,y}`-module (`Module.Finite.of_surjective`).
3. `LineGenericCoordinates.moduleRestrictStalkEquiv` gives a semilinear equivalence `(M|_U)_y ≃ M_x`
   (over the ring isomorphism `O_{U,y} ≅ O_{X,x}`); finite generation is transported along it
   (`MiyaokaMori.Module.Finite.of_semilinearEquiv`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Finite generation is transported along a semilinear equivalence (over a ring isomorphism `σ`). -/
theorem MiyaokaMori.Module.Finite.of_semilinearEquiv {R R' M M' : Type*} [CommRing R] [CommRing R']
    [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R' M']
    {σ : R →+* R'} {σ' : R' →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (S : M ≃ₛₗ[σ] M') [hM : Module.Finite R M] : Module.Finite R' M' := by
  have hσ : Function.Surjective σ := fun r => ⟨σ' r, RingHomInvPair.comp_apply_eq₂⟩
  have : RingHomSurjective σ := ⟨hσ⟩
  obtain ⟨s, hs⟩ := hM.fg_top
  refine ⟨Submodule.fg_def.mpr ⟨S '' (s : Set M), s.finite_toSet.image _, ?_⟩⟩
  have h := Submodule.map_span (S : M →ₛₗ[σ] M') (s : Set M)
  rw [hs, Submodule.map_top, LinearEquiv.range] at h
  exact h.symm

/-- The stalk of the free sheaf `O_Y^{⊕J}` (`J` finite) is a finite module. -/
theorem MiyaokaMori.FreeStalk.finite_stalk_freeM {Y : AlgebraicGeometry.Scheme.{u}} (J : Type u)
    [Finite J] (y : Y) :
    Module.Finite (Y.presheaf.stalk y) ((MiyaokaMori.FreeStalk.freeM Y J).presheaf.stalk y) :=
  ⟨Submodule.fg_def.mpr ⟨Set.range fun j => MiyaokaMori.FreeStalk.b J j y, Set.finite_range _,
    MiyaokaMori.FreeStalk.span_b_eq_top J y⟩⟩

/-- The stalk of a sheaf of modules of finite type is a finite module (no Noetherian hypothesis). -/
theorem AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isFiniteType {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) [M.IsFiniteType] (x : X) :
    Module.Finite (X.presheaf.stalk x) (M.presheaf.stalk x) := by
  obtain ⟨U, J, hJ, π, hxU, hπ⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_epi_free_pullback_of_isFiniteType M x
  let y : U := ⟨x, hxU⟩
  let := AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme (M.restrict U.ι) y
  let := AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme (MiyaokaMori.FreeStalk.freeM U.toScheme J) y
  let := AlgebraicGeometry.Scheme.Modules.moduleStalkModule X M x
  let π' : MiyaokaMori.FreeStalk.freeM U.toScheme J ⟶ M.restrict U.ι :=
    π ≫ ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).inv
  have : Epi π' := @epi_comp _ _ _ _ _ π hπ _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _))
  have hsurj := MiyaokaMori.FreeStalk.stalkMap_surjective_of_epi π' y
  have h1 : Module.Finite (U.toScheme.presheaf.stalk y) ((M.restrict U.ι).presheaf.stalk y) :=
    have := MiyaokaMori.FreeStalk.finite_stalk_freeM (Y := U.toScheme) J y
    Module.Finite.of_surjective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap U.toScheme y π') hsurj
  let σ := (U.stalkIso y).commRingCatIsoToRingEquiv
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  exact MiyaokaMori.Module.Finite.of_semilinearEquiv
    (AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleRestrictStalkEquiv X M U y)

/-- The stalk of a coherent sheaf on a locally Noetherian scheme is a finite module. -/
theorem AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (M : X.Modules) [M.IsCoherent] (x : X) :
    Module.Finite (X.presheaf.stalk x) (M.stalk x) := by
  have : M.IsFiniteType := AlgebraicGeometry.Scheme.Modules.IsCoherent.finiteType
  exact AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isFiniteType M x

end
