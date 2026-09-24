import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.FreeModuleStalkBasisSpan
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineGenericCoordinates

/-! # The rank at a stalk from a local trivialization

If `E|_U ≅ O_U^{(I)}` with `I` finite, then for `x ∈ U` the rank of `E` at `x` is `#I`; the rank at a
point depends only on the isomorphism class on an open neighbourhood of the point.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A semilinear equivalence sends bases to bases. -/
theorem MiyaokaMori.basis_of_semilinearEquiv {R R' M M' ι : Type*} [CommRing R] [CommRing R']
    [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R' M']
    {σ : R →+* R'} {σ' : R' →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (S : M ≃ₛₗ[σ] M') (b : Module.Basis ι R M) : Nonempty (Module.Basis ι R' M') := by
  have hσ : Function.Surjective σ := fun r => ⟨σ' r, RingHomInvPair.comp_apply_eq₂⟩
  have : RingHomSurjective σ := ⟨hσ⟩
  have hli : LinearIndependent R' ((S : M →ₛₗ[σ] M').toAddMonoidHom ∘ b) :=
    b.linearIndependent.map_of_surjective_injective σ (S : M →ₛₗ[σ] M').toAddMonoidHom hσ
      (fun m hm => S.map_eq_zero_iff.mp hm) (fun r m => map_smulₛₗ S r m)
  refine ⟨Module.Basis.mk hli ?_⟩
  have : Set.range ((S : M →ₛₗ[σ] M').toAddMonoidHom ∘ b) = (S : M →ₛₗ[σ] M') '' Set.range b :=
    Set.range_comp _ _
  rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_top, LinearEquiv.range]

/-- The stalk at `y` of the free sheaf `O_Y^{(I)}` (`I` finite) has a basis indexed by `I`. -/
private theorem rankLocalIso.free_stalk_basis {Y : AlgebraicGeometry.Scheme.{u}} (I : Type u) [Finite I] (y : Y) :
    Nonempty (Module.Basis I (Y.presheaf.stalk y)
      ((MiyaokaMori.FreeStalk.freeM Y I).presheaf.stalk y)) :=
  ⟨Module.Basis.mk (MiyaokaMori.FreeStalk.linearIndependent_b I y)
    (MiyaokaMori.FreeStalk.span_b_eq_top I y).ge⟩

theorem AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free {X : AlgebraicGeometry.Scheme.{u}}
    (E : X.Modules) (U : X.Opens) (I : Type u) [Fintype I]
    (e : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj E ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
    (x : X) (hx : x ∈ U) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk E x = Fintype.card I := by
  let y : U := ⟨x, hx⟩
  -- (E|_U)_y ≅ (O_U^{(I)})_y, O_{U,y}-linear
  let e' : E.restrict U.ι ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) I :=
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app E ≪≫ e
  let := AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme (E.restrict U.ι) y
  let := AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme (MiyaokaMori.FreeStalk.freeM U.toScheme I) y
  let := AlgebraicGeometry.Scheme.Modules.moduleStalkModule X E x
  let L := ((AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme y).mapIso e').toLinearEquiv
  obtain ⟨b0⟩ := rankLocalIso.free_stalk_basis (Y := U.toScheme) I y
  let b1 := b0.map L.symm
  -- move to E_x (a semilinear equivalence over O_{U,y} ≅ O_{X,x})
  let σ := (U.stalkIso y).commRingCatIsoToRingEquiv
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  obtain ⟨b2⟩ := MiyaokaMori.basis_of_semilinearEquiv (AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleRestrictStalkEquiv X E U y) b1
  let := (X.residue x).hom.toAlgebra
  have hfree : Module.Free (X.presheaf.stalk x) (E.presheaf.stalk x) := Module.Free.of_basis b2
  change Module.finrank (X.residueField x) (TensorProduct (X.presheaf.stalk x) (X.residueField x) (E.presheaf.stalk x)) = _
  rw [Module.finrank_baseChange, Module.finrank_eq_card_basis b2]

end
