import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.AnnihilatorIdealSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.AssociatedPointsLocalCriterion
import MiyaokaMori.RingTheory.Localization.AssociatedPrimesComapSurjective
import MiyaokaMori.RingTheory.Localization.Stacks02m8
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentStalkFinite
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesFiniteTypeInstances
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01xz
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineGenericCoordinates

/-! # The annihilator subscheme has no embedded points

Step 4 of Stacks 02OM: if `F` is coherent without embedded associated points on a
locally Noetherian `X` and `I = Ann(F)` (`IdealSheafData.IsAnnihilatorOf`), then the closed subscheme
`Z = V(I)` has no embedded points.

Proof. `Z` is locally Noetherian (`LocallyOfFiniteType.isLocallyNoetherian`) and `O_Z` is coherent, so by the
local criterion (`hasNoEmbeddedAssociatedPoints_iff_forall_stalk`) it suffices that each local ring
`B = O_{Z,z}` has no embedded primes as a module over itself. Let `A = O_{X,ι z}`, `φ : A → B` the stalk map
(surjective; kernel `K = Ann_A(F_{ι z})` by `IsAnnihilatorOf.ker_stalkMap_subschemeι_eq`). Then
`B ≅ A ⧸ K` as `A`-algebras (`Ideal.quotientKerAlgEquivOfSurjective`), and "no embedded primes" can be
tested over `A` instead of over `B` or `A ⧸ K` (`Module.hasNoEmbeddedPrimes_iff_of_surjective`,
`LinearEquiv.AssociatedPrimes.eq`). Finally Stacks 02M8 (`Module.hasNoEmbeddedPrimes_quotient_annihilator`)
gives that `A ⧸ Ann_A(M)` has no embedded primes, for `M = F_{ι z}` a finite module over the Noetherian
local ring `A` without embedded primes (local criterion on `X`).

Source: Stacks 02OM, 02M8.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- "No embedded primes" transports along a linear equivalence. -/
theorem Module.HasNoEmbeddedPrimes.of_linearEquiv {R M N : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (h : Module.HasNoEmbeddedPrimes R M) :
    Module.HasNoEmbeddedPrimes R N := by
  unfold Module.HasNoEmbeddedPrimes at h ⊢
  rwa [← LinearEquiv.AssociatedPrimes.eq e]

/-- "No embedded primes" of a ring (as a module over itself) transports along a ring equivalence. -/
theorem Module.HasNoEmbeddedPrimes.of_ringEquiv {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : Module.HasNoEmbeddedPrimes R R) : Module.HasNoEmbeddedPrimes S S := by
  let _ : Module R S := Module.compHom S e.toRingHom
  have hsmul : ∀ (r : R) (s : S), r • s = e.toRingHom r • s := fun _ _ => rfl
  rw [← Module.hasNoEmbeddedPrimes_iff_of_surjective e.toRingHom e.surjective hsmul]
  refine Module.HasNoEmbeddedPrimes.of_linearEquiv (R := R) { e.toAddEquiv with map_smul' := ?_ } h
  intro r x
  exact map_mul e r x

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **The annihilator subscheme has no embedded points** (Stacks 02OM, step 4). -/
theorem IsAnnihilatorOf.subscheme_hasNoEmbeddedPoints [AlgebraicGeometry.IsLocallyNoetherian X]
    {I : X.IdealSheafData} {F : X.Modules} [F.IsCoherent] (hI : I.IsAnnihilatorOf F)
    (hF : F.HasNoEmbeddedAssociatedPoints) : I.subscheme.HasNoEmbeddedPoints := by
  have : AlgebraicGeometry.IsLocallyNoetherian I.subscheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  have : AlgebraicGeometry.Scheme.Modules.IsCoherent (X := I.subscheme)
      (SheafOfModules.unit I.subscheme.ringCatSheaf) :=
    AlgebraicGeometry.Scheme.Modules.isCoherent_of_isLocallyFree (X := I.subscheme) _
  show AlgebraicGeometry.Scheme.Modules.HasNoEmbeddedAssociatedPoints (X := I.subscheme)
    (SheafOfModules.unit I.subscheme.ringCatSheaf)
  rw [AlgebraicGeometry.Scheme.Modules.hasNoEmbeddedAssociatedPoints_iff_forall_stalk (X := I.subscheme)
    (SheafOfModules.unit I.subscheme.ringCatSheaf)]
  intro z
  -- the stalk of the structure module is the local ring `B = O_{Z,z}`
  let _ := AlgebraicGeometry.Scheme.Modules.moduleStalkModule I.subscheme (SheafOfModules.unit I.subscheme.ringCatSheaf) z
  refine Module.HasNoEmbeddedPrimes.of_linearEquiv
    (AlgebraicGeometry.Divisors.LineGenericCoordinates.unitStalkLinearEquiv I.subscheme z).symm ?_
  -- notation: `A = O_{X,x}`, `φ : A → B` surjective with kernel `Ann_A(F_x)`
  set x : X := I.subschemeι.base z with hxdef
  set φ : X.presheaf.stalk x →+* I.subscheme.presheaf.stalk z := (I.subschemeι.stalkMap z).hom with hφdef
  have hφ : Function.Surjective φ := I.subschemeι.stalkMap_surjective z
  have hkerφ : RingHom.ker φ = Module.annihilator (X.presheaf.stalk x) (F.stalk x) :=
    hI.ker_stalkMap_subschemeι_eq z
  -- `A ⧸ Ann_A(F_x) ≃+* B`
  let e : ((X.presheaf.stalk x) ⧸ Module.annihilator (X.presheaf.stalk x) (F.stalk x)) ≃+*
      I.subscheme.presheaf.stalk z :=
    (Ideal.quotEquivOfEq hkerφ.symm).trans (RingHom.quotientKerEquivOfSurjective hφ)
  -- Stacks 02M8 on the stalk `F_x`
  have : Module.Finite (X.presheaf.stalk x) (F.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent F x
  have hM : Module.HasNoEmbeddedPrimes (X.presheaf.stalk x) (F.stalk x) :=
    (AlgebraicGeometry.Scheme.Modules.hasNoEmbeddedAssociatedPoints_iff_forall_stalk F).mp hF x
  exact Module.HasNoEmbeddedPrimes.of_ringEquiv e
    (Module.hasNoEmbeddedPrimes_quotient_annihilator (X.presheaf.stalk x) (F.stalk x) hM)

end AlgebraicGeometry.Scheme.IdealSheafData

end
