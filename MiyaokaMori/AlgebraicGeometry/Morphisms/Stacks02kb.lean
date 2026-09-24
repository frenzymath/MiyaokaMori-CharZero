import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.AffinePushforwardQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeOfFreeAffineSections

/-! # Finite flat morphisms are finite locally free

Stacks Project, Tag 02KB: `f` finite, flat and locally of finite presentation ⇔ `f` finite locally free;
over a locally Noetherian `S`, finite and flat suffices (`f_*O_X` is a locally free `O_S`-module of
finite rank).

Source: Stacks 02KB (morphisms-lemma-finite-flat), (3) ⇒ (1) branch, with the Noetherian remark
(finite over Noetherian ⇒ finitely presented, Stacks 0564 / Mathlib `Module.finitePresentation_of_finite`).

Proof:
1. Affine reduction: `f` finite ⇒ affine, so for an affine open `V ⊆ S` the ring map
   `R := Γ(S, V) → A := Γ(X, f⁻¹V)` is `f.app V`; `A` is a finite `R`-module (`IsFinite.finite_app`)
   and flat (`Flat.flat_appLE` at `(V, f⁻¹V, le_rfl)`, which is `f.app V` by `appLE_eq_app`).
2. `S` locally Noetherian ⇒ `R` Noetherian (`IsLocallyNoetherian.component_noetherian`), so `A` is
   finitely presented (`Module.finitePresentation_of_finite`). This is the second theorem.
3. For `s ∈ V` with prime `p := hV.primeIdealOf s`, `A_p` is finite flat over the local ring `R_p`,
   hence free (`Module.free_of_flat_of_isLocalRing`); by finite presentation freeness spreads to a basic
   open: `∃ r ∉ p`, `A[1/r]` free over `R[1/r]` (`Module.FinitePresentation.exists_free_localizedModule_powers`).
4. Identification (`free_pushforward_unit_basicOpen`): `Γ(S, D(r)) = R[1/r]` and
   `Γ(X, f⁻¹D(r)) = Γ(X, D(f^♯r)) = A[1/f^♯ r]` (`isLocalization_of_eq_basicOpen`, `preimage_basicOpen`);
   the pushforward module structure is restriction of scalars along `f.app D(r)`, compatible with
   `f.app V` by naturality; freeness transfers along the abstract localizations
   (`Module.Free.of_isLocalization_away`, generalizing Mathlib's `Module.mem_freeLocus_of_isLocalization`).
5. `f_*O_X` is quasi-coherent (`AffinePushforwardQuasicoherent.lean`), every `s` has the affine
   `D(r) ∋ s` with finite free sections (finiteness from `IsFinite.finite_app` on `D(r)`), so
   `LocallyFreeOfFreeAffineSections.lean` gives `IsLocallyFree`. This is the first theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry

noncomputable section

open scoped AlgebraicGeometry

section Algebra

variable {R : Type*} [CommRing R] (S : Submonoid R) {M : Type*} [AddCommGroup M] [Module R M]

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- Freeness transfers from the model `LocalizedModule S M` over `Localization S` to any
abstract localization `Mₛ` over `Rₛ` (generalizing Mathlib's `Module.mem_freeLocus_of_isLocalization`
from `p.primeCompl` to an arbitrary submonoid). -/
theorem Module.Free.of_isLocalizedModule_of_free_localizedModule
    (Rₛ Mₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
    [AddCommGroup Mₛ] [Module R Mₛ] (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f]
    [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    [Module.Free (Localization S) (LocalizedModule S M)] : Module.Free Rₛ Mₛ := by
  set e := (IsLocalization.algEquiv S (Localization S) Rₛ).toRingEquiv
  refine (Module.Free.iff_of_equiv (σ := (e : Localization S →+* Rₛ))
    (M := LocalizedModule S M) (M' := Mₛ) ?_).mp inferInstance
  refine { __ := IsLocalizedModule.iso S f, map_smul' := ?_ }
  intro r x
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq S r
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).1
  simp [e, ← map_smul, ← smul_assoc]

/-- Algebra form: `A` an `R`-algebra, `Rₛ = R[1/r]`, `Aₛ = A[1/r]` compatibly; if the model
`A[1/r]` is free over `R[1/r]`, so is `Aₛ` over `Rₛ`. -/
theorem Module.Free.of_isLocalization_away
    {A Rₛ Aₛ : Type*} [CommRing A] [Algebra R A] [CommRing Rₛ] [Algebra R Rₛ]
    [CommRing Aₛ] [Algebra A Aₛ] [Algebra R Aₛ] [Algebra Rₛ Aₛ]
    [IsScalarTower R A Aₛ] [IsScalarTower R Rₛ Aₛ] (r : R)
    [IsLocalization.Away r Rₛ] [IsLocalization.Away (algebraMap R A r) Aₛ]
    [Module.Free (Localization.Away r) (LocalizedModule.Away r A)] : Module.Free Rₛ Aₛ := by
  have : IsLocalization (Algebra.algebraMapSubmonoid A (.powers r)) Aₛ := by
    rwa [Algebra.algebraMapSubmonoid_powers]
  have : IsLocalizedModule (.powers r) (IsScalarTower.toAlgHom R A Aₛ).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr this
  exact Module.Free.of_isLocalizedModule_of_free_localizedModule (.powers r) Rₛ Aₛ
    (IsScalarTower.toAlgHom R A Aₛ).toLinearMap

end Algebra

section Geometry

/-- Sections of `f_*O_X` over the basic open `D(r) ⊆ V` (`V` affine, `f` affine) form a free
`Γ(S, D(r))`-module as soon as the model localization `Γ(X, f⁻¹V)[1/r]` is free over
`Γ(S, V)[1/r]`: `Γ(S, D(r))` is `Γ(S,V)[1/r]` (`IsAffineOpen.isLocalization_of_eq_basicOpen`),
`f⁻¹D(r) = D(f^♯ r)` (`Scheme.preimage_basicOpen`) so `Γ(X, f⁻¹D(r))` is `Γ(X, f⁻¹V)[1/f^♯ r]`,
and the `Γ(S, D(r))`-action on the pushforward is restriction of scalars along `f.app D(r)`
(compatible with `f.app V` by naturality). -/
theorem AlgebraicGeometry.Scheme.Modules.free_pushforward_unit_basicOpen
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] {V : S.Opens} (hV : IsAffineOpen V)
    (r : Γ(S, V))
    (hfree : letI := (f.app V).hom.toAlgebra
      Module.Free (Localization.Away r) (LocalizedModule.Away r Γ(X, f ⁻¹ᵁ V))) :
    Module.Free Γ(S, S.basicOpen r)
      Γ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf), S.basicOpen r) := by
  let iS : S.basicOpen r ⟶ V := homOfLE (S.basicOpen_le r)
  let iX : f ⁻¹ᵁ S.basicOpen r ⟶ f ⁻¹ᵁ V := (Opens.map f.base).map iS
  let : Algebra Γ(S, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(S, S.basicOpen r) := (S.presheaf.map iS.op).hom.toAlgebra
  let : Algebra Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ S.basicOpen r) := (X.presheaf.map iX.op).hom.toAlgebra
  let : Algebra Γ(S, S.basicOpen r) Γ(X, f ⁻¹ᵁ S.basicOpen r) :=
    (f.app (S.basicOpen r)).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(X, f ⁻¹ᵁ S.basicOpen r) :=
    (f.app V ≫ X.presheaf.map iX.op).hom.toAlgebra
  have : IsScalarTower Γ(S, V) Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ S.basicOpen r) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  have : IsScalarTower Γ(S, V) Γ(S, S.basicOpen r) Γ(X, f ⁻¹ᵁ S.basicOpen r) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      have h := ConcreteCategory.congr_hom (f.naturality iS.op) x
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
      exact h.symm
  have : IsLocalization.Away r Γ(S, S.basicOpen r) :=
    hV.isLocalization_of_eq_basicOpen r iS rfl
  have : IsLocalization.Away (algebraMap Γ(S, V) Γ(X, f ⁻¹ᵁ V) r) Γ(X, f ⁻¹ᵁ S.basicOpen r) :=
    (hV.preimage f).isLocalization_of_eq_basicOpen (f.app V r) iX (Scheme.preimage_basicOpen f r)
  exact Module.Free.of_isLocalization_away (A := Γ(X, f ⁻¹ᵁ V)) (Aₛ := Γ(X, f ⁻¹ᵁ S.basicOpen r)) r

end Geometry

/-- Stacks 02KB, (3) ⇒ (1) in the locally Noetherian case: for `f` finite and flat over a locally
Noetherian `S`, `f_*O_X` is a locally free `O_S`-module. See the module docstring for the proof. -/
theorem AlgebraicGeometry.isLocallyFree_pushforward_of_isFinite_of_flat
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.IsFinite f]
    [AlgebraicGeometry.Flat f] [AlgebraicGeometry.IsLocallyNoetherian S] :
    ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit X.ringCatSheaf)).IsLocallyFree := by
  have := isQuasicoherent_pushforward_one_of_isAffineHom f
  refine Scheme.Modules.isLocallyFree_of_free_affine_sections _ fun s => ?_
  obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ s)
  let : Algebra Γ(S, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : Module.Finite Γ(S, V) Γ(X, f ⁻¹ᵁ V) := IsFinite.finite_app f V hV
  have : Module.Flat Γ(S, V) Γ(X, f ⁻¹ᵁ V) := by
    have := Flat.flat_appLE f hV (hV.preimage f) le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  have : Module.FinitePresentation Γ(S, V) Γ(X, f ⁻¹ᵁ V) := Module.finitePresentation_of_finite _ _
  let p : PrimeSpectrum Γ(S, V) := hV.primeIdealOf ⟨s, hsV⟩
  have : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl Γ(X, f ⁻¹ᵁ V)) := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl Γ(X, f ⁻¹ᵁ V))
    (Localization.AtPrime p.asIdeal)
  refine ⟨S.basicOpen r, hV.basicOpen r, ?_, ?_, ?_⟩
  · have hp : p ∈ hV.fromSpec ⁻¹ᵁ S.basicOpen r := by
      rw [hV.fromSpec_preimage_basicOpen]; exact hr
    have hp' : hV.fromSpec p ∈ S.basicOpen r := hp
    rwa [hV.fromSpec_primeIdealOf ⟨s, hsV⟩] at hp'
  · exact Scheme.Modules.free_pushforward_unit_basicOpen f hV r hfree
  · exact IsFinite.finite_app f (S.basicOpen r) (hV.basicOpen r)



/-- Affine-local form (used in Stacks 02RU to define the degree `d`: the pointwise rank of a finitely
presented flat module is locally constant).

Stacks 02KB, Noetherian remark: for `V ⊆ S` affine, `Γ(X, f⁻¹V)` is a finitely presented flat
`Γ(S, V)`-module via `f.app V` (finite by `IsFinite.finite_app`, flat by `Flat.flat_appLE`, finitely
presented because `Γ(S, V)` is Noetherian, `IsLocallyNoetherian.component_noetherian`). -/
theorem AlgebraicGeometry.IsFinite.finitePresentation_flat_app_of_flat
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.IsFinite f]
    [AlgebraicGeometry.Flat f] [AlgebraicGeometry.IsLocallyNoetherian S]
    {V : S.Opens} (hV : AlgebraicGeometry.IsAffineOpen V) :
    letI := (f.app V).hom.toAlgebra
    Module.FinitePresentation Γ(S, V) Γ(X, f ⁻¹ᵁ V) ∧ Module.Flat Γ(S, V) Γ(X, f ⁻¹ᵁ V) := by
  let _ : Algebra Γ(S, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : Module.Finite Γ(S, V) Γ(X, f ⁻¹ᵁ V) := IsFinite.finite_app f V hV
  have : Module.Flat Γ(S, V) Γ(X, f ⁻¹ᵁ V) := by
    have := Flat.flat_appLE f hV (hV.preimage f) le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  exact ⟨Module.finitePresentation_of_finite _ _, inferInstance⟩

end
