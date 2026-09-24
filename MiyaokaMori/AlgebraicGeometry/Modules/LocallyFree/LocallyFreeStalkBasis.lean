import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModuleUnit
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.FreeModuleStalkBasisSpan
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank

/-! # The stalk of a locally free module at a point of rank `n > 0`

**The stalk of a locally free module at a point of rank `n > 0` has a basis indexed by `Fin n`.**
Helper for `LocallyFreeOnArtinianIsFree`: `E` locally free (Mathlib `SheafOfModules.IsLocallyFree`,
any rank), `x` a point with `rankAtStalk E x = n`, `n > 0`; then `E_x` is a free `O_{X,x}`-module with a basis
indexed by `ULift (Fin n)`.

Proof: a local trivialisation `E|_U ≅ O_U^{(I)}` near `x` (`exists_pullback_iso_free_of_isLocallyFree`).
If `I` were infinite, `rankAtStalk E x = 0` (the coordinate projections give `#S` linearly independent
vectors in `κ(x) ⊗ E_x` for every finite `S ⊆ I`, so the fibre is infinite-dimensional and `finrank = 0`);
this is the argument of `ModulesPullbackRankInfinite.rank_zero_of_restrict_iso_free`
(`ModulesPullbackRank`), which is `private` there and is therefore repeated here.
So `I` is finite, `rankAtStalk E x = #I` (`rankAtStalk_of_restrict_iso_free`), hence `#I = n`, and the
basis `(germ e_i)_i` of `(O_U^{(I)})_x` (`FreeStalk.linearIndependent_b`, `FreeStalk.span_b_eq_top`)
transported along the stalk iso `E_x ≅ (E|_U)_x ≅ (O_U^{(I)})_x` (`moduleRestrictStalkEquiv`,
`basis_of_semilinearEquiv`) is a basis of `E_x` indexed by `I ≃ ULift (Fin n)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace MiyaokaMori.StalkBasisOfRank

open Classical

/-- Coordinate projections force the standard residue-fibre family to be linearly independent
(copy of `ModulesPullbackRankInfinite.fiber_standard_li`). -/
private theorem fiber_standard_li {A K M I : Type*} [CommRing A] [Field K]
    [AddCommGroup M] [Module A M] [Algebra A K]
    (b : I → M) (p : I → (M →ₗ[A] A))
    (hp : ∀ i j, p i (b j) = if j = i then 1 else 0) :
    LinearIndependent K (fun i => (TensorProduct.mk A K M) 1 (b i)) := by
  let q : I → (M →ₗ[A] K) := fun i => (Algebra.linearMap A K).comp (p i)
  let L : I → ((K ⊗[A] M) →ₗ[K] K) := fun i =>
    TensorProduct.AlgebraTensorModule.lift (A := K)
      (LinearMap.smulRight (LinearMap.id : K →ₗ[K] K) (q i))
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congrArg (L i) hg
  rw [map_sum] at h
  simpa [L, q, hp, hi] using h

private abbrev freeM (Y : AlgebraicGeometry.Scheme.{u}) (I : Type u) : Y.Modules :=
  MiyaokaMori.FreeStalk.freeM Y I

private abbrev freeStalk (Y : AlgebraicGeometry.Scheme.{u}) (I : Type u) (y : Y) : Type u :=
  (freeM Y I).presheaf.stalk y

private abbrev astalk (Y : AlgebraicGeometry.Scheme.{u}) (y : Y) : Type u :=
  Y.presheaf.stalk y

private instance free_stalk_module (Y : AlgebraicGeometry.Scheme.{u}) (I : Type u) (y : Y) :
    Module (astalk Y y) (freeStalk Y I y) :=
  AlgebraicGeometry.Scheme.Modules.moduleStalkModule Y (freeM Y I) y

private instance unit_stalk_module (Y : AlgebraicGeometry.Scheme.{u}) (y : Y) :
    Module (astalk Y y) ((AlgebraicGeometry.Scheme.Modules.unitModule Y).presheaf.stalk y) :=
  AlgebraicGeometry.Scheme.Modules.moduleStalkModule Y (AlgebraicGeometry.Scheme.Modules.unitModule Y) y

private def freeProj (Y : AlgebraicGeometry.Scheme.{u}) (I : Type u) (y : Y) (i : I) :
    freeStalk Y I y →ₗ[astalk Y y] astalk Y y :=
  (AlgebraicGeometry.Divisors.LineGenericCoordinates.unitStalkLinearEquiv Y y).toLinearMap.comp
    (AlgebraicGeometry.Scheme.Modules.moduleStalkMap Y y (MiyaokaMori.FreeStalk.proj Y I i))

private lemma freeProj_basis (Y : AlgebraicGeometry.Scheme.{u}) (I : Type u) (y : Y) (i j : I) :
    freeProj Y I y i (MiyaokaMori.FreeStalk.b I j y) = if j = i then 1 else 0 := by
  rw [freeProj, LinearMap.comp_apply, MiyaokaMori.FreeStalk.stalkMap_proj_b]
  split_ifs with h
  · subst h
    have hu :
        (AlgebraicGeometry.Divisors.LineGenericCoordinates.unitStalkLinearEquiv Y y)
            ((ConcreteCategory.hom
              ((AlgebraicGeometry.Scheme.Modules.unitModule Y).presheaf.germ ⊤ y trivial))
              (MiyaokaMori.FreeStalk.uSec ⊤ 1)) = 1 := by
      simpa [AlgebraicGeometry.Scheme.Modules.unitModule, MiyaokaMori.FreeStalk.uSec] using
        (AlgebraicGeometry.Divisors.LineGenericCoordinates.unitStalkLinearEquiv_germ Y y ⊤ trivial (1 : Γ(Y, ⊤)))
    exact hu
  · simp

private def transportedProj
    {A B M N : Type*} [CommRing A] [CommRing B]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
    (σ : A ≃+* B)
    [RingHomInvPair (σ : A →+* B) (σ.symm : B →+* A)]
    [RingHomInvPair (σ.symm : B →+* A) (σ : A →+* B)]
    (S : M ≃ₛₗ[(σ : A →+* B)] N) (p : M →ₗ[A] A) :
    N →ₗ[B] B := by
  let psl : M →ₛₗ[(RingHom.id A)] A := p
  let q : N →ₛₗ[(σ.symm : B →+* A)] A := psl.comp S.symm.toLinearMap
  exact LinearMap.mk
    { toFun := fun n => σ (q n)
      map_add' := by intro x y; simp }
    (by
      intro b n
      dsimp [q, psl]
      rw [map_smulₛₗ, map_smulₛₗ]
      simp [smul_eq_mul])

private lemma transportedProj_apply
    {A B M N : Type*} [CommRing A] [CommRing B]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
    (σ : A ≃+* B)
    [RingHomInvPair (σ : A →+* B) (σ.symm : B →+* A)]
    [RingHomInvPair (σ.symm : B →+* A) (σ : A →+* B)]
    (S : M ≃ₛₗ[(σ : A →+* B)] N) (p : M →ₗ[A] A) (m : M) :
    transportedProj σ S p (S m) = σ (p m) := by
  simp [transportedProj]

/-- The basis of `(O_U^{(I)})_y` given by the germs of the standard sections (`I` finite). -/
private theorem free_stalk_basis {Y : AlgebraicGeometry.Scheme.{u}} (I : Type u) [Finite I] (y : Y) :
    Nonempty (Module.Basis I (Y.presheaf.stalk y) ((MiyaokaMori.FreeStalk.freeM Y I).presheaf.stalk y)) :=
  ⟨Module.Basis.mk (MiyaokaMori.FreeStalk.linearIndependent_b I y)
    (MiyaokaMori.FreeStalk.span_b_eq_top I y).ge⟩

/-- Infinite trivialising index set ⇒ `rankAtStalk = 0`
(copy of `ModulesPullbackRankInfinite.rank_zero_of_restrict_iso_free`). -/
private theorem rank_zero_of_restrict_iso_free {X : AlgebraicGeometry.Scheme.{u}}
    (E : X.Modules) (U : X.Opens) (I : Type u)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj E ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
    (x : X) (hx : x ∈ U) (hI : Infinite I) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk E x = 0 := by
  let y : U.toScheme := ⟨x, hx⟩
  let e' : E.restrict U.ι ≅ freeM U.toScheme I :=
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app E ≪≫ e
  letI : Module (U.toScheme.presheaf.stalk y) ((E.restrict U.ι).presheaf.stalk y) :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme (E.restrict U.ι) y
  letI : Module (U.toScheme.presheaf.stalk y) (freeStalk U.toScheme I y) :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme (freeM U.toScheme I) y
  letI : Module (X.presheaf.stalk x) (E.presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkModule X E x
  let L : (E.restrict U.ι).presheaf.stalk y ≃ₗ[U.toScheme.presheaf.stalk y] freeStalk U.toScheme I y :=
    ((AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme y).mapIso e').toLinearEquiv
  let σ : U.toScheme.presheaf.stalk y ≃+* X.presheaf.stalk x :=
    (U.stalkIso y).commRingCatIsoToRingEquiv
  letI : RingHomInvPair (σ : U.toScheme.presheaf.stalk y →+* X.presheaf.stalk x)
      (σ.symm : X.presheaf.stalk x →+* U.toScheme.presheaf.stalk y) :=
    RingHomInvPair.of_ringEquiv σ
  letI : RingHomInvPair (σ.symm : X.presheaf.stalk x →+* U.toScheme.presheaf.stalk y)
      (σ : U.toScheme.presheaf.stalk y →+* X.presheaf.stalk x) :=
    RingHomInvPair.of_ringEquiv σ.symm
  let S : (E.restrict U.ι).presheaf.stalk y ≃ₛₗ[(σ : _)] E.presheaf.stalk x := by
    simpa [σ] using (AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleRestrictStalkEquiv X E U y)
  let T : freeStalk U.toScheme I y ≃ₛₗ[(σ : U.toScheme.presheaf.stalk y →+* X.presheaf.stalk x)]
      E.presheaf.stalk x := by
    simpa [σ] using L.symm.trans S
  let bE : I → E.presheaf.stalk x := fun i => T (MiyaokaMori.FreeStalk.b (Y := U.toScheme) I i y)
  let pE : I → (E.presheaf.stalk x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x) :=
    fun i => transportedProj σ T (freeProj U.toScheme I y i)
  have hpE : ∀ i j, pE i (bE j) = if j = i then 1 else 0 := by
    intro i j
    dsimp [pE, bE]
    rw [transportedProj_apply, freeProj_basis]
    split_ifs with h
    · subst h; simp
    · simp
  unfold AlgebraicGeometry.Scheme.Modules.rankAtStalk
  letI : Algebra (X.presheaf.stalk x) (X.residueField x) := (X.residue x).hom.toAlgebra
  exact (fiber_standard_li bE pE hpE).finrank_eq_zero_of_infinite

/-- Finite trivialising index set ⇒ `E_x` has a basis indexed by `I`
(the construction inside `free_stalk_of_restrict_iso_free`, `LineBundleStalkFree`, which exports only
`Module.Free`). -/
private theorem basis_of_restrict_iso_free {X : AlgebraicGeometry.Scheme.{u}}
    (E : X.Modules) (U : X.Opens) (I : Type u) [Finite I]
    (e : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj E ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
    (x : X) (hx : x ∈ U) :
    Nonempty (Module.Basis I (X.presheaf.stalk x) (E.presheaf.stalk x)) := by
  let y : U := ⟨x, hx⟩
  let e' : E.restrict U.ι ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) I :=
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app E ≪≫ e
  let := AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme (E.restrict U.ι) y
  let := AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme (MiyaokaMori.FreeStalk.freeM U.toScheme I) y
  let := AlgebraicGeometry.Scheme.Modules.moduleStalkModule X E x
  let L := ((AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme y).mapIso e').toLinearEquiv
  obtain ⟨b0⟩ := free_stalk_basis (Y := U.toScheme) I y
  let b1 := b0.map L.symm
  let σ := (U.stalkIso y).commRingCatIsoToRingEquiv
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  exact MiyaokaMori.basis_of_semilinearEquiv
    (AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleRestrictStalkEquiv X E U y) b1

end MiyaokaMori.StalkBasisOfRank

/-- **Stalk basis of a locally free module at a point of rank `n > 0`.** `E` locally free
(`SheafOfModules.IsLocallyFree`), `rankAtStalk E x = n` with `0 < n`; then `E_x` has an
`O_{X,x}`-basis indexed by `ULift (Fin n)`. (Module structure: `AlgebraicGeometry.Scheme.Modules.moduleStalkModule`.)
See the module docstring for the proof. -/
theorem AlgebraicGeometry.Scheme.Modules.nonempty_stalk_basis_fin_of_isLocallyFree
    {X : AlgebraicGeometry.Scheme.{u}} (E : X.Modules) [E.IsLocallyFree] (x : X) (n : ℕ) (hn : 0 < n)
    (hx : AlgebraicGeometry.Scheme.Modules.rankAtStalk E x = n) :
    Nonempty (Module.Basis (ULift.{u} (Fin n)) (X.presheaf.stalk x) (E.presheaf.stalk x)) := by
  classical
  obtain ⟨U, I, hxU, ⟨e⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree E x
  by_cases hI : Finite I
  · letI : Finite I := hI
    have : Fintype I := Fintype.ofFinite I
    have hcard : Fintype.card I = n := by
      rw [← hx, AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free E U I e x hxU]
    obtain ⟨b⟩ := MiyaokaMori.StalkBasisOfRank.basis_of_restrict_iso_free E U I e x hxU
    have hcard' : Fintype.card I = Fintype.card (ULift.{u} (Fin n)) := by
      rw [hcard, Fintype.card_ulift, Fintype.card_fin]
    exact ⟨b.reindex (Fintype.equivOfCardEq hcard')⟩
  · exfalso
    have hInf : Infinite I := not_finite_iff_infinite.mp hI
    have h0 := MiyaokaMori.StalkBasisOfRank.rank_zero_of_restrict_iso_free E U I e x hxU hInf
    omega

end
