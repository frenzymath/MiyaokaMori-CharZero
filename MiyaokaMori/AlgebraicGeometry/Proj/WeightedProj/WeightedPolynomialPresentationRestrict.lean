import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.OfGradedQCAlgebra
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.Localization

/-! # Restricting a weighted-polynomial presentation of a graded quasi-coherent algebra to a basic open

Used for the jet-coordinate transitions (equation (2.7) of the paper and the affine
lift after finite base change, Lemma 3.1). Reference: Stacks 01I8 (sections of a
quasi-coherent sheaf over `D(f)` are the localization at `f`).

Let `S` be a graded quasi-coherent algebra on a scheme `X`, `U` an affine open, `w : σ → ℕ` weights and
`coords p ∈ S_{w p}(U)` sections. `polyEval` is the ring homomorphism `Γ(X, U)[x_σ] → S(U)`,
`x_p ↦ ofPiece (coords p)`, `r ↦ r`. A `PolyPresentation` records that `S(U) ≃ Γ(X, U)[x_σ]` with the
`coords` as variables, the structure map as the constants and the grading as weighted homogeneity —
exactly the ring-theoretic content of `jetChart.IsHonest`. This module transports such a presentation
to a basic open `V = D(f) ⊆ U`:

* `polyEval_basicOpen_injective`: `Γ(X, V)[x] → S(V)` (restricted coordinates) is injective. Proof:
  `Γ(X, V)[x]` is the localization of `Γ(X, U)[x]` at `f` (Mathlib `MvPolynomial.isLocalization`) and
  `S(V)` that of `S(U)` at `f` (`affineUnit_coequifibered`, the quasi-coherence of the pieces), the two
  evaluation maps are compatible with restriction (`polyEval_map`), and the one on `U` is bijective.
* `exists_polyEval_basicOpen_eq`: every `a ∈ S_m(V)` is `polyEval T` for a weighted-homogeneous `T`
  of weight `m` over `Γ(X, V)` (`Modules.exists_pow_smul_eq_map_basicOpen`: `f^n • a` lifts to `U`,
  where it is a weighted-homogeneous polynomial by the presentation; divide by the unit `f|_V^n`).
* `exists_transition`: two presentations on affine opens `U`, `U'` with a common basic open
  `V = D(f) = D(f')` give weighted-homogeneous transition polynomials `T`, `T'` expressing each
  family of restricted coordinates in the other, inverse to each other under substitution
  (`bind₁ T' (T p) = X p` and symmetrically).
-/
set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A ring homomorphism preserves weighted homogeneity (coefficientwise). -/
theorem MvPolynomial.IsWeightedHomogeneous.map_of {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    {w : σ → ℕ} {m : ℕ} {p : MvPolynomial σ R} (h : p.IsWeightedHomogeneous w m) (f : R →+* S) :
    (MvPolynomial.map f p).IsWeightedHomogeneous w m := by
  intro d hd
  refine h (fun hz => hd ?_)
  rw [MvPolynomial.coeff_map, hz, map_zero]

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) {σ : Type*} (w : σ → ℕ)

/-- The evaluation homomorphism `Γ(X, U)[x_σ] →+* S(U)`, `C r ↦ sectionsUnitHom r`,
`X p ↦ ofPiece (coords p)`. -/
def polyEval (U : X.Opens) (coords : ∀ p : σ, S.sectionsPiece U (w p)) :
    MvPolynomial σ Γ(X, U) →+* S.sectionsRing U :=
  MvPolynomial.eval₂Hom (S.sectionsUnitHom U) fun p => S.ofPiece U (w p) (coords p)

theorem polyEval_C (U : X.Opens) (coords : ∀ p : σ, S.sectionsPiece U (w p)) (r : Γ(X, U)) :
    S.polyEval w U coords (MvPolynomial.C r) = S.sectionsUnitHom U r :=
  MvPolynomial.eval₂Hom_C _ _ r

theorem polyEval_X (U : X.Opens) (coords : ∀ p : σ, S.sectionsPiece U (w p)) (p : σ) :
    S.polyEval w U coords (MvPolynomial.X p) = S.ofPiece U (w p) (coords p) :=
  MvPolynomial.eval₂Hom_X' _ _ p

/-- The coordinates restricted to a smaller open. -/
def restrictCoords {U V : X.Opens} (h : V ≤ U) (coords : ∀ p : σ, S.sectionsPiece U (w p)) :
    ∀ p : σ, S.sectionsPiece V (w p) :=
  fun p => S.sectionsRestrictPiece h (w p) (coords p)

/-- Evaluation is compatible with restriction: `polyEval_V (Q|_V) = (polyEval_U Q)|_V`. -/
theorem polyEval_map {U V : X.Opens} (h : V ≤ U) (coords : ∀ p : σ, S.sectionsPiece U (w p))
    (Q : MvPolynomial σ Γ(X, U)) :
    S.polyEval w V (S.restrictCoords w h coords)
        (MvPolynomial.map (X.presheaf.map (homOfLE h).op).hom Q) =
      S.sectionsRestrictHom h (S.polyEval w U coords Q) := by
  have key : (S.polyEval w V (S.restrictCoords w h coords)).comp
      (MvPolynomial.map (X.presheaf.map (homOfLE h).op).hom) =
      (S.sectionsRestrictHom h).comp (S.polyEval w U coords) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.map_C, polyEval_C, polyEval_C,
        S.sectionsUnitHom_naturality h r]
    · rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.map_X, polyEval_X, polyEval_X,
        S.sectionsRestrictHom_ofPiece h]
      rfl
  exact DFunLike.congr_fun key Q

/-- A weighted-polynomial presentation of `S(U)` with the `coords` as variables: the ring-theoretic
part of `jetChart.IsHonest` (`ε` graded, constants ↦ `C`, `coords p ↦ X p`). -/
structure PolyPresentation (U : X.Opens) (coords : ∀ p : σ, S.sectionsPiece U (w p)) where
  equiv : S.sectionsRing U ≃+* MvPolynomial σ Γ(X, U)
  equiv_unit : ∀ r : Γ(X, U), equiv (S.sectionsUnitHom U r) = MvPolynomial.C r
  equiv_coords : ∀ p : σ, equiv (S.ofPiece U (w p) (coords p)) = MvPolynomial.X p
  equiv_grading : ∀ (m : ℕ) (a : S.sectionsRing U), a ∈ S.sectionsGrading U m →
    (equiv a).IsWeightedHomogeneous w m

namespace PolyPresentation

variable {S} {w} {U : X.Opens} {coords : ∀ p : σ, S.sectionsPiece U (w p)}
  (P : S.PolyPresentation w U coords)

theorem polyEval_eq : S.polyEval w U coords = P.equiv.symm.toRingHom := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
  · rw [polyEval_C]
    show _ = P.equiv.symm (MvPolynomial.C r)
    exact (P.equiv.symm_apply_eq.mpr (P.equiv_unit r).symm).symm
  · rw [polyEval_X]
    show _ = P.equiv.symm (MvPolynomial.X p)
    exact (P.equiv.symm_apply_eq.mpr (P.equiv_coords p).symm).symm

include P in
theorem polyEval_bijective : Function.Bijective (S.polyEval w U coords) := by
  rw [P.polyEval_eq]
  exact P.equiv.symm.bijective

theorem polyEval_equiv (a : S.sectionsRing U) : S.polyEval w U coords (P.equiv a) = a := by
  rw [P.polyEval_eq]
  exact P.equiv.symm_apply_apply a

end PolyPresentation

/-- **Stacks 01I8 for the sections ring**: `S(D f) = S(U)[1/f]` for `U` affine (the graded version
`affineUnit_coequifibered`, read through Mathlib's `coequifibered_iff_forall_isLocalizationAway`). -/
theorem isLocalization_away_basicOpen {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    (f : Γ(X, U)) :
    letI := (S.sectionsRestrictHom (X.basicOpen_le f)).toAlgebra
    IsLocalization.Away (S.sectionsUnitHom U f) (S.sectionsRing (X.basicOpen f)) := by
  letI := (S.sectionsRestrictHom (X.basicOpen_le f)).toAlgebra
  have h := AlgebraicGeometry.Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mp
    S.affineUnit_coequifibered ⟨U, hU⟩ f
  exact h

/-- **Injectivity of the restricted evaluation on a basic open.** With `V = D(f) ⊆ U`, `U` affine and
a presentation on `U`, the evaluation `Γ(X, V)[x] → S(V)` in the restricted coordinates is injective:
`Γ(X, V)[x]` is the localization of `Γ(X, U)[x]` at `C f`, `S(V)` that of `S(U)` at `f`, the
evaluations are compatible with restriction and the one on `U` is bijective. -/
theorem polyEval_basicOpen_injective {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    {coords : ∀ p : σ, S.sectionsPiece U (w p)} (P : S.PolyPresentation w U coords)
    (f : Γ(X, U)) {V : X.Opens} (hVf : V = X.basicOpen f) (h : V ≤ U) :
    Function.Injective (S.polyEval w V (S.restrictCoords w h coords)) := by
  subst hVf
  -- `Γ(X, D f) = Γ(X, U)[1/f]` and `Γ(X, D f)[x] = Γ(X, U)[x][1/C f]`
  letI algΓ : Algebra Γ(X, U) Γ(X, X.basicOpen f) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  haveI hlocΓ : IsLocalization.Away f Γ(X, X.basicOpen f) :=
    hU.isLocalization_of_eq_basicOpen f (homOfLE h) rfl
  letI algP : Algebra (MvPolynomial σ Γ(X, U)) (MvPolynomial σ Γ(X, X.basicOpen f)) :=
    MvPolynomial.algebraMvPolynomial
  haveI hlocP : IsLocalization ((Submonoid.powers f).map (MvPolynomial.C (σ := σ)))
      (MvPolynomial σ Γ(X, X.basicOpen f)) := MvPolynomial.isLocalization _ _
  -- `S(D f) = S(U)[1/f]`
  letI algS : Algebra (S.sectionsRing U) (S.sectionsRing (X.basicOpen f)) :=
    (S.sectionsRestrictHom h).toAlgebra
  haveI hlocS : IsLocalization.Away (S.sectionsUnitHom U f) (S.sectionsRing (X.basicOpen f)) :=
    S.isLocalization_away_basicOpen hU f
  set u : Γ(X, X.basicOpen f) := (X.presheaf.map (homOfLE h).op).hom f with hu_def
  have hu : IsUnit u := X.toRingedSpace.isUnit_res_basicOpen f
  have hCu : IsUnit (MvPolynomial.C u : MvPolynomial σ Γ(X, X.basicOpen f)) :=
    hu.map (MvPolynomial.C : Γ(X, X.basicOpen f) →+* MvPolynomial σ Γ(X, X.basicOpen f))
  intro Q₁ Q₂ hQ
  rw [← sub_eq_zero, ← map_sub] at hQ
  rw [← sub_eq_zero]
  set Q := Q₁ - Q₂ with hQ_def
  clear_value Q
  -- clear denominators: `Q * C u^n = Q'|_V`
  obtain ⟨⟨Q', ⟨_, ⟨a, ⟨n, rfl⟩, rfl⟩⟩⟩, hQ'⟩ :=
    IsLocalization.surj ((Submonoid.powers f).map (MvPolynomial.C (σ := σ))) Q
  have hQ'' : Q * MvPolynomial.C (u ^ n) =
      MvPolynomial.map (X.presheaf.map (homOfLE h).op).hom Q' := by
    have e1 : algebraMap (MvPolynomial σ Γ(X, U)) (MvPolynomial σ Γ(X, X.basicOpen f))
        (MvPolynomial.C (f ^ n)) = MvPolynomial.C (u ^ n) := by
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C, map_pow]
      rfl
    have e2 : algebraMap (MvPolynomial σ Γ(X, U)) (MvPolynomial σ Γ(X, X.basicOpen f)) Q' =
        MvPolynomial.map (X.presheaf.map (homOfLE h).op).hom Q' := rfl
    rw [← e1, ← e2]
    exact hQ'
  -- `Q'` evaluates to something restricting to `0`, hence killed by a power of `f`
  have h1 : S.sectionsRestrictHom h (S.polyEval w U coords Q') = 0 := by
    rw [← S.polyEval_map w h coords Q', ← hQ'', map_mul, hQ, zero_mul]
  have h2 : algebraMap (S.sectionsRing U) (S.sectionsRing (X.basicOpen f))
      (S.polyEval w U coords Q') = 0 := h1
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (S.sectionsUnitHom U f)) (S.sectionsRing (X.basicOpen f)) _).mp h2
  have h3 : S.polyEval w U coords (MvPolynomial.C (f ^ m) * Q') = 0 := by
    rw [map_mul, polyEval_C, map_pow]
    exact hm
  have h4 : MvPolynomial.C (f ^ m) * Q' = 0 :=
    P.polyEval_bijective.injective (h3.trans (map_zero _).symm)
  have h5 := congrArg (MvPolynomial.map (X.presheaf.map (homOfLE h).op).hom) h4
  rw [map_mul, MvPolynomial.map_C, map_pow, map_zero, ← hQ''] at h5
  have h6 : Q * (MvPolynomial.C (u ^ m) * MvPolynomial.C (u ^ n)) = 0 := by
    rw [← h5]
    ring
  have hunit : IsUnit (MvPolynomial.C (u ^ m) * MvPolynomial.C (u ^ n) :
      MvPolynomial σ Γ(X, X.basicOpen f)) := by
    rw [map_pow, map_pow]
    exact (hCu.pow m).mul (hCu.pow n)
  exact hunit.mul_left_eq_zero.mp h6

/-- **Every section over a basic open is a weighted-homogeneous polynomial in the restricted
coordinates** (Stacks 01I8). With `V = D(f) ⊆ U`, `U` affine, a presentation on `U` and
`a ∈ S_m(V)`: `f|_V^n • a` is the restriction of some `t ∈ S_m(U)` (`exists_pow_smul_eq_map_basicOpen`),
`t` is a weighted-homogeneous polynomial of weight `m` in the coordinates (the presentation), and
`f|_V` is a unit on `V`. -/
theorem exists_polyEval_basicOpen_eq {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    {coords : ∀ p : σ, S.sectionsPiece U (w p)} (P : S.PolyPresentation w U coords)
    (f : Γ(X, U)) {V : X.Opens} (hVf : V = X.basicOpen f) (h : V ≤ U) (m : ℕ)
    (a : S.sectionsPiece V m) :
    ∃ T : MvPolynomial σ Γ(X, V), T.IsWeightedHomogeneous w m ∧
      S.polyEval w V (S.restrictCoords w h coords) T = S.ofPiece V m a := by
  subst hVf
  have hqc : (S.part m).IsQuasicoherent := S.quasicoherent m
  obtain ⟨n, t, ht⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_map_basicOpen (S.part m) hU f a
  set u : Γ(X, X.basicOpen f) := (X.presheaf.map (homOfLE h).op).hom f with hu_def
  have hu : IsUnit u := X.toRingedSpace.isUnit_res_basicOpen f
  set v : Γ(X, X.basicOpen f) := ↑hu.unit⁻¹ with hv_def
  have hvu : v ^ n * u ^ n = 1 := by
    rw [← mul_pow, hu.val_inv_mul, one_pow]
  refine ⟨MvPolynomial.C (v ^ n) *
    MvPolynomial.map (X.presheaf.map (homOfLE h).op).hom (P.equiv (S.ofPiece U m t)), ?_, ?_⟩
  · have h1 : (P.equiv (S.ofPiece U m t)).IsWeightedHomogeneous w m :=
      P.equiv_grading m _ ⟨t, rfl⟩
    have h2 := (MvPolynomial.isWeightedHomogeneous_C w (v ^ n)).mul
      (h1.map_of (X.presheaf.map (homOfLE h).op).hom)
    rwa [zero_add] at h2
  · have e1 : S.polyEval w _ (S.restrictCoords w h coords)
        (MvPolynomial.map (X.presheaf.map (homOfLE h).op).hom (P.equiv (S.ofPiece U m t))) =
        S.ofPiece (X.basicOpen f) m (S.sectionsRestrictPiece h m t) := by
      rw [S.polyEval_map w h coords, P.polyEval_equiv]
      exact S.sectionsRestrictHom_ofPiece h m t
    have e2 : S.ofPiece (X.basicOpen f) m (S.sectionsRestrictPiece h m t) =
        S.sectionsUnitHom (X.basicOpen f) (u ^ n) * S.ofPiece (X.basicOpen f) m a := by
      rw [S.sectionsUnitHom_mul_ofPiece]
      exact congrArg (S.ofPiece (X.basicOpen f) m) ht
    rw [map_mul, polyEval_C, e1, e2]
    calc S.sectionsUnitHom (X.basicOpen f) (v ^ n) *
          (S.sectionsUnitHom (X.basicOpen f) (u ^ n) * S.ofPiece (X.basicOpen f) m a)
        = S.sectionsUnitHom (X.basicOpen f) (v ^ n * u ^ n) * S.ofPiece (X.basicOpen f) m a := by
          rw [map_mul]
          exact (_root_.mul_assoc _ _ _).symm
      _ = S.ofPiece (X.basicOpen f) m a := by
          rw [hvu, map_one]
          exact _root_.one_mul _

/-- **Transition between two presentations on a common basic open.** Presentations on affine opens
`U`, `U'` and a common basic open `V = D(f) = D(f')` (`exists_basicOpen_le_affine_inter`) give
weighted-homogeneous `T p`, `T' p` of weight `w p` over `Γ(X, V)` with
`polyEval (T p) = coords' p|_V` (in the `coords`) and `polyEval' (T' p) = coords p|_V` (in the
`coords'`), inverse to each other: `bind₁ T' (T p) = X p` and `bind₁ T (T' p) = X p`
(`exists_polyEval_basicOpen_eq` for each coordinate, then `polyEval_basicOpen_injective`). -/
theorem exists_transition {U U' : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    (hU' : AlgebraicGeometry.IsAffineOpen U')
    {coords : ∀ p : σ, S.sectionsPiece U (w p)} {coords' : ∀ p : σ, S.sectionsPiece U' (w p)}
    (P : S.PolyPresentation w U coords) (P' : S.PolyPresentation w U' coords')
    (f : Γ(X, U)) (f' : Γ(X, U')) {V : X.Opens} (hVf : V = X.basicOpen f)
    (hVf' : V = X.basicOpen f') (h : V ≤ U) (h' : V ≤ U') :
    ∃ T T' : σ → MvPolynomial σ Γ(X, V),
      (∀ p, (T p).IsWeightedHomogeneous w (w p)) ∧
      (∀ p, (T' p).IsWeightedHomogeneous w (w p)) ∧
      (∀ p, S.polyEval w V (S.restrictCoords w h coords) (T p) =
        S.ofPiece V (w p) (S.restrictCoords w h' coords' p)) ∧
      (∀ p, S.polyEval w V (S.restrictCoords w h' coords') (T' p) =
        S.ofPiece V (w p) (S.restrictCoords w h coords p)) ∧
      (∀ p, MvPolynomial.bind₁ T' (T p) = MvPolynomial.X p) ∧
      (∀ p, MvPolynomial.bind₁ T (T' p) = MvPolynomial.X p) := by
  choose T hT hTe using fun p =>
    S.exists_polyEval_basicOpen_eq w hU P f hVf h (w p) (S.restrictCoords w h' coords' p)
  choose T' hT' hT'e using fun p =>
    S.exists_polyEval_basicOpen_eq w hU' P' f' hVf' h' (w p) (S.restrictCoords w h coords p)
  have hcomp : (S.polyEval w V (S.restrictCoords w h' coords')).comp
      (MvPolynomial.bind₁ T').toRingHom = S.polyEval w V (S.restrictCoords w h coords) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · show S.polyEval w V (S.restrictCoords w h' coords') (MvPolynomial.bind₁ T' (MvPolynomial.C r)) =
        S.polyEval w V (S.restrictCoords w h coords) (MvPolynomial.C r)
      rw [MvPolynomial.bind₁_C_right, polyEval_C, polyEval_C]
    · show S.polyEval w V (S.restrictCoords w h' coords') (MvPolynomial.bind₁ T' (MvPolynomial.X p)) =
        S.polyEval w V (S.restrictCoords w h coords) (MvPolynomial.X p)
      rw [MvPolynomial.bind₁_X_right, hT'e p, polyEval_X]
  have hcomp' : (S.polyEval w V (S.restrictCoords w h coords)).comp
      (MvPolynomial.bind₁ T).toRingHom = S.polyEval w V (S.restrictCoords w h' coords') := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · show S.polyEval w V (S.restrictCoords w h coords) (MvPolynomial.bind₁ T (MvPolynomial.C r)) =
        S.polyEval w V (S.restrictCoords w h' coords') (MvPolynomial.C r)
      rw [MvPolynomial.bind₁_C_right, polyEval_C, polyEval_C]
    · show S.polyEval w V (S.restrictCoords w h coords) (MvPolynomial.bind₁ T (MvPolynomial.X p)) =
        S.polyEval w V (S.restrictCoords w h' coords') (MvPolynomial.X p)
      rw [MvPolynomial.bind₁_X_right, hTe p, polyEval_X]
  refine ⟨T, T', hT, hT', hTe, hT'e, fun p => ?_, fun p => ?_⟩
  · apply S.polyEval_basicOpen_injective w hU' P' f' hVf' h'
    have e := DFunLike.congr_fun hcomp (T p)
    rw [polyEval_X, ← hTe p]
    exact e
  · apply S.polyEval_basicOpen_injective w hU P f hVf h
    have e := DFunLike.congr_fun hcomp' (T' p)
    rw [polyEval_X, ← hT'e p]
    exact e

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
