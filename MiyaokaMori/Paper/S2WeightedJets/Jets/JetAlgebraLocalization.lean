import MiyaokaMori.Paper.S2WeightedJets.Jets.CoeffSystemInstances
import Mathlib.RingTheory.Localization.Away.Basic

/-! # The based jet algebra commutes with localization of the base

The ring-level form of Ein–Mustață Lemma 2.3 (in the style of Stacks 01I8): **the based jet algebra commutes with
localization of the base**. Let `(R, B, ε) → (R', B', ε')` be an input of `BasedJetAlgebra.map` (`ρ : R → R'`,
`β : B → B'` compatible with the augmentations), `f ∈ R`, `R' = R[1/f]` (via `ρ`) and `B' = B[1/f]` (via `β`).
Then `J_r(B', ε') = J_r(B, ε)[1/f]` (via `BasedJetAlgebra.map`).

Proof: write `J = J_r(B,ε)`, `J' = J_r(B',ε')`, `L = J[1/f]`.
* `φ : L → J'` comes from `map` by the universal property of localization (`f` is the image of a unit of `R'` in
  `J'`).
* `ψ : J' → L` comes from the universal property of the jet algebra (`BasedJetAlgebra.lift`): `R' → L` and
  `B' → L[t]/(t^{r+1})` are the extensions along localization of `R → J → L` and of
  `B → J[t]/(t^{r+1}) → L[t]/(t^{r+1})` (the universal jet); the quotient rule here says that the universal jet of
  `f` is invertible in the truncated ring because its constant term `f` is invertible in `L`.
* The two are inverse to each other by the `ringHom_ext` of localization and of the jet algebra (compare on `R` and
  on the `D_n b`).

Source: Ein–Mustață, "Jet schemes and singularities", Lemma 2.3.
-/

set_option autoImplicit false

universe u

open MiyaokaMori.Jet MiyaokaMori.Jet.TruncatedJetRing

noncomputable section

namespace BasedJetAlgebra

variable {R B R' B' : Type u} [CommRing R] [CommRing B] [Algebra R B]
  [CommRing R'] [CommRing B'] [Algebra R' B'] (ε : B →ₐ[R] R) (ε' : B' →ₐ[R'] R') (r : ℕ)
  (ρ : R →+* R') (β : B →+* B')
  (hβ : ∀ (a : R) (b : B), β (a • b) = ρ a • β b) (hε : ∀ b : B, ε' (β b) = ρ (ε b))

theorem map_algebraMap (a : R) :
    map ε ε' r ρ β hβ hε (algebraMap R (BasedJetAlgebra ε r) a) =
      algebraMap R' (BasedJetAlgebra ε' r) (ρ a) := by
  show Ideal.Quotient.mk _ (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)) = _
  rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
  rfl

theorem map_coeffClass (n : ℕ) (b : B) :
    map ε ε' r ρ β hβ hε (coeffClass ε r n b) = coeffClass ε' r n (β b) := by
  show Ideal.Quotient.mk _ (MvPolynomial.eval₂Hom _ _ (symbol ε r n b)) = _
  rw [map_eval_symbol ε ε' r ρ β hε]
  rfl

include hβ in
theorem β_algebraMap (a : R) : β (algebraMap R B a) = algebraMap R' B' (ρ a) := by
  have h := hβ a 1
  rwa [Algebra.smul_def, mul_one, map_one, Algebra.smul_def, mul_one] at h

/-- The universal jet is compatible with `map`: `J_r(β)` sends the universal jet of `b` to that of `β b`. -/
theorem map_universalJet (b : B) :
    MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (map ε ε' r ρ β hβ hε) (universalJet ε r b) =
      universalJet ε' r (β b) := by
  refine ext_coeff r fun n hn => ?_
  rw [coeff_map, coeff_universalJet, coeff_universalJet, map_coeffClass]

section Localization

variable (f : R)

/-- L = J[1/f] -/
abbrev Loc : Type u := Localization.Away (algebraMap R (BasedJetAlgebra ε r) f)

/-- J → L -/
abbrev toLoc : BasedJetAlgebra ε r →+* Loc ε r f := algebraMap (BasedJetAlgebra ε r) (Loc ε r f)

/-- R' → L -/
def locBase (hR : letI := ρ.toAlgebra; IsLocalization.Away f R') : R' →+* Loc ε r f :=
  letI := ρ.toAlgebra
  haveI : IsLocalization.Away f R' := hR
  IsLocalization.Away.lift (S := R') f
    (g := (toLoc ε r f).comp (algebraMap R (BasedJetAlgebra ε r)))
    (IsLocalization.Away.algebraMap_isUnit (algebraMap R (BasedJetAlgebra ε r) f))

theorem locBase_ρ (hR : letI := ρ.toAlgebra; IsLocalization.Away f R') (a : R) :
    locBase ε r ρ f hR (ρ a) = toLoc ε r f (algebraMap R (BasedJetAlgebra ε r) a) :=
  letI := ρ.toAlgebra
  haveI : IsLocalization.Away f R' := hR
  IsLocalization.Away.lift_eq (S := R') f _ a

/-- `B → L[t]/(t^{r+1})`: the universal jet followed by localization of the coefficients. -/
def locJetPre : B →+* TruncatedJetRing (Loc ε r f) r :=
  (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (toLoc ε r f)).comp (universalJet ε r).toRingHom

theorem locJetPre_algebraMap (a : R) :
    locJetPre ε r f (algebraMap R B a) =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r
        (toLoc ε r f (algebraMap R (BasedJetAlgebra ε r) a)) := by
  show MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r _ (universalJet ε r (algebraMap R B a)) = _
  rw [(universalJet ε r).commutes a]
  exact congrArg (fun φ => φ (algebraMap R (BasedJetAlgebra ε r) a))
    (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map_eta r (toLoc ε r f))

theorem coeff_locJetPre (n : ℕ) (hn : n ≤ r) (b : B) :
    coeff r n hn (locJetPre ε r f b) = toLoc ε r f (coeffClass ε r n b) := by
  show coeff r n hn (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r _ (universalJet ε r b)) = _
  rw [coeff_map, coeff_universalJet]

theorem isUnit_locJetPre : IsUnit (locJetPre ε r f (algebraMap R B f)) := by
  rw [locJetPre_algebraMap]
  exact (IsLocalization.Away.algebraMap_isUnit (algebraMap R (BasedJetAlgebra ε r) f)).map
    (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r)

/-- B' → L[t]/(t^{r+1}) -/
def locJet (hB : letI := β.toAlgebra; IsLocalization.Away (algebraMap R B f) B') :
    B' →+* TruncatedJetRing (Loc ε r f) r :=
  letI := β.toAlgebra
  haveI : IsLocalization.Away (algebraMap R B f) B' := hB
  IsLocalization.Away.lift (S := B') (algebraMap R B f) (g := locJetPre ε r f)
    (isUnit_locJetPre ε r f)

theorem locJet_β (hB : letI := β.toAlgebra; IsLocalization.Away (algebraMap R B f) B') (b : B) :
    locJet ε r β f hB (β b) = locJetPre ε r f b :=
  letI := β.toAlgebra
  haveI : IsLocalization.Away (algebraMap R B f) B' := hB
  IsLocalization.Away.lift_eq (S := B') (algebraMap R B f) _ b

variable (hR : letI := ρ.toAlgebra; IsLocalization.Away f R')
  (hB : letI := β.toAlgebra; IsLocalization.Away (algebraMap R B f) B')

include hβ in
theorem locJet_comp_algebraMap :
    (locJet ε r β f hB).comp (algebraMap R' B') =
      (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r).comp (locBase ε r ρ f hR) := by
  let _ := ρ.toAlgebra
  have : IsLocalization.Away f R' := hR
  refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun a => ?_)
  show locJet ε r β f hB (algebraMap R' B' (ρ a)) =
    MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r (locBase ε r ρ f hR (ρ a))
  rw [← β_algebraMap ρ β hβ a, locJet_β, locJetPre_algebraMap, locBase_ρ]

include hβ in
theorem locJet_smul (a : R') (b : B') :
    locJet ε r β f hB (a • b) =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r (locBase ε r ρ f hR a) * locJet ε r β f hB b := by
  rw [Algebra.smul_def, map_mul]
  exact congrArg (· * _) (congrArg (fun φ => φ a) (locJet_comp_algebraMap ε r ρ β hβ f hR hB))

include hε in
theorem locJet_epsilon (b : B') :
    MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (locJet ε r β f hB b) =
      locBase ε r ρ f hR (ε' b) := by
  let _ := β.toAlgebra
  have : IsLocalization.Away (algebraMap R B f) B' := hB
  have key : (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r).comp (locJet ε r β f hB) =
      (locBase ε r ρ f hR).comp (ε' : B' →+* R') := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R B f))
      (RingHom.ext fun b₀ => ?_)
    show MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (locJet ε r β f hB (β b₀)) =
      locBase ε r ρ f hR (ε' (β b₀))
    rw [locJet_β, epsilon_eq_coeff_zero, coeff_locJetPre, hε, locBase_ρ, coeffClass_zero_order]
    rfl
  exact congrArg (fun φ => φ b) key

/-- ψ : J' → L -/
def locInv : BasedJetAlgebra ε' r →+* Loc ε r f :=
  lift ε' r (locBase ε r ρ f hR) (locJet ε r β f hB)
    (locJet_smul ε r ρ β hβ f hR hB) (locJet_epsilon ε ε' r ρ β hε f hR hB)

/-- φ : L → J' -/
def locFwd : Loc ε r f →+* BasedJetAlgebra ε' r :=
  IsLocalization.Away.lift (algebraMap R (BasedJetAlgebra ε r) f)
    (g := map ε ε' r ρ β hβ hε) (by
      let _ := ρ.toAlgebra
      have : IsLocalization.Away f R' := hR
      rw [map_algebraMap]
      exact (IsLocalization.Away.algebraMap_isUnit (S := R') f).map
        (algebraMap R' (BasedJetAlgebra ε' r)))

theorem locFwd_toLoc (x : BasedJetAlgebra ε r) :
    locFwd ε ε' r ρ β hβ hε f hR (toLoc ε r f x) = map ε ε' r ρ β hβ hε x :=
  IsLocalization.Away.lift_eq _ _ x

/-- ψ ∘ J_r(β) = (J → L) -/
theorem locInv_comp_map :
    (locInv ε ε' r ρ β hβ hε f hR hB).comp (map ε ε' r ρ β hβ hε) = toLoc ε r f := by
  refine BasedJetAlgebra.ringHom_ext (fun a => ?_) fun n hn b => ?_
  · show locInv ε ε' r ρ β hβ hε f hR hB (map ε ε' r ρ β hβ hε (algebraMap R _ a)) = _
    rw [map_algebraMap]
    show MvPolynomial.eval₂Hom _ _ (MvPolynomial.C (ρ a)) = _
    rw [MvPolynomial.eval₂Hom_C, locBase_ρ]
  · show locInv ε ε' r ρ β hβ hε f hR hB (map ε ε' r ρ β hβ hε (coeffClass ε r n b)) = _
    rw [map_coeffClass]
    show lift ε' r _ _ _ _ (coeffClass ε' r n (β b)) = _
    rw [lift_coeffClass ε' r _ _ _ _ n hn, locJet_β, coeff_locJetPre]

theorem locInv_locFwd (x : Loc ε r f) :
    locInv ε ε' r ρ β hβ hε f hR hB (locFwd ε ε' r ρ β hβ hε f hR x) = x := by
  have key : ((locInv ε ε' r ρ β hβ hε f hR hB).comp (locFwd ε ε' r ρ β hβ hε f hR)).comp
      (toLoc ε r f) = (RingHom.id _).comp (toLoc ε r f) := by
    refine RingHom.ext fun y => ?_
    show locInv ε ε' r ρ β hβ hε f hR hB (locFwd ε ε' r ρ β hβ hε f hR (toLoc ε r f y)) = _
    rw [locFwd_toLoc]
    exact congrArg (fun φ => φ y) (locInv_comp_map ε ε' r ρ β hβ hε f hR hB)
  exact congrArg (fun φ => φ x)
    (IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R (BasedJetAlgebra ε r) f)) key)

/-- At the level of truncated rings: after applying `φ` to the coefficients, the jet given by `ψ` is the universal
jet of `J'`. -/
theorem map_locFwd_locJet (b : B') :
    MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (locFwd ε ε' r ρ β hβ hε f hR)
      (locJet ε r β f hB b) = universalJet ε' r b := by
  let _ := β.toAlgebra
  have : IsLocalization.Away (algebraMap R B f) B' := hB
  have key : (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (locFwd ε ε' r ρ β hβ hε f hR)).comp
      (locJet ε r β f hB) = (universalJet ε' r).toRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R B f))
      (RingHom.ext fun b₀ => ?_)
    show MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r _ (locJet ε r β f hB (β b₀)) =
      universalJet ε' r (β b₀)
    rw [locJet_β, ← map_universalJet ε ε' r ρ β hβ hε]
    refine ext_coeff r fun n hn => ?_
    rw [coeff_map, coeff_locJetPre, locFwd_toLoc, coeff_map, coeff_universalJet]
  exact congrArg (fun φ => φ b) key

theorem locFwd_locInv (y : BasedJetAlgebra ε' r) :
    locFwd ε ε' r ρ β hβ hε f hR (locInv ε ε' r ρ β hβ hε f hR hB y) = y := by
  have key : (locFwd ε ε' r ρ β hβ hε f hR).comp (locInv ε ε' r ρ β hβ hε f hR hB) =
      RingHom.id _ := by
    let _ := ρ.toAlgebra
    have : IsLocalization.Away f R' := hR
    refine BasedJetAlgebra.ringHom_ext (fun a => ?_) fun n hn b => ?_
    · show locFwd ε ε' r ρ β hβ hε f hR (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)) = _
      rw [MvPolynomial.eval₂Hom_C]
      have h2 : (locFwd ε ε' r ρ β hβ hε f hR).comp (locBase ε r ρ f hR) =
          algebraMap R' (BasedJetAlgebra ε' r) := by
        refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun a₀ => ?_)
        show locFwd ε ε' r ρ β hβ hε f hR (locBase ε r ρ f hR (ρ a₀)) = algebraMap R' _ (ρ a₀)
        rw [locBase_ρ, locFwd_toLoc, map_algebraMap]
      exact congrArg (fun φ => φ a) h2
    · show locFwd ε ε' r ρ β hβ hε f hR (lift ε' r _ _ _ _ (coeffClass ε' r n b)) = _
      rw [lift_coeffClass ε' r _ _ _ _ n hn, ← coeff_map,
        map_locFwd_locJet ε ε' r ρ β hβ hε f hR hB, coeff_universalJet]
      rfl
  exact congrArg (fun φ => φ y) key

include hR hB in
/-- **The jet algebra commutes with localization of the base**: `J_r(B[1/f], ε_f) = J_r(B, ε)[1/f]`. -/
theorem isLocalization_away_map :
    letI := (map ε ε' r ρ β hβ hε).toAlgebra
    IsLocalization.Away (algebraMap R (BasedJetAlgebra ε r) f) (BasedJetAlgebra ε' r) := by
  let _ := (map ε ε' r ρ β hβ hε).toAlgebra
  let e : Loc ε r f ≃ₐ[BasedJetAlgebra ε r] BasedJetAlgebra ε' r :=
    { toFun := locFwd ε ε' r ρ β hβ hε f hR
      invFun := locInv ε ε' r ρ β hβ hε f hR hB
      left_inv := locInv_locFwd ε ε' r ρ β hβ hε f hR hB
      right_inv := locFwd_locInv ε ε' r ρ β hβ hε f hR hB
      map_mul' := map_mul _
      map_add' := map_add _
      commutes' := locFwd_toLoc ε ε' r ρ β hβ hε f hR }
  exact IsLocalization.isLocalization_of_algEquiv
    (Submonoid.powers (algebraMap R (BasedJetAlgebra ε r) f)) e

end Localization

end BasedJetAlgebra

end
