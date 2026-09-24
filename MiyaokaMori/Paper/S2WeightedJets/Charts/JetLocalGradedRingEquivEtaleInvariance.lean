import MiyaokaMori.Paper.S2WeightedJets.Jets.JetAlgebraLocalization
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetAlgebraCoaction
import Mathlib.RingTheory.Etale.Basic

/-! # Étale invariance of the based jet algebra (ring level)

**Statement.** Let `R → A → B` be a tower of commutative rings with `A → B` formally étale
(`Algebra.FormallyEtale A B`), `ε : B →ₐ[R] R` an augmentation and `ε₀ : A →ₐ[R] R` its
restriction to `A` (`hε₀ : ε (algebraMap A B x) = ε₀ x`).  Then the functoriality map
`BasedJetAlgebra.map` along `A → B`,

    `BasedJetAlgebra.towerMap ε₀ ε hε₀ r : J_r(A, ε₀) →+* J_r(B, ε)`,

is a ring isomorphism (`BasedJetAlgebra.towerEquiv`) which is compatible with the gradings
(`towerEquiv_mem_grading_iff`) and with the structure maps (`towerEquiv_algebraMap`).

**Source.** Ein–Mustaţă, *Jet schemes and singularities*, Lemma 2.9 (étale base change for jet
schemes), in the based form of §2.2 of the paper: based jets only
see the formal neighbourhood of the section, and along a formally étale map the formal
neighbourhoods agree.  Formal étaleness is the Stacks definition 00UQ (unique lifting along
nilpotent thickenings), taken from Mathlib (`Algebra.FormallySmooth.liftOfSurjective`,
`Algebra.FormallyUnramified.lift_unique_of_ringHom`).

**Proof (self-contained).**
1. Let `J₀ := J_r(A, ε₀)`, `T := J₀[t]/(t^{r+1})` and `u : A → T` the universal jet of `A`.
   Give `T` the `A`-algebra structure through `u`, and `J₀` the `A`-algebra structure through
   `a ↦ ε₀(a)` (constant term).  The constant term `T → J₀` is then an `A`-algebra map with
   nilpotent kernel `(t)` (`isNilpotent_ker_epsilon`).
2. Formal smoothness of `A → B` lifts the `A`-algebra map `b ↦ ε(b) : B → J₀` along `T → J₀`
   to an `A`-algebra map `ψ : B → T` (`etaleLift`); so `ψ` is a based jet of `B` with values in
   `J₀` whose restriction to `A` is `u`.
3. By the universal property of `J_r(B, ε)` (`CoeffSystem.lift`) `ψ` gives `Ψ : J_r(B, ε) → J₀`
   with `Ψ(D_n b) = coeff_n(ψ b)`; and `Φ := map (A → B) : J₀ → J_r(B, ε)` sends `D_n a` to
   `D_n(algebraMap a)`.
4. `Ψ ∘ Φ = id`: both sides agree on `R` and on every `D_n a`, because `ψ (algebraMap a) = u a`
   and `coeff_n (u a) = D_n a` (`BasedJetAlgebra.ringHom_ext`).
5. `Φ ∘ Ψ = id`: it suffices (again by `ringHom_ext`) that `T_Φ ∘ ψ = u_B` where `u_B` is the
   universal jet of `B` and `T_Φ` is `Φ` applied coefficientwise.  Both are `A`-algebra maps
   `B → J_r(B,ε)[t]/(t^{r+1})` (the `A`-structure being `u_B ∘ (A → B)`) with the same constant
   term `b ↦ ε b`, so formal unramifiedness of `A → B` forces them to agree.
6. Grading: `Φ` preserves the gradings (`map_mem_grading`); a bijective ring map between
   graded rings that maps each piece into the corresponding piece maps each piece *onto* it
   (`GradedAlgebra.mem_of_map_mem`, by uniqueness of the homogeneous decomposition). -/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

noncomputable section

open MiyaokaMori.Jet MiyaokaMori.Jet.TruncatedJetRing

/-! ## A bijective graded ring map is a graded isomorphism -/

/-- If `f` is an injective ring map between graded rings that sends each piece `𝒜 i` into `ℬ i`,
then `f x ∈ ℬ i` forces `x ∈ 𝒜 i` (uniqueness of the homogeneous decomposition). -/
theorem GradedAlgebra.mem_of_map_mem {R₁ R₂ A₁ A₂ : Type*} [CommRing R₁] [CommRing R₂]
    [CommRing A₁] [CommRing A₂] [Algebra R₁ A₁] [Algebra R₂ A₂]
    (𝒜 : ℕ → Submodule R₁ A₁) (ℬ : ℕ → Submodule R₂ A₂) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (f : A₁ →+* A₂) (hf : Function.Injective f) (hmem : ∀ (i : ℕ) (x : A₁), x ∈ 𝒜 i → f x ∈ ℬ i)
    {i : ℕ} {x : A₁} (hx : f x ∈ ℬ i) : x ∈ 𝒜 i := by
  classical
  have key : ∀ y : A₁,
      (DirectSum.decompose ℬ (f y) i : A₂) = f (DirectSum.decompose 𝒜 y i : A₁) := by
    intro y
    induction y using DirectSum.Decomposition.inductionOn (ℳ := 𝒜) with
    | zero => rw [map_zero, DirectSum.decompose_zero, DirectSum.decompose_zero]; simp
    | homogeneous m =>
      rename_i j
      by_cases hij : j = i
      · subst hij
        rw [DirectSum.decompose_of_mem_same ℬ (hmem j m m.2), DirectSum.decompose_of_mem_same 𝒜 m.2]
      · rw [DirectSum.decompose_of_mem_ne ℬ (hmem j m m.2) hij, DirectSum.decompose_of_mem_ne 𝒜 m.2 hij,
          map_zero]
    | add m m' hm hm' =>
      rw [map_add, DirectSum.decompose_add, DirectSum.decompose_add, DirectSum.add_apply,
        DirectSum.add_apply, Submodule.coe_add, Submodule.coe_add, map_add, hm, hm']
  have h1 : f x = f (DirectSum.decompose 𝒜 x i : A₁) := by
    rw [← key x, DirectSum.decompose_of_mem_same ℬ hx]
  rw [hf h1]
  exact (DirectSum.decompose 𝒜 x i).2

/-! ## The truncated ring: constant term is surjective with nilpotent kernel -/

namespace MiyaokaMori.Jet.TruncatedJetRing

variable {S : Type u} [CommRing S] (r : ℕ)

theorem epsilon_surjective :
    Function.Surjective (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon (R := S) r) := fun a =>
  ⟨MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r a,
    RingHom.congr_fun (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon_eta (R := S) r) a⟩

theorem ker_epsilon_le :
    RingHom.ker (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon (R := S) r) ≤
      Ideal.span {jetProjection S r Polynomial.X} := by
  intro x hx
  obtain ⟨p, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ x
  rw [RingHom.mem_ker] at hx
  change p.eval 0 = 0 at hx
  rw [Ideal.mem_span_singleton]
  obtain ⟨q, hq⟩ : (Polynomial.X : Polynomial S) ∣ p :=
    Polynomial.X_dvd_iff.mpr ((Polynomial.coeff_zero_eq_eval_zero p).trans hx)
  exact ⟨jetProjection S r q, by rw [← map_mul, ← hq]⟩

theorem isNilpotent_ker_epsilon :
    IsNilpotent (RingHom.ker (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon (R := S) r)) := by
  refine ⟨r + 1, eq_bot_iff.mpr ?_⟩
  calc RingHom.ker (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon (R := S) r) ^ (r + 1)
      ≤ (Ideal.span {jetProjection S r Polynomial.X}) ^ (r + 1) :=
        Ideal.pow_right_mono (ker_epsilon_le r) _
    _ = Ideal.span {jetProjection S r Polynomial.X ^ (r + 1)} :=
        Ideal.span_singleton_pow (jetProjection S r Polynomial.X) (r + 1)
    _ = ⊥ := by
        rw [MiyaokaMori.BasedAffineJet.parameter_pow_eq_zero, Ideal.span_singleton_eq_bot]

end MiyaokaMori.Jet.TruncatedJetRing

namespace BasedJetAlgebra

/-- The constant term of the universal jet is the augmentation. -/
theorem epsilon_universalJet {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (ε : B →ₐ[R] R) (r : ℕ) (b : B) :
    MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (universalJet ε r b) =
      algebraMap R (BasedJetAlgebra ε r) (ε b) := by
  rw [epsilon_eq_coeff_zero, coeff_universalJet, coeffClass_zero_order]
  rfl

section Tower

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]
  (ε₀ : A →ₐ[R] R) (ε : B →ₐ[R] R) (hε₀ : ∀ x : A, ε (algebraMap A B x) = ε₀ x) (r : ℕ)

theorem algebraMap_smul_tower (a : R) (x : A) :
    algebraMap A B (a • x) = (RingHom.id R) a • algebraMap A B x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply R A B]
  rfl

/-- `Φ = J_r(A → B) : J_r(A, ε₀) → J_r(B, ε)`, the functoriality map along the tower. -/
def towerMap : BasedJetAlgebra ε₀ r →+* BasedJetAlgebra ε r :=
  map ε₀ ε r (RingHom.id R) (algebraMap A B) (algebraMap_smul_tower) hε₀

theorem towerMap_algebraMap (a : R) :
    towerMap ε₀ ε hε₀ r (algebraMap R _ a) = algebraMap R _ a :=
  map_algebraMap ε₀ ε r (RingHom.id R) (algebraMap A B) algebraMap_smul_tower hε₀ a

theorem towerMap_coeffClass (n : ℕ) (x : A) :
    towerMap ε₀ ε hε₀ r (coeffClass ε₀ r n x) = coeffClass ε r n (algebraMap A B x) :=
  map_coeffClass ε₀ ε r (RingHom.id R) (algebraMap A B) algebraMap_smul_tower hε₀ n x

theorem towerMap_universalJet (x : A) :
    MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (towerMap ε₀ ε hε₀ r) (universalJet ε₀ r x) =
      universalJet ε r (algebraMap A B x) :=
  map_universalJet ε₀ ε r (RingHom.id R) (algebraMap A B) algebraMap_smul_tower hε₀ x

theorem towerMap_mem_grading {m : ℕ} {x : BasedJetAlgebra ε₀ r} (hx : x ∈ grading ε₀ r m) :
    towerMap ε₀ ε hε₀ r x ∈ grading ε r m :=
  map_mem_grading ε₀ r ε (RingHom.id R) (algebraMap A B) algebraMap_smul_tower hε₀ hx

section EtaleLift

variable [Algebra.FormallyEtale A B]

/-- `A`-algebra structure on `J_r(A, ε₀)[t]/(t^{r+1})` through the universal jet of `A`. -/
@[instance_reducible] def truncAlgebra : Algebra A (TruncatedJetRing (BasedJetAlgebra ε₀ r) r) :=
  (universalJet ε₀ r).toRingHom.toAlgebra

/-- `A`-algebra structure on `J_r(A, ε₀)` through the constant term `a ↦ ε₀ a`. -/
@[instance_reducible] def baseAlgebra : Algebra A (BasedJetAlgebra ε₀ r) :=
  ((algebraMap R (BasedJetAlgebra ε₀ r)).comp ε₀.toRingHom).toAlgebra

/-- The constant term `T → J_r(A, ε₀)` as an `A`-algebra map. -/
def epsilonAlgHom :
    letI := truncAlgebra ε₀ r
    letI := baseAlgebra ε₀ r
    TruncatedJetRing (BasedJetAlgebra ε₀ r) r →ₐ[A] BasedJetAlgebra ε₀ r :=
  letI := truncAlgebra ε₀ r
  letI := baseAlgebra ε₀ r
  { MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r with
    commutes' := fun x => epsilon_universalJet ε₀ r x }

/-- `b ↦ ε b : B → J_r(A, ε₀)` as an `A`-algebra map. -/
def constAlgHom :
    letI := baseAlgebra ε₀ r
    B →ₐ[A] BasedJetAlgebra ε₀ r :=
  letI := baseAlgebra ε₀ r
  { (algebraMap R (BasedJetAlgebra ε₀ r)).comp ε.toRingHom with
    commutes' := fun x => by
      show algebraMap R (BasedJetAlgebra ε₀ r) (ε (algebraMap A B x)) =
        algebraMap R (BasedJetAlgebra ε₀ r) (ε₀ x)
      rw [hε₀] }

/-- The formally étale lift `ψ : B → J_r(A, ε₀)[t]/(t^{r+1})` of the universal jet of `A`
(an `A`-algebra map with constant term `ε`). -/
def etaleLift :
    letI := truncAlgebra ε₀ r
    B →ₐ[A] TruncatedJetRing (BasedJetAlgebra ε₀ r) r :=
  letI := truncAlgebra ε₀ r
  letI := baseAlgebra ε₀ r
  Algebra.FormallySmooth.liftOfSurjective (constAlgHom ε₀ ε hε₀ r) (epsilonAlgHom ε₀ r)
    (epsilon_surjective r) (isNilpotent_ker_epsilon r)

/-- The underlying ring map of `etaleLift`. -/
def etaleLiftHom : B →+* TruncatedJetRing (BasedJetAlgebra ε₀ r) r :=
  letI := truncAlgebra ε₀ r
  (etaleLift ε₀ ε hε₀ r).toRingHom

omit [IsScalarTower R A B] in
theorem epsilon_etaleLiftHom (b : B) :
    MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (etaleLiftHom ε₀ ε hε₀ r b) =
      algebraMap R (BasedJetAlgebra ε₀ r) (ε b) := by
  letI := truncAlgebra ε₀ r
  letI := baseAlgebra ε₀ r
  exact AlgHom.congr_fun (Algebra.FormallySmooth.comp_liftOfSurjective (constAlgHom ε₀ ε hε₀ r)
    (epsilonAlgHom ε₀ r) (epsilon_surjective r) (isNilpotent_ker_epsilon r)) b

omit [IsScalarTower R A B] in
theorem etaleLiftHom_algebraMap (x : A) :
    etaleLiftHom ε₀ ε hε₀ r (algebraMap A B x) = universalJet ε₀ r x := by
  letI := truncAlgebra ε₀ r
  exact (etaleLift ε₀ ε hε₀ r).commutes x

theorem etaleLiftHom_smul (a : R) (b : B) :
    etaleLiftHom ε₀ ε hε₀ r (a • b) =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r (algebraMap R (BasedJetAlgebra ε₀ r) a) *
        etaleLiftHom ε₀ ε hε₀ r b := by
  rw [Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply R A B, etaleLiftHom_algebraMap]
  congr 1
  exact (universalJet ε₀ r).commutes a

/-- `Ψ : J_r(B, ε) → J_r(A, ε₀)`, `D_n b ↦ coeff_n (ψ b)`. -/
def towerInv : BasedJetAlgebra ε r →+* BasedJetAlgebra ε₀ r :=
  (CoeffSystem.ofTruncated ε r (algebraMap R (BasedJetAlgebra ε₀ r)) (etaleLiftHom ε₀ ε hε₀ r)
    (etaleLiftHom_smul ε₀ ε hε₀ r) (epsilon_etaleLiftHom ε₀ ε hε₀ r)).lift

theorem towerInv_algebraMap (a : R) :
    towerInv ε₀ ε hε₀ r (algebraMap R _ a) = algebraMap R _ a :=
  CoeffSystem.lift_algebraMap _ a

theorem towerInv_coeffClass (n : ℕ) (hn : n ≤ r) (b : B) :
    towerInv ε₀ ε hε₀ r (coeffClass ε r n b) = coeff r n hn (etaleLiftHom ε₀ ε hε₀ r b) := by
  rw [towerInv, CoeffSystem.lift_coeffClass _ n hn, CoeffSystem.ofTruncated_coeff,
    coeffTotal_of_le r hn]

theorem towerInv_towerMap (x : BasedJetAlgebra ε₀ r) :
    towerInv ε₀ ε hε₀ r (towerMap ε₀ ε hε₀ r x) = x := by
  have key : (towerInv ε₀ ε hε₀ r).comp (towerMap ε₀ ε hε₀ r) = RingHom.id _ := by
    refine ringHom_ext (fun a => ?_) (fun n hn x => ?_)
    · show towerInv ε₀ ε hε₀ r (towerMap ε₀ ε hε₀ r (algebraMap R _ a)) = algebraMap R _ a
      rw [towerMap_algebraMap, towerInv_algebraMap]
    · show towerInv ε₀ ε hε₀ r (towerMap ε₀ ε hε₀ r (coeffClass ε₀ r n x)) = coeffClass ε₀ r n x
      rw [towerMap_coeffClass, towerInv_coeffClass ε₀ ε hε₀ r n hn, etaleLiftHom_algebraMap,
        coeff_universalJet]
  exact RingHom.congr_fun key x

/-- `Φ` applied coefficientwise to `ψ b` is the universal jet of `b`
(uniqueness of formally étale lifts). -/
theorem map_etaleLiftHom (b : B) :
    MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (towerMap ε₀ ε hε₀ r) (etaleLiftHom ε₀ ε hε₀ r b) =
      universalJet ε r b := by
  letI : Algebra A (TruncatedJetRing (BasedJetAlgebra ε r) r) :=
    ((universalJet ε r).toRingHom.comp (algebraMap A B)).toAlgebra
  let g₁ : B →ₐ[A] TruncatedJetRing (BasedJetAlgebra ε r) r :=
    { (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (towerMap ε₀ ε hε₀ r)).comp
        (etaleLiftHom ε₀ ε hε₀ r) with
      commutes' := fun x => by
        show MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (towerMap ε₀ ε hε₀ r)
          (etaleLiftHom ε₀ ε hε₀ r (algebraMap A B x)) = universalJet ε r (algebraMap A B x)
        rw [etaleLiftHom_algebraMap, towerMap_universalJet] }
  let g₂ : B →ₐ[A] TruncatedJetRing (BasedJetAlgebra ε r) r :=
    { (universalJet ε r).toRingHom with commutes' := fun _ => rfl }
  have h : g₁ = g₂ := by
    refine Algebra.FormallyUnramified.lift_unique_of_ringHom
      (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r) (isNilpotent_ker_epsilon r) g₁ g₂ ?_
    refine RingHom.ext fun b => ?_
    show MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r
        (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (towerMap ε₀ ε hε₀ r)
          (etaleLiftHom ε₀ ε hε₀ r b)) =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (universalJet ε r b)
    have h1 : MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r
        (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (towerMap ε₀ ε hε₀ r)
          (etaleLiftHom ε₀ ε hε₀ r b)) =
        towerMap ε₀ ε hε₀ r (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r
          (etaleLiftHom ε₀ ε hε₀ r b)) :=
      RingHom.congr_fun (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon_map r
        (towerMap ε₀ ε hε₀ r)) (etaleLiftHom ε₀ ε hε₀ r b)
    rw [h1, epsilon_etaleLiftHom, towerMap_algebraMap, epsilon_universalJet]
  exact AlgHom.congr_fun h b

theorem towerMap_towerInv (y : BasedJetAlgebra ε r) :
    towerMap ε₀ ε hε₀ r (towerInv ε₀ ε hε₀ r y) = y := by
  have key : (towerMap ε₀ ε hε₀ r).comp (towerInv ε₀ ε hε₀ r) = RingHom.id _ := by
    refine ringHom_ext (fun a => ?_) (fun n hn b => ?_)
    · show towerMap ε₀ ε hε₀ r (towerInv ε₀ ε hε₀ r (algebraMap R _ a)) = algebraMap R _ a
      rw [towerInv_algebraMap, towerMap_algebraMap]
    · show towerMap ε₀ ε hε₀ r (towerInv ε₀ ε hε₀ r (coeffClass ε r n b)) = coeffClass ε r n b
      rw [towerInv_coeffClass ε₀ ε hε₀ r n hn, ← coeff_map r n hn, map_etaleLiftHom,
        coeff_universalJet]
  exact RingHom.congr_fun key y

/-- **Étale invariance of the based jet algebra**: `J_r(A, ε₀) ≃+* J_r(B, ε)` for `A → B`
formally étale, given by `D_n a ↦ D_n (algebraMap A B a)`. -/
def towerEquiv : BasedJetAlgebra ε₀ r ≃+* BasedJetAlgebra ε r where
  toFun := towerMap ε₀ ε hε₀ r
  invFun := towerInv ε₀ ε hε₀ r
  left_inv := towerInv_towerMap ε₀ ε hε₀ r
  right_inv := towerMap_towerInv ε₀ ε hε₀ r
  map_mul' := map_mul _
  map_add' := map_add _

theorem towerEquiv_apply (x : BasedJetAlgebra ε₀ r) :
    towerEquiv ε₀ ε hε₀ r x = towerMap ε₀ ε hε₀ r x := rfl

theorem towerEquiv_algebraMap (a : R) :
    towerEquiv ε₀ ε hε₀ r (algebraMap R _ a) = algebraMap R _ a :=
  towerMap_algebraMap ε₀ ε hε₀ r a

theorem towerEquiv_symm_algebraMap (a : R) :
    (towerEquiv ε₀ ε hε₀ r).symm (algebraMap R _ a) = algebraMap R _ a :=
  towerInv_algebraMap ε₀ ε hε₀ r a

/-- The isomorphism is graded. -/
theorem towerEquiv_mem_grading_iff (m : ℕ) (x : BasedJetAlgebra ε₀ r) :
    x ∈ grading ε₀ r m ↔ towerEquiv ε₀ ε hε₀ r x ∈ grading ε r m :=
  ⟨towerMap_mem_grading ε₀ ε hε₀ r, fun h =>
    GradedAlgebra.mem_of_map_mem (grading ε₀ r) (grading ε r) (towerMap ε₀ ε hε₀ r)
      (towerEquiv ε₀ ε hε₀ r).injective (fun _ _ hy => towerMap_mem_grading ε₀ ε hε₀ r hy) h⟩

theorem towerEquiv_symm_mem_grading_iff (m : ℕ) (y : BasedJetAlgebra ε r) :
    (towerEquiv ε₀ ε hε₀ r).symm y ∈ grading ε₀ r m ↔ y ∈ grading ε r m := by
  rw [towerEquiv_mem_grading_iff ε₀ ε hε₀ r m, RingEquiv.apply_symm_apply]

end EtaleLift

end Tower

end BasedJetAlgebra

end
