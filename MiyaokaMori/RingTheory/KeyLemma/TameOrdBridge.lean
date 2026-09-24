import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.TameOrd
import MiyaokaMori.RingTheory.KeyLemma.Defs
import MiyaokaMori.RingTheory.KeyLemma.SumDefs
import MiyaokaMori.RingTheory.KeyLemma.HsymEqLam
import MiyaokaMori.RingTheory.OrderOfVanishing.OrdNormEqLength

/-! # Bridge lemmas (B1)–(B5) for `tameOrd = −Σ Hsym`

`TameOrdEqHsym` translates the language in which `Ring.tameSymbol` is defined (the `HeightOneSpectrum` of
`integralClosure (Localization.AtPrime q) K`, the residue fields of the valuation subrings, `Algebra.norm`)
into the language of `(A, B = Ã, 𝔭)`. This file contains the pieces of that bridge: two definitions
(`ι`, `𝔭_v`, `B → O_v`), two auxiliary lemmas (`exp_finsum`, (B6a) `tameOrd_eq_finprod_ordFrac_tameSymbolAt`),
and the five named steps (B1)(B2)(B3)(B4)(B5). The parent theorem in `TameOrdEqHsym` assembles them.

Notation: `K = Frac A`, `R = A_q = Localization.AtPrime q.asIdeal`, `B = integralClosure A K`,
`C = integralClosure R K`, `ι = KeyLemma.toIcAtPrime A q : B →+* C`,
`𝔭_v = KeyLemma.primeBelow A q v = ι⁻¹(v)`, `O_v = (v.valuation K).valuationSubring`,
`KeyLemma.toValuationSubringIC A q v : B →+* O_v`.

Reference: the equation at the end of the first paragraph of Stacks 0EAW (0EAT + 02MJ) combined with
`e_A(M_i, a, b) = −ord(∂(a,b))` of the third and fourth paragraphs; `ord_{A/q} ∘ Norm = A-length` is Stacks
02MI (`Ring.ordFrac_norm_eq_exp_length`).

The equality form `C = S⁻¹B` of Stacks 0307 is Mathlib's `IsLocalization.integralClosure`
(`KeyLemma.isLocalization_toIcAtPrime`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open PeriodicComplex

noncomputable section

namespace KeyLemma

/-! ## Definitions -/

/-- `ι : Ã → (A_q)~`: an element integral over `A` is still integral over `A_q` (`IsIntegral.tower_top`; the
scalar tower `A → A_q → K` is the Mathlib instance `IsLocalization.instIsScalarTower…AtPrime`). -/
def toIcAtPrime (A : Type u) [CommRing A] [IsDomain A] (q : PrimeSpectrum A) :
    integralClosure A (FractionRing A) →+*
      integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A) where
  toFun x := ⟨x.1, x.2.tower_top⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

@[simp] theorem coe_toIcAtPrime {A : Type u} [CommRing A] [IsDomain A] (q : PrimeSpectrum A)
    (x : integralClosure A (FractionRing A)) :
    ((toIcAtPrime A q x : integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) :
      FractionRing A) = (x : FractionRing A) := rfl

/-- `𝔭_v := ι⁻¹(v)`, the contraction of `v` to a prime of `B`. -/
def primeBelow (A : Type u) [CommRing A] [IsDomain A] (q : PrimeSpectrum A)
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))) :
    PrimeSpectrum (integralClosure A (FractionRing A)) :=
  ⟨v.asIdeal.comap (toIcAtPrime A q), Ideal.comap_isPrime _ _⟩

theorem mem_primeBelow_iff {A : Type u} [CommRing A] [IsDomain A] (q : PrimeSpectrum A)
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (x : integralClosure A (FractionRing A)) :
    x ∈ (primeBelow A q v).asIdeal ↔ toIcAtPrime A q x ∈ v.asIdeal := Iff.rfl

/-- Elements of `B` lie in the valuation ring of `v` (`B ⊆ C ⊆ O_v`). -/
def toValuationSubringIC (A : Type u) [CommRing A] [IsDomain A] (q : PrimeSpectrum A)
    [IsDedekindDomain (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))]
    [IsFractionRing (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))
      (FractionRing A)]
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))) :
    integralClosure A (FractionRing A) →+*
      (IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v).valuationSubring where
  toFun x := ⟨(x : FractionRing A), IsDedekindDomain.HeightOneSpectrum.valuation_le_one v
    (toIcAtPrime A q x)⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-! ## Two auxiliary lemmas -/

/-- `WithZero.exp` turns finite sums into finite products. -/
theorem exp_finsum {α : Type*} (g : α → ℤ) (hg : (Function.support g).Finite) :
    (WithZero.exp (∑ᶠ i, g i) : WithZero (Multiplicative ℤ)) = ∏ᶠ i, WithZero.exp (g i) := by
  classical
  rw [finsum_eq_sum _ hg]
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hg.toFinset) (fun i hi => by
    simp only [Set.Finite.coe_toFinset, Function.mem_support]
    intro h0
    exact hi (by simp [h0]))]
  induction hg.toFinset using Finset.induction_on with
  | empty => simp
  | insert x t hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, WithZero.exp_add, ih]

/-- **(B6a)**: `Ring.tameOrd` unfolds to the product over `v` of `Ring.ordFrac` (`map_finprod`; finiteness of
the support by `Ring.TameSymbol.finite_mulSupport_localFactor`). -/
theorem tameOrd_eq_finprod_ordFrac_tameSymbolAt {A : Type u} [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] (hA : ringKrullDim A = 2)
    (hfin : ∀ q : PrimeSpectrum A, q.asIdeal.height = 1 →
      Module.Finite (Localization.AtPrime q.asIdeal)
        (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (q : {q : PrimeSpectrum A // q.asIdeal.height = 1})
    [Ring.KrullDimLE 1 (A ⧸ q.1.asIdeal)]
    [Ring.KrullDimLE 1 (Localization.AtPrime q.1.asIdeal)] (f g : (FractionRing A)ˣ) :
    Ring.tameOrd A hA hfin q f g
      = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum
          (integralClosure (Localization.AtPrime q.1.asIdeal) (FractionRing A)),
        Ring.ordFrac (A ⧸ q.1.asIdeal) (K := q.1.asIdeal.ResidueField)
          (Ring.tameSymbolAt (Localization.AtPrime q.1.asIdeal) (hfin q.1 q.2) v f g) := by
  letI : IsDedekindDomain (integralClosure (Localization.AtPrime q.1.asIdeal) (FractionRing A)) :=
    Ring.TameSymbol.isDedekindDomain_integralClosure (Localization.AtPrime q.1.asIdeal)
      (FractionRing A) (hfin q.1 q.2)
  letI : IsFractionRing (integralClosure (Localization.AtPrime q.1.asIdeal) (FractionRing A))
      (FractionRing A) :=
    Ring.TameSymbol.isFractionRing_integralClosure (Localization.AtPrime q.1.asIdeal)
      (FractionRing A)
  show Ring.ordFrac (A ⧸ q.1.asIdeal) (K := q.1.asIdeal.ResidueField)
      (Ring.tameSymbol (Localization.AtPrime q.1.asIdeal) (hfin q.1 q.2) f g) = _
  unfold Ring.tameSymbol
  exact map_finprod _ (Ring.TameSymbol.finite_mulSupport_localFactor
    (Localization.AtPrime q.1.asIdeal) f g)

/-! ## The steps (B1)–(B5) -/

/-- **(B5b) Length is unchanged along a surjection of base rings**: if `I ⊆ Ann M`, then `M` has the same length
as an `A/I`-module and as an `A`-module.

Reference: standard, cf. Stacks 00IV / 02LZ; Mathlib has `Submodule.Quotient.restrictScalarsEquiv` and pieces
of `Module.length_eq_of_…` but not this form.

Proof: for `A ↠ A/I` surjective, the `A`-submodules and `A/I`-submodules of `M` correspond bijectively
(`Submodule.comap` along a surjection is an order isomorphism, Mathlib
`Submodule.restrictScalarsEmbedding` / `Submodule.orderIsoOfSurjective`), and `Module.length` is the Krull
dimension of the submodule lattice, which is preserved by order isomorphisms.

Edge cases: for `M = 0` both sides are `0`; for `I = ⊥` this is the identity; if the length is `⊤` both sides
are `⊤`. -/
theorem length_quotient_base {A : Type u} [CommRing A] (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] [Module (A ⧸ I) M] [IsScalarTower A (A ⧸ I) M] :
    Module.length (A ⧸ I) M = Module.length A M :=
  (Module.length_eq_of_surjective Ideal.Quotient.mk_surjective).symm

/-- `(B/P)/(ȳ) ≅ B/(P + yB)` as `A`-modules, hence equal lengths (used in (B3), (B5)). -/
theorem length_quotient_quotient_span_eq {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal B) (y : B) :
    Module.length A ((B ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P y}) =
      Module.length A (B ⧸ (P ⊔ Ideal.span {y})) := by
  have h : Ideal.span {Ideal.Quotient.mk P y} = (Ideal.span {y}).map (Ideal.Quotient.mkₐ A P) := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  rw [h]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ A P (Ideal.span {y})).toLinearEquiv.length_eq

/-- The Herbrand quotient on a zero quotient module is `0` (used in (B1′), (B1)). -/
theorem herbrand_mulQ_top {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B)
    (hI : I = ⊤) (a b : B) : PeriodicComplex.herbrand (mulQ A I a) (mulQ A I b) = 0 := by
  subst hI
  have : Subsingleton (B ⧸ (⊤ : Ideal B)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  have h0 : Module.length A (B ⧸ (⊤ : Ideal B)) = 0 := Module.length_eq_zero
  have h1 := PeriodicComplex.length_H_le (mulQ A (⊤ : Ideal B) a) (mulQ A ⊤ b)
  have h2 := PeriodicComplex.length_H_le (mulQ A (⊤ : Ideal B) b) (mulQ A ⊤ a)
  rw [h0, nonpos_iff_eq_zero] at h1 h2
  unfold PeriodicComplex.herbrand
  rw [h1, h2]
  rfl

/-- `ab ∉ 𝔭 ⇒ contr 𝔭 (ab) = ⊤ ⇒ Hsym = 0` ((B1), step 5). -/
theorem Hsym_eq_zero_of_not_mem {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (a b : B) (𝔭 : PrimeSpectrum B) (h : a * b ∉ 𝔭.asIdeal) : Hsym A a b 𝔭 = 0 := by
  refine herbrand_mulQ_top _ ?_ a b
  unfold contr
  rw [Ideal.span_singleton_eq_top.mpr ((IsLocalization.AtPrime.isUnit_to_map_iff _ 𝔭.asIdeal _).mpr h),
    Ideal.comap_top]


section Leaves

variable {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
  (q : PrimeSpectrum A) [Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]
  [IsDedekindDomain (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))]
  [IsFractionRing (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))
    (FractionRing A)]

/-! ### Auxiliary lemmas

The valuation-theoretic characterization of `𝔭_v`, elements of `A ∖ q` are `v`-units, elements of `C` times
elements of `A ∖ q` land in `B` (Mathlib `IsIntegral.exists_multiple_integral_of_isLocalization`, the
"surjectivity" half of Stacks 0307), and elements of `O_v` as quotients of two elements of `B` (the common
core of (B4) and (B5a)). -/

theorem valuation_lt_one_iff_mem_primeBelow
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (y : integralClosure A (FractionRing A)) :
    IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v (y : FractionRing A) < 1 ↔
      y ∈ (primeBelow A q v).asIdeal :=
  IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem v (toIcAtPrime A q y)

theorem valuation_eq_one_iff_not_mem_primeBelow
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (y : integralClosure A (FractionRing A)) :
    IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v (y : FractionRing A) = 1 ↔
      y ∉ (primeBelow A q v).asIdeal := by
  rw [← valuation_lt_one_iff_mem_primeBelow q v y]
  have h := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := FractionRing A) v
    (toIcAtPrime A q y)
  change IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v (y : FractionRing A) ≤ 1
    at h
  constructor
  · intro h1; rw [h1]; exact lt_irrefl 1
  · intro h1; exact le_antisymm h (not_lt.mp h1)

theorem valuation_algebraMap_primeCompl
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (t : A) (ht : t ∈ q.asIdeal.primeCompl) :
    IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v
      (algebraMap A (FractionRing A) t) = 1 := by
  rw [IsScalarTower.algebraMap_apply A (Localization.AtPrime q.asIdeal) (FractionRing A)]
  exact Ring.TameSymbol.valuation_unit_eq_one (Localization.AtPrime q.asIdeal) v
    (IsLocalization.map_units (Localization.AtPrime q.asIdeal) ⟨t, ht⟩).unit

omit [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]
  [IsDedekindDomain (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))]
  [IsFractionRing (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))
    (FractionRing A)] in
theorem exists_primeCompl_mul_isIntegral
    (c : integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) :
    ∃ t ∈ q.asIdeal.primeCompl, IsIntegral A (algebraMap A (FractionRing A) t * (c : FractionRing A)) := by
  obtain ⟨⟨m, hm⟩, h⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    q.asIdeal.primeCompl (Rₘ := Localization.AtPrime q.asIdeal) (c : FractionRing A) c.2
  exact ⟨m, hm, by simpa [Submonoid.smul_def, Algebra.smul_def] using h⟩

theorem exists_mul_eq_of_valuation_le_one
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (x : FractionRing A)
    (hx : IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v x ≤ 1) :
    ∃ y₁ y₂ : integralClosure A (FractionRing A), y₂ ∉ (primeBelow A q v).asIdeal ∧
      x * (y₂ : FractionRing A) = (y₁ : FractionRing A) := by
  obtain ⟨n, d, hnd⟩ := IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v x hx
  obtain ⟨t₁, ht₁, h₁⟩ := exists_primeCompl_mul_isIntegral q n
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A),
      c₂ ∉ v.asIdeal ∧ x * (c₂ : FractionRing A) = (n : FractionRing A) := ⟨d, d.2, hnd⟩
  obtain ⟨t₂, ht₂, h₂⟩ := exists_primeCompl_mul_isIntegral q c₂
  refine ⟨⟨algebraMap A (FractionRing A) t₂ *
      (algebraMap A (FractionRing A) t₁ * (n : FractionRing A)), (isIntegral_algebraMap).mul h₁⟩,
    ⟨algebraMap A (FractionRing A) t₁ *
      (algebraMap A (FractionRing A) t₂ * (c₂ : FractionRing A)),
      (isIntegral_algebraMap).mul h₂⟩, ?_, ?_⟩
  · rw [← valuation_eq_one_iff_not_mem_primeBelow]
    change IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v
      (algebraMap A (FractionRing A) t₁ *
        (algebraMap A (FractionRing A) t₂ * (c₂ : FractionRing A))) = 1
    rw [map_mul, map_mul, valuation_algebraMap_primeCompl q v t₁ ht₁,
      valuation_algebraMap_primeCompl q v t₂ ht₂, one_mul, one_mul]
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := FractionRing A) v).mpr
      hc₂.1
  · change x * (algebraMap A (FractionRing A) t₁ *
        (algebraMap A (FractionRing A) t₂ * (c₂ : FractionRing A))) =
      algebraMap A (FractionRing A) t₂ * (algebraMap A (FractionRing A) t₁ * (n : FractionRing A))
    rw [← hc₂.2]
    ring

omit [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]
  [IsDedekindDomain (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))]
  [IsFractionRing (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))
    (FractionRing A)] in
/-- **Stacks 0307**: `C = S⁻¹B`, with `S` the image of `A ∖ q` in `B` (Mathlib `IsLocalization.integralClosure`). -/
theorem isLocalization_toIcAtPrime :
    letI : Algebra (integralClosure A (FractionRing A))
        (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) :=
      (toIcAtPrime A q).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure A (FractionRing A))
      q.asIdeal.primeCompl) (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) := by
  letI : Algebra (integralClosure A (FractionRing A))
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) :=
    (toIcAtPrime A q).toAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (FractionRing A) q.asIdeal.primeCompl)
      (FractionRing A) := by
    refine IsLocalization.of_le_isUnit ?_
    rintro _ ⟨m, hm, rfl⟩
    refine isUnit_iff_ne_zero.mpr ?_
    exact (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr
      (fun h => hm (h ▸ q.asIdeal.zero_mem))
  haveI : IsScalarTower (integralClosure A (FractionRing A))
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) (FractionRing A) :=
    .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A (integralClosure A (FractionRing A))
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) :=
    .of_algebraMap_eq fun _ => rfl
  exact IsLocalization.integralClosure (R := A) (S := FractionRing A)
    (Rf := Localization.AtPrime q.asIdeal) (Sf := FractionRing A) q.asIdeal.primeCompl

omit [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]
  [IsDedekindDomain (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))]
  [IsFractionRing (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))
    (FractionRing A)] in
theorem toIcAtPrime_injective : Function.Injective (toIcAtPrime A q) :=
  fun a b h => by
    have h' : ((toIcAtPrime A q a : integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) :
      FractionRing A) = (toIcAtPrime A q b : integralClosure _ _) := congrArg Subtype.val h
    exact Subtype.ext h'

/-- `S` is disjoint from `𝔭_v`. -/
theorem disjoint_primeBelow
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))) :
    Disjoint ((Algebra.algebraMapSubmonoid (integralClosure A (FractionRing A))
      q.asIdeal.primeCompl : Submonoid _) : Set (integralClosure A (FractionRing A)))
      (primeBelow A q v).asIdeal := by
  rw [Set.disjoint_left]
  rintro _ ⟨t, ht, rfl⟩ hmem
  have hmem' : algebraMap A (integralClosure A (FractionRing A)) t ∈ (primeBelow A q v).asIdeal :=
    hmem
  rw [← valuation_lt_one_iff_mem_primeBelow] at hmem'
  have hmem := hmem'
  have h1 := valuation_algebraMap_primeCompl q v t ht
  exact (lt_irrefl (1 : WithZero (Multiplicative ℤ))) (h1 ▸ hmem)

theorem map_primeBelow
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))) :
    (primeBelow A q v).asIdeal.map (toIcAtPrime A q) = v.asIdeal := by
  letI : Algebra (integralClosure A (FractionRing A))
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) :=
    (toIcAtPrime A q).toAlgebra
  haveI := isLocalization_toIcAtPrime q
  exact IsLocalization.map_under (Algebra.algebraMapSubmonoid (integralClosure A (FractionRing A))
      q.asIdeal.primeCompl) (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))
      v.asIdeal

theorem comap_primeBelow
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))) :
    (primeBelow A q v).asIdeal.comap (algebraMap A (integralClosure A (FractionRing A)))
      = q.asIdeal := by
  have hcomp : (toIcAtPrime A q).comp (algebraMap A (integralClosure A (FractionRing A))) =
      (algebraMap (Localization.AtPrime q.asIdeal)
        (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))).comp
        (algebraMap A (Localization.AtPrime q.asIdeal)) := by
    ext a
    exact IsScalarTower.algebraMap_apply A (Localization.AtPrime q.asIdeal) (FractionRing A) a
  change Ideal.comap ((toIcAtPrime A q).comp (algebraMap A _)) v.asIdeal = q.asIdeal
  rw [hcomp, ← Ideal.comap_comap]
  obtain ⟨x, hxv, hx0⟩ : ∃ x ∈ v.asIdeal, x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact v.ne_bot (eq_bot_iff.mpr fun x hx => (Submodule.mem_bot _).mpr (hcon x hx))
  have hne : v.asIdeal.comap (algebraMap (Localization.AtPrime q.asIdeal)
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hx0 hxv (Algebra.IsIntegral.isIntegral x)
  have hmax := (Ideal.comap_isPrime (algebraMap (Localization.AtPrime q.asIdeal)
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))) v.asIdeal).isMaximal_of_ne_bot hne
  rw [IsLocalRing.eq_maximalIdeal hmax]
  exact Localization.AtPrime.under_maximalIdeal


/-- `B_{𝔭_v}` is a DVR: it is isomorphic to `C_v` (composite of two localizations), and `C` is Dedekind. -/
theorem isDiscreteValuationRing_primeBelow
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))) :
    IsDiscreteValuationRing (Localization.AtPrime (primeBelow A q v).asIdeal) := by
  letI : Algebra (integralClosure A (FractionRing A))
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) :=
    (toIcAtPrime A q).toAlgebra
  haveI := isLocalization_toIcAtPrime q
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ v.ne_bot _
  haveI : IsLocalization.AtPrime (Localization.AtPrime v.asIdeal) (primeBelow A q v).asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (M := Algebra.algebraMapSubmonoid (integralClosure A (FractionRing A)) q.asIdeal.primeCompl)
      (S := integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))
      (T := Localization.AtPrime v.asIdeal) v.asIdeal
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (IsLocalization.algEquiv (primeBelow A q v).asIdeal.primeCompl
      (Localization.AtPrime v.asIdeal) (Localization.AtPrime (primeBelow A q v).asIdeal))

/-- **(B1) Index correspondence**: `v ↦ 𝔭_v = ι⁻¹(v)` turns the sum of `Hsym` over `HeightOneSpectrum C` into
the sum over the minimal primes of `B` containing `ab` and contracting to `q`.

Reference: first paragraph of Stacks 0EAW (0EAT turns the sum over `A` into a sum over `B`); Stacks 0307
(integral closure commutes with localization).

Proof:
1. **`C = S⁻¹B`** (`S` = image of `A ∖ q` in `B`): Stacks 0307 (`isLocalization_toIcAtPrime`). Then
   `IsLocalization.orderIsoOfPrime` gives `Spec C ≃ {𝔭 ∈ Spec B | 𝔭 ∩ (A∖q) = ∅} = {𝔭 | 𝔭 ∩ A ⊆ q}`. The
   prime `𝔭 = 𝔭_v` corresponds to `v`, and `𝔭_v ∩ A = q`: `⊆` by the above; `⊇` because `v ≠ ⊥ ⇒ 𝔭_v ≠ ⊥`
   (`B → C` is injective, `C` being a localization of `B`) `⇒ 𝔭_v ∩ A ≠ 0` (`B` integral over `A`,
   `Ideal.comap_ne_bot_of_integral_mem`), and `0 ⊊ 𝔭_v ∩ A ⊆ q` with `ht q = 1` forces `𝔭_v ∩ A = q`.
2. **`v ↦ 𝔭_v` is injective**: for `C = S⁻¹B`, `v.asIdeal = (𝔭_v)·C` (`IsLocalization.map_comap`).
3. **Image**: `{𝔭 ∈ Spec B | 𝔭 ≠ ⊥, 𝔭 ∩ A = q}`. Given such `𝔭`, `𝔭·C` is a nonzero prime of `C`; take it
   as `v`.
4. **`ab ∈ 𝔭_v ⟺ 𝔭_v ∈ MinPrimes(ab)`**: `B` is an integrally closed Noetherian domain (`hB` ⇒ Noetherian;
   `integralClosure` is integrally closed), and the height-one primes containing `ab ≠ 0` are exactly the
   minimal primes of `(ab)` (`Ideal.minimalPrimes` and Krull's principal ideal theorem); `𝔭_v` has height `1`
   (`C` is one-dimensional and `ht(𝔭_v) = ht(v)`).
5. **Terms with `v(ab) = 1` contribute `0`**: then `ab ∉ 𝔭_v`, so `abB_{𝔭_v} = B_{𝔭_v}`,
   `contr 𝔭_v (ab) = ⊤`, `B ⧸ ⊤ = 0`, and `PeriodicComplex.herbrand` vanishes on the zero module, i.e.
   `Hsym A a b 𝔭_v = 0`. So the support of the left-hand side lies in `MinPrimes`, and the two sides agree
   termwise.

Edge cases: if `a` or `b` is a unit of `A`, all corresponding `v` satisfy `v(a) = 1` and both sides still
agree (`MinPrimes(ab)` is then determined by the other element); `a = b` is not special; if there is only one
prime above `q`, this is one term against one term; `A` a DVR cannot happen (`dim A = 2`); non-algebraically
closed residue fields do not affect this step; `B` is a domain, so there are no zero divisors. -/
theorem finsum_Hsym_primeBelow_eq
    (hB : Module.Finite A (integralClosure A (FractionRing A)))
    (hfinq : Module.Finite (Localization.AtPrime q.asIdeal)
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (hq : q.asIdeal.height = 1) (hA : ringKrullDim A = 2) (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∑ᶠ v : IsDedekindDomain.HeightOneSpectrum
        (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)),
      Hsym A (algebraMap A (integralClosure A (FractionRing A)) a)
        (algebraMap A (integralClosure A (FractionRing A)) b) (primeBelow A q v))
      = ∑ᶠ 𝔭 : {𝔭 : KeyLemma.MinPrimes
            (algebraMap A (integralClosure A (FractionRing A)) a *
              algebraMap A (integralClosure A (FractionRing A)) b) //
            𝔭.1.asIdeal.comap (algebraMap A (integralClosure A (FractionRing A))) = q.asIdeal},
          Hsym A (algebraMap A (integralClosure A (FractionRing A)) a)
            (algebraMap A (integralClosure A (FractionRing A)) b) 𝔭.1.1 := by
  classical
  letI : Algebra (integralClosure A (FractionRing A))
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) :=
    (toIcAtPrime A q).toAlgebra
  haveI := isLocalization_toIcAtPrime q
  set t := algebraMap A (integralClosure A (FractionRing A)) a *
    algebraMap A (integralClosure A (FractionRing A)) b with ht
  have htK : (t : FractionRing A) = algebraMap A (FractionRing A) (a * b) := by
    rw [ht, map_mul]; rfl
  have hιt : toIcAtPrime A q t ≠ 0 := by
    intro h0
    have : (t : FractionRing A) = 0 := congrArg Subtype.val h0
    rw [htK] at this
    exact mul_ne_zero ha hb ((map_eq_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mp this)
  set S := Algebra.algebraMapSubmonoid (integralClosure A (FractionRing A)) q.asIdeal.primeCompl
  have hdisj : ∀ 𝔭 : PrimeSpectrum (integralClosure A (FractionRing A)),
      𝔭.asIdeal.comap (algebraMap A (integralClosure A (FractionRing A))) = q.asIdeal →
        Disjoint (S : Set (integralClosure A (FractionRing A))) 𝔭.asIdeal := by
    intro 𝔭 h
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hm
    exact hs (h ▸ (hm : s ∈ 𝔭.asIdeal.comap (algebraMap A (integralClosure A (FractionRing A)))))
  have hcm : ∀ 𝔭 : PrimeSpectrum (integralClosure A (FractionRing A)),
      𝔭.asIdeal.comap (algebraMap A (integralClosure A (FractionRing A))) = q.asIdeal →
        (𝔭.asIdeal.map (toIcAtPrime A q)).comap (toIcAtPrime A q) = 𝔭.asIdeal := fun 𝔭 h =>
    IsLocalization.under_map_of_isPrime_disjoint S
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) 𝔭.isPrime (hdisj 𝔭 h)
  have hne : ∀ I : Ideal (integralClosure A (FractionRing A)), t ∈ I →
      I.map (toIcAtPrime A q) ≠ ⊥ := fun I hI h0 =>
    hιt ((Ideal.mem_bot).mp (h0 ▸ Ideal.mem_map_of_mem _ hI))
  have htmem : ∀ 𝔭 : KeyLemma.MinPrimes t, t ∈ 𝔭.1.asIdeal := fun 𝔭 =>
    𝔭.2.1.2 (Ideal.mem_span_singleton_self t)
  let e : {𝔭 : KeyLemma.MinPrimes t //
      𝔭.1.asIdeal.comap (algebraMap A (integralClosure A (FractionRing A))) = q.asIdeal} →
      IsDedekindDomain.HeightOneSpectrum
        (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) := fun x =>
    ⟨x.1.1.asIdeal.map (toIcAtPrime A q),
      IsLocalization.isPrime_of_isPrime_disjoint S _ _ x.1.1.isPrime (hdisj _ x.2),
      hne _ (htmem x.1)⟩
  have he : ∀ x, primeBelow A q (e x) = x.1.1 := fun x =>
    PrimeSpectrum.ext (hcm x.1.1 x.2)
  set T : Set (IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))) :=
    {v | t ∈ (primeBelow A q v).asIdeal} with hT
  have hsupp : Function.support (fun v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) =>
      Hsym A (algebraMap A (integralClosure A (FractionRing A)) a)
        (algebraMap A (integralClosure A (FractionRing A)) b) (primeBelow A q v)) ⊆ T := by
    intro v hv
    by_contra h
    exact hv (Hsym_eq_zero_of_not_mem _ _ _ h)
  have hmin : ∀ v ∈ T, (primeBelow A q v).asIdeal ∈ (Ideal.span {t}).minimalPrimes := by
    intro v hv
    refine ⟨⟨(primeBelow A q v).isPrime, (Ideal.span_singleton_le_iff_mem _).mpr hv⟩, ?_⟩
    rintro 𝔮 ⟨h𝔮, hle⟩ h𝔮P
    have hd : Disjoint (S : Set (integralClosure A (FractionRing A))) 𝔮 :=
      (disjoint_primeBelow q v).mono_right h𝔮P
    have hprime := IsLocalization.isPrime_of_isPrime_disjoint S
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) 𝔮 h𝔮 hd
    have hmax := hprime.isMaximal (hne 𝔮 (hle (Ideal.mem_span_singleton_self t)))
    have heq : 𝔮.map (toIcAtPrime A q) = v.asIdeal :=
      hmax.eq_of_le v.isPrime.ne_top (by rw [← map_primeBelow q v]; exact Ideal.map_mono h𝔮P)
    have h2 := IsLocalization.under_map_of_isPrime_disjoint S
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) h𝔮 hd
    change (𝔮.map (toIcAtPrime A q)).comap (toIcAtPrime A q) = 𝔮 at h2
    rw [heq] at h2
    exact h2 ▸ le_refl _
  have hbij : Set.BijOn e Set.univ T := by
    refine ⟨fun x _ => ?_, fun x _ y _ hxy => ?_, fun v hv => ?_⟩
    · show t ∈ (primeBelow A q (e x)).asIdeal
      rw [he]; exact htmem x.1
    · have := congrArg (primeBelow A q) hxy
      rw [he, he] at this
      exact Subtype.ext (Subtype.ext this)
    · refine ⟨⟨⟨primeBelow A q v, hmin v hv⟩, comap_primeBelow q v⟩, Set.mem_univ _, ?_⟩
      exact IsDedekindDomain.HeightOneSpectrum.ext (map_primeBelow q v)
  have key := finsum_mem_eq_of_bijOn e hbij
    (f := fun x => Hsym A (algebraMap A (integralClosure A (FractionRing A)) a)
      (algebraMap A (integralClosure A (FractionRing A)) b) x.1.1)
    (g := fun v => Hsym A (algebraMap A (integralClosure A (FractionRing A)) a)
      (algebraMap A (integralClosure A (FractionRing A)) b) (primeBelow A q v))
    (fun x _ => by simp only [he])
  rw [finsum_mem_univ, finsum_mem_def, Set.indicator_eq_self.mpr hsupp] at key
  exact key.symm

/-- **(B1′) Finite support**: only finitely many `v` have `Hsym A a b 𝔭_v ≠ 0`.

Proof: by (B1) step 5, `Hsym A a b 𝔭_v ≠ 0` implies `ab ∈ 𝔭_v`, i.e. `v(ab) < 1`, and
`Ring.TameSymbol.finite_valuation_ne_one` says there are only finitely many such `v` (applied to `ab ≠ 0`).
(Alternatively, from `KeyLemma.finite_MinPrimes` and the injectivity in (B1).)

Edge cases: `ab` a unit ⇒ the support is empty; likewise when `MinPrimes` is empty. -/
theorem finite_support_Hsym_primeBelow
    (hfinq : Module.Finite (Localization.AtPrime q.asIdeal)
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Function.support fun v : IsDedekindDomain.HeightOneSpectrum
        (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) =>
      Hsym A (algebraMap A (integralClosure A (FractionRing A)) a)
        (algebraMap A (integralClosure A (FractionRing A)) b) (primeBelow A q v)).Finite := by
  have hab : algebraMap A (FractionRing A) (a * b) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr (mul_ne_zero ha hb)
  refine (Ring.TameSymbol.finite_valuation_ne_one (Localization.AtPrime q.asIdeal)
    (K := FractionRing A) (Units.mk0 _ hab)).subset ?_
  intro v hv
  rw [Function.mem_support] at hv
  have hmem : algebraMap A (integralClosure A (FractionRing A)) a *
      algebraMap A (integralClosure A (FractionRing A)) b ∈ (primeBelow A q v).asIdeal := by
    by_contra h
    exact hv (Hsym_eq_zero_of_not_mem _ _ _ h)
  rw [← valuation_lt_one_iff_mem_primeBelow] at hmem
  have hco : ((algebraMap A (integralClosure A (FractionRing A)) a *
      algebraMap A (integralClosure A (FractionRing A)) b : integralClosure A (FractionRing A)) :
        FractionRing A) = algebraMap A (FractionRing A) (a * b) := by
    rw [map_mul]; rfl
  rw [hco] at hmem
  exact hmem.ne

/-- **(B2) Symbolic powers ↔ valuation**: for `x ∈ B`, `x ∈ 𝔭_v^{(n)} ⟺ v(x) ≤ exp(−n)`.

Reference: third paragraph of Stacks 0EAW (`(M_i)_{𝔮_i} = B_{𝔮_i}/π^{e+f}`); Mathlib
`IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring`.

Proof: `symbPow 𝔭_v n` is the contraction of `(𝔪_{B_{𝔭_v}})ⁿ`. By (B1) step 1, `C = S⁻¹B`, so
`B_{𝔭_v} = C_v` (composite of two localizations), and Mathlib's
`valuationSubringAtPrime_eq_valuationSubring` says `C_v = O_v = {v ≤ 1}`, a DVR with maximal ideal `{v < 1}`,
whose `n`-th power is `{v ≤ exp(−n)}` (the `intValuation` characterization around
`IsDedekindDomain.HeightOneSpectrum.valuation_le_pow_iff`). Contracting to `B` gives the result.

Edge cases: for `n = 0` both sides always hold (`v(x) ≤ 1` for `x ∈ B`); for `x = 0` both sides hold; if
`B_{𝔭_v}` is already `O_v` (the case where `R` is a DVR) nothing changes. -/
theorem mem_symbPow_primeBelow_iff
    (hfinq : Module.Finite (Localization.AtPrime q.asIdeal)
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (x : integralClosure A (FractionRing A)) (n : ℕ) :
    x ∈ symbPow (primeBelow A q v).asIdeal n ↔
      IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v (x : FractionRing A)
        ≤ WithZero.exp (-(n : ℤ)) := by
  letI : Algebra (integralClosure A (FractionRing A))
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) :=
    (toIcAtPrime A q).toAlgebra
  haveI := isLocalization_toIcAtPrime q
  have hinjB : Function.Injective (algebraMap (integralClosure A (FractionRing A))
      (Localization.AtPrime (primeBelow A q v).asIdeal)) :=
    IsLocalization.injective (Localization.AtPrime (primeBelow A q v).asIdeal)
      (primeBelow A q v).asIdeal.primeCompl_le_nonZeroDivisors
  have hvalC : ∀ c : integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A),
      IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v (c : FractionRing A) =
        v.intValuation c := fun c =>
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := FractionRing A) v c
  have hval : ∀ j ∈ (primeBelow A q v).asIdeal ^ n,
      IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v (j : FractionRing A)
        ≤ WithZero.exp (-(n : ℤ)) := by
    intro j hj
    have h1 : toIcAtPrime A q j ∈ ((primeBelow A q v).asIdeal.map (toIcAtPrime A q)) ^ n := by
      rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hj
    rw [map_primeBelow] at h1
    rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem] at h1
    rw [show (j : FractionRing A) = ((toIcAtPrime A q j :
      integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)) : FractionRing A) from rfl,
      hvalC]
    exact h1
  unfold symbPow
  rw [Ideal.mem_comap, ← IsLocalization.AtPrime.map_eq_maximalIdeal (primeBelow A q v).asIdeal
    (Localization.AtPrime (primeBelow A q v).asIdeal), ← Ideal.map_pow,
    IsLocalization.mem_map_algebraMap_iff (primeBelow A q v).asIdeal.primeCompl]
  constructor
  · rintro ⟨⟨⟨j, hj⟩, ⟨s, hs⟩⟩, h⟩
    have h' : x * s = j := hinjB (by rw [map_mul]; exact h)
    have hs1 := (valuation_eq_one_iff_not_mem_primeBelow q v s).mpr hs
    have hj' := hval j hj
    rw [← h', MulMemClass.coe_mul, map_mul, hs1, mul_one] at hj'
    exact hj'
  · intro hx
    have hι : toIcAtPrime A q x ∈ v.asIdeal ^ n := by
      rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, ← hvalC]; exact hx
    rw [← map_primeBelow q v, ← Ideal.map_pow] at hι
    obtain ⟨⟨⟨j, hj⟩, ⟨s, hs⟩⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff
      (Algebra.algebraMapSubmonoid (integralClosure A (FractionRing A)) q.asIdeal.primeCompl)
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))).mp hι
    have h' : x * s = j := toIcAtPrime_injective q (by rw [map_mul]; exact h)
    have hsP : s ∉ (primeBelow A q v).asIdeal := fun hm =>
      Set.disjoint_left.mp (disjoint_primeBelow q v) hs hm
    exact ⟨⟨⟨j, hj⟩, ⟨s, hsP⟩⟩, by rw [← map_mul, h']⟩

/-- The algebra structure `A/q → B/𝔭_v` (`𝔭_v ∩ A = q`). -/
abbrev algebraQuotPrimeBelow
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))) :
    Algebra (A ⧸ q.asIdeal) (integralClosure A (FractionRing A) ⧸ (primeBelow A q v).asIdeal) :=
  Ideal.Quotient.algebraQuotientOfLEComap (comap_primeBelow q v).ge

theorem quot_primeBelow_facts (hB : Module.Finite A (integralClosure A (FractionRing A)))
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A))) :
    letI := algebraQuotPrimeBelow q v
    IsScalarTower A (A ⧸ q.asIdeal) (integralClosure A (FractionRing A) ⧸ (primeBelow A q v).asIdeal) ∧
    FaithfulSMul (A ⧸ q.asIdeal) (integralClosure A (FractionRing A) ⧸ (primeBelow A q v).asIdeal) ∧
    Module.Finite (A ⧸ q.asIdeal) (integralClosure A (FractionRing A) ⧸ (primeBelow A q v).asIdeal) := by
  letI := algebraQuotPrimeBelow q v
  have ht : IsScalarTower A (A ⧸ q.asIdeal)
      (integralClosure A (FractionRing A) ⧸ (primeBelow A q v).asIdeal) :=
    .of_algebraMap_eq fun _ => rfl
  refine ⟨ht, ?_, ?_⟩
  · exact (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (Ideal.quotientMap_injective' (comap_primeBelow q v).le)
  · haveI : Module.Finite A (integralClosure A (FractionRing A) ⧸ (primeBelow A q v).asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ A (primeBelow A q v).asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    exact Module.Finite.of_restrictScalars_finite A _ _

/-- **(B3) Finite length**: `y ∉ 𝔭_v ⇒ length_A(B/(𝔭_v + yB)) < ∞` — the hypothesis `hfl` of
`KeyLemma.Hsym_eq_lam_sub`.

Reference: third paragraph of Stacks 0EAW; `Ring.length_quotient_span_singleton_ne_top` (module
`OrdNormEqLength`).

Proof: `B/𝔭_v` is a domain, finite over `A/q′` (`q′ = 𝔭_v ∩ A`; `hB` is preserved by quotients). By (B1)
step 1, `q′ = q` with `ht q = 1`, so `A/q` is a one-dimensional Noetherian local domain,
`Ring.KrullDimLE 1 (A ⧸ q)` (`Ring.krullDimLE_one_quotient_of_height_eq_one`). `ȳ ≠ 0` (`y ∉ 𝔭_v`), so
`Ring.length_quotient_span_singleton_ne_top (A ⧸ q) (B := B ⧸ 𝔭_v) hȳ` gives
`length_{A/q}((B/𝔭_v)/(ȳ)) < ∞`; then (B5b) `length_{A/q} = length_A` and the ring isomorphism
`(B/𝔭_v)/(ȳ) ≅ B/(𝔭_v + yB)` (`Ideal.quotientQuotientEquivQuotientSup`) give the result.

Edge cases: `y` a unit ⇒ the quotient is the zero module, of length `0`; `𝔭_v` maximal cannot happen
(`𝔭_v ∩ A = q ≠ 𝔪_A`); `A/q` a field is excluded by `dim A = 2`. -/
theorem lam_ne_top_primeBelow
    (hB : Module.Finite A (integralClosure A (FractionRing A)))
    (hfinq : Module.Finite (Localization.AtPrime q.asIdeal)
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (hq : q.asIdeal.height = 1) (hA : ringKrullDim A = 2)
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (y : integralClosure A (FractionRing A)) (hy : y ∉ (primeBelow A q v).asIdeal) :
    Module.length A (integralClosure A (FractionRing A) ⧸
        ((primeBelow A q v).asIdeal ⊔ Ideal.span {y})) ≠ ⊤ := by
  haveI : Ring.KrullDimLE 1 (A ⧸ q.asIdeal) := Ring.krullDimLE_one_quotient_of_height_eq_one hA q hq
  letI := algebraQuotPrimeBelow q v
  obtain ⟨h1, h2, h3⟩ := quot_primeBelow_facts q hB v
  have hy0 : Ideal.Quotient.mk (primeBelow A q v).asIdeal y ≠ 0 :=
    fun h => hy (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have key := Ring.length_quotient_span_singleton_ne_top (A ⧸ q.asIdeal)
    (B := integralClosure A (FractionRing A) ⧸ (primeBelow A q v).asIdeal)
    (y := Ideal.Quotient.mk (primeBelow A q v).asIdeal y) hy0
  rw [length_quotient_base, length_quotient_quotient_span_eq] at key
  exact key

/-- **(B4) Units as fractions**: `z ∈ K` with `v(z) = 1 ⇒ z = y₁/y₂` with `y₁, y₂ ∈ B ∖ 𝔭_v`.

Reference: fourth paragraph of Stacks 0EAW (writing the local factor of `∂` as a quotient of two elements
of `B`).

Proof: by (B1) step 1, `C = S⁻¹B`, and `O_v = C_v` ((B2)). `v(z) = 1` says `z` is a unit of `O_v`, so
`z ∈ C_v` can be written as `c/c′` with `c, c′ ∈ C ∖ v`; write `c`, `c′` as `b/s`, `b′/s′`
(`s, s′ ∈ A ∖ q ⊆ B ∖ 𝔭_v`) and cancel to get `z = (b s′)/(b′ s)`, with numerator and denominator in `B`
and outside `𝔭_v` (`v(z) = 1` guarantees this for the numerator too).

Use: for `z = Ring.TameSymbol.symbolElt (v.valuation K) f g = (−1)^{ef}·f^{e′}/g^{e}` one gets
`y₁·b^e = (−1)^{ef}·y₂·a^f`, which is exactly the hypothesis `hy` of `KeyLemma.Hsym_eq_lam_sub`.

Edge cases: for `z = 1` take `y₁ = y₂ = 1`; `v(z) = 1` with `z ∉ B` is the typical case (this is the content
of the lemma); if `a` or `b` is a unit, `e` or `f` is `0`, the fraction degenerates and the conclusion still
holds. -/
theorem exists_num_den_of_valuation_eq_one
    (hfinq : Module.Finite (Localization.AtPrime q.asIdeal)
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (z : FractionRing A)
    (hz : IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v z = 1) :
    ∃ y₁ y₂ : integralClosure A (FractionRing A),
      y₁ ∉ (primeBelow A q v).asIdeal ∧ y₂ ∉ (primeBelow A q v).asIdeal ∧
        z * (y₂ : FractionRing A) = (y₁ : FractionRing A) := by
  obtain ⟨y₁, y₂, hy₂, h⟩ := exists_mul_eq_of_valuation_le_one q v z hz.le
  refine ⟨y₁, y₂, ?_, hy₂, h⟩
  rw [← valuation_eq_one_iff_not_mem_primeBelow] at hy₂ ⊢
  rw [← h, map_mul, hz, hy₂, one_mul]

/-- **(B5a) `κ(O_v)` is the fraction field of `B/𝔭_v` — the "write as a fraction" half**: every element
of `κ(O_v)` is a quotient of residue classes of two elements of `B`, with denominator not in `𝔭_v`.

Reference: the identification `κ(𝔭) = Frac(B/𝔭)` implicit in the use of 02MI in the third paragraph of
Stacks 0EAW; Stacks 0307.

Proof: `O_v = C_v` ((B2)), so `κ(O_v)` is the fraction field of `C/v`, which is `C/v` itself (`C` is
one-dimensional and `v` maximal, so `C/v` is a field). By (B1) step 1, `C = S⁻¹B`, hence
`C/v = S̄⁻¹(B/𝔭_v)` where `S̄` is the image of `A ∖ q` in `B/𝔭_v`; so every element of `C/v` is `b̄/s̄`
with `s̄ ≠ 0`. Absorbing the denominator of `s̄` into the numerator gives the result.

Together with (B5a′) this yields the instance `IsFractionRing (B ⧸ 𝔭_v) (IsLocalRing.ResidueField O_v)`
(descend the composite of `toValuationSubringIC` and `IsLocalRing.residue` to `B/𝔭_v` with
`Ideal.Quotient.lift`; (B5a′) says the kernel is exactly `𝔭_v`).

Edge cases: `κ(O_v)` is a field, the zero element is `y₁ = 0, y₂ = 1`; finite or inseparable residue fields
make no difference. -/
theorem exists_residue_div
    (hfinq : Module.Finite (Localization.AtPrime q.asIdeal)
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (x : IsLocalRing.ResidueField
      (IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v).valuationSubring) :
    ∃ y₁ y₂ : integralClosure A (FractionRing A), y₂ ∉ (primeBelow A q v).asIdeal ∧
      x * IsLocalRing.residue _ (toValuationSubringIC A q v y₂)
        = IsLocalRing.residue _ (toValuationSubringIC A q v y₁) := by
  obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨y₁, y₂, hy₂, h⟩ := exists_mul_eq_of_valuation_le_one q v (o : FractionRing A) o.2
  refine ⟨y₁, y₂, hy₂, ?_⟩
  rw [← map_mul]
  congr 1
  exact Subtype.ext h

/-- **(B5a′) The kernel is exactly `𝔭_v`**: for `y ∈ B`, the residue class of `y` in `κ(O_v)` is zero iff
`y ∈ 𝔭_v`.

Proof: the zero of `κ(O_v)` corresponds to the maximal ideal `{v < 1}` of `O_v`; for `y ∈ B ⊆ C`,
`v(y) < 1 ⟺ ι(y) ∈ v.asIdeal` (Mathlib `IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem`)
`⟺ y ∈ 𝔭_v` (definition of `primeBelow`).

Edge cases: for `y = 0` both sides hold; for `y` a unit of `B` both sides fail. -/
theorem residue_toValuationSubringIC_eq_zero_iff
    (hfinq : Module.Finite (Localization.AtPrime q.asIdeal)
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (y : integralClosure A (FractionRing A)) :
    IsLocalRing.residue _ (toValuationSubringIC A q v y) = 0 ↔ y ∈ (primeBelow A q v).asIdeal := by
  rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  exact valuation_lt_one_iff_mem_primeBelow q v y

set_option synthInstance.maxHeartbeats 200000 in
/-- **(B5) The `ord` of the norm is a length**: for `y ∈ B` with `v(y) = 1` (i.e. `y ∉ 𝔭_v`),
`ordFrac_{A/q}(Norm_{κ(O_v)/κ(q)}(ȳ)) = exp(lam A 𝔭_v y)`.

Reference: **Stacks 02MI**, `Ring.ordFrac_norm_eq_exp_length`.

Proof: apply 02MI with `(A, B, K, L) := (A/q, B/𝔭_v, κ(q), κ(O_v))`. Required instances:
* `Ring.KrullDimLE 1 (A ⧸ q)`: `Ring.krullDimLE_one_quotient_of_height_eq_one hA q hq`;
* `Module.Finite (A ⧸ q) (B ⧸ 𝔭_v)`: `hB` is preserved along the surjections `B ↠ B/𝔭_v`, `A ↠ A/q`;
* `IsFractionRing (A ⧸ q) κ(q)`: Mathlib (the definition of `Ideal.ResidueField`);
* `IsFractionRing (B ⧸ 𝔭_v) κ(O_v)`: built from (B5a) + (B5a′);
* `FaithfulSMul (A ⧸ q) (B ⧸ 𝔭_v)`: `A/q → B/𝔭_v` is injective (`𝔭_v ∩ A = q`, (B1) step 1).
02MI gives `ordFrac_{A/q}(Norm ȳ) = exp(length_{A/q}((B/𝔭_v)/(ȳ)))`; by the ring isomorphism
`(B/𝔭_v)/(ȳ) ≅ B/(𝔭_v + yB)` and (B5b) `length_{A/q} = length_A`, the right-hand side is
`exp (lam A 𝔭_v y)` (definition of `lam`).

Edge cases: `y` a unit of `B` ⇒ both sides are `exp 0 = 1`; for finite or inseparable residue fields 02MI
still holds (it uses determinants, no separability); if `κ(q) = κ(O_v)` (residue degree `1` over `𝔭_v`)
the norm is the identity. -/
theorem ordFrac_norm_residue_eq_exp_lam
    [Ring.KrullDimLE 1 (A ⧸ q.asIdeal)]
    (hB : Module.Finite A (integralClosure A (FractionRing A)))
    (hfinq : Module.Finite (Localization.AtPrime q.asIdeal)
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (hq : q.asIdeal.height = 1) (hA : ringKrullDim A = 2)
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (y : integralClosure A (FractionRing A)) (hy : y ∉ (primeBelow A q v).asIdeal) :
    letI : IsLocalHom (Ring.TameSymbol.toValuationSubring (Localization.AtPrime q.asIdeal) v) :=
      Ring.TameSymbol.isLocalHom_toValuationSubring (Localization.AtPrime q.asIdeal) v
    letI : Algebra (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
        (IsLocalRing.ResidueField
          (IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v).valuationSubring) :=
      (IsLocalRing.ResidueField.map
        (Ring.TameSymbol.toValuationSubring (Localization.AtPrime q.asIdeal) v)).toAlgebra
    Ring.ordFrac (A ⧸ q.asIdeal) (K := q.asIdeal.ResidueField)
        (Algebra.norm (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
          (IsLocalRing.residue _ (toValuationSubringIC A q v y)))
      = WithZero.exp ((lam A (primeBelow A q v).asIdeal y : ℕ) : ℤ) := by
  letI hloc : IsLocalHom (Ring.TameSymbol.toValuationSubring (Localization.AtPrime q.asIdeal) v) :=
    Ring.TameSymbol.isLocalHom_toValuationSubring (Localization.AtPrime q.asIdeal) v
  letI algKL : Algebra (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
      (IsLocalRing.ResidueField
        (IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v).valuationSubring) :=
    (IsLocalRing.ResidueField.map
      (Ring.TameSymbol.toValuationSubring (Localization.AtPrime q.asIdeal) v)).toAlgebra
  letI := algebraQuotPrimeBelow q v
  obtain ⟨h1, h2, h3⟩ := quot_primeBelow_facts q hB v
  let f : integralClosure A (FractionRing A) ⧸ (primeBelow A q v).asIdeal →+*
      IsLocalRing.ResidueField
        (IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v).valuationSubring :=
    Ideal.Quotient.lift (primeBelow A q v).asIdeal
      ((IsLocalRing.residue _).comp (toValuationSubringIC A q v))
      (fun y hy => (residue_toValuationSubringIC_eq_zero_iff q hfinq v y).mpr hy)
  have hf : ∀ y, f (Ideal.Quotient.mk _ y) = IsLocalRing.residue _ (toValuationSubringIC A q v y) :=
    fun _ => rfl
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((residue_toValuationSubringIC_eq_zero_iff q hfinq v y).mp hz)
  letI : Algebra (integralClosure A (FractionRing A) ⧸ (primeBelow A q v).asIdeal)
      (IsLocalRing.ResidueField
        (IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v).valuationSubring) :=
    f.toAlgebra
  haveI : IsFractionRing (integralClosure A (FractionRing A) ⧸ (primeBelow A q v).asIdeal)
      (IsLocalRing.ResidueField
        (IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v).valuationSubring) := by
    refine (isLocalization_iff _ _).mpr ⟨fun z => ?_, fun z => ?_, fun {x y} h => ?_⟩
    · exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff f hfinj).mpr (nonZeroDivisors.coe_ne_zero z))
    · obtain ⟨y₁, y₂, hy₂, h⟩ := exists_residue_div q hfinq v z
      have hy₂' : Ideal.Quotient.mk (primeBelow A q v).asIdeal y₂ ∈
          nonZeroDivisors (integralClosure A (FractionRing A) ⧸ (primeBelow A q v).asIdeal) :=
        mem_nonZeroDivisors_of_ne_zero (fun h0 => hy₂ (Ideal.Quotient.eq_zero_iff_mem.mp h0))
      exact ⟨(Ideal.Quotient.mk _ y₁, ⟨_, hy₂'⟩), h⟩
    · exact ⟨1, by rw [hfinj h]⟩
  letI : Algebra (A ⧸ q.asIdeal)
      (IsLocalRing.ResidueField
        (IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v).valuationSubring) :=
    ((algebraMap (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) _).comp
      (algebraMap (A ⧸ q.asIdeal) q.asIdeal.ResidueField)).toAlgebra
  haveI : IsScalarTower (A ⧸ q.asIdeal) q.asIdeal.ResidueField
      (IsLocalRing.ResidueField
        (IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v).valuationSubring) :=
    .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (A ⧸ q.asIdeal)
      (integralClosure A (FractionRing A) ⧸ (primeBelow A q v).asIdeal)
      (IsLocalRing.ResidueField
        (IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v).valuationSubring) :=
    by
      refine IsScalarTower.of_algebraMap_eq (R := A ⧸ q.asIdeal)
        (S := integralClosure A (FractionRing A) ⧸ (primeBelow A q v).asIdeal)
        (A := IsLocalRing.ResidueField
          (IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v).valuationSubring)
        fun x => ?_
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := q.asIdeal) x
      show IsLocalRing.ResidueField.map
          (Ring.TameSymbol.toValuationSubring (Localization.AtPrime q.asIdeal) v)
          (algebraMap (A ⧸ q.asIdeal) q.asIdeal.ResidueField (Ideal.Quotient.mk _ a)) =
        f (Ideal.Quotient.mk _ (algebraMap A (integralClosure A (FractionRing A)) a))
      rw [Ideal.algebraMap_quotient_residueField_mk, hf,
        IsScalarTower.algebraMap_apply A (Localization.AtPrime q.asIdeal) q.asIdeal.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ResidueField.map_residue]
      congr 1
      exact Subtype.ext (IsScalarTower.algebraMap_apply A (Localization.AtPrime q.asIdeal)
        (FractionRing A) a).symm
  have hy0 : Ideal.Quotient.mk (primeBelow A q v).asIdeal y ≠ 0 :=
    fun h => hy (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have key := Ring.ordFrac_norm_eq_exp_length (A := A ⧸ q.asIdeal)
    (B := integralClosure A (FractionRing A) ⧸ (primeBelow A q v).asIdeal)
    (K := q.asIdeal.ResidueField)
    (L := IsLocalRing.ResidueField
        (IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v).valuationSubring) hy0
  rw [length_quotient_base, length_quotient_quotient_span_eq] at key
  exact key

end Leaves

/-- **(B6b) The factor at each `v`**: for every `v`,
`ordFrac_{A/q}(tameSymbolAt R hfinq v ā b̄) = exp(−Hsym A a b 𝔭_v)`.

Reference: third and fourth paragraphs of Stacks 0EAW (`e_A(M_i, a, b) = −ord(∂(a,b))`); assembled from
(B2)(B3)(B4)(B5).

Proof:
1. `tameSymbolAt R hfinq v f g = Ring.TameSymbol.localFactor R v f g
   = Norm_{κ(O_v)/κ(q)}(residue O_v (symbolElt (v.valuation K) f g))` (unfold the definitions).
2. Let `e := ordv (v.valuation K) f`, `f′ := ordv (v.valuation K) g`. `symbolElt` has valuation `1` (this is
   what the proof of `Ring.TameSymbol.symbol_mem_valuationSubring` computes), so by (B4) it is `y₁/y₂` with
   `y₁, y₂ ∈ B ∖ 𝔭_v` and `y₁·b^{e} = (−1)^{e·f′}·y₂·a^{f′}`.
3. Norm and residue class are multiplicative, so the value in step 1 is `Norm(ȳ₁)/Norm(ȳ₂)`; `ordFrac` is
   multiplicative (`map_div₀`), so the left-hand side is `exp(lam y₁ − lam y₂)` (by (B5) twice).
4. (B2) translates "`a ∈ 𝔭_v^{(e)} ∖ 𝔭_v^{(e+1)}`" into `v(a) = exp(−e)`, likewise for `b`; (B3) gives `hfl`.
   Then `KeyLemma.Hsym_eq_lam_sub` (assembled from the `HerbrandSymbPow` family) gives
   `Hsym A a b 𝔭_v = lam y₂ − lam y₁`. Adding the two equations gives the result.

Edge cases: if `v(ab) = 1` (i.e. `e = f′ = 0`) then `symbolElt = 1` (`Ring.TameSymbol.symbolElt_eq_one`), the
left-hand side is `ordFrac 1 = 1 = exp 0`, and on the right `Hsym = 0` ((B1), step 5); if `a` or `b` is a unit
of `A` the corresponding `e` or `f′` is `0` and (B4) still gives a fraction representation; if `B_{𝔭_v}` is
already `O_v` nothing changes. -/
theorem ordFrac_tameSymbolAt_eq_exp_neg_Hsym {A : Type u} [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] (hA : ringKrullDim A = 2)
    (q : {q : PrimeSpectrum A // q.asIdeal.height = 1})
    [Ring.KrullDimLE 1 (A ⧸ q.1.asIdeal)]
    [Ring.KrullDimLE 1 (Localization.AtPrime q.1.asIdeal)]
    [IsDedekindDomain (integralClosure (Localization.AtPrime q.1.asIdeal) (FractionRing A))]
    [IsFractionRing (integralClosure (Localization.AtPrime q.1.asIdeal) (FractionRing A))
      (FractionRing A)]
    (hB : Module.Finite A (integralClosure A (FractionRing A)))
    (hfinq : Module.Finite (Localization.AtPrime q.1.asIdeal)
      (integralClosure (Localization.AtPrime q.1.asIdeal) (FractionRing A)))
    (a b : A) (ha : a ≠ 0) (hb : b ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.1.asIdeal) (FractionRing A))) :
    Ring.ordFrac (A ⧸ q.1.asIdeal) (K := q.1.asIdeal.ResidueField)
        (Ring.tameSymbolAt (Localization.AtPrime q.1.asIdeal) hfinq v
          (Units.mk0 (algebraMap A (FractionRing A) a)
            ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr ha))
          (Units.mk0 (algebraMap A (FractionRing A) b)
            ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr hb)))
      = WithZero.exp (-(Hsym A (algebraMap A (integralClosure A (FractionRing A)) a)
          (algebraMap A (integralClosure A (FractionRing A)) b) (primeBelow A q.1 v))) := by
  haveI := hB
  haveI := isDiscreteValuationRing_primeBelow q.1 v
  set f : (FractionRing A)ˣ := Units.mk0 (algebraMap A (FractionRing A) a)
    ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr ha) with hf
  set g : (FractionRing A)ˣ := Units.mk0 (algebraMap A (FractionRing A) b)
    ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr hb) with hg
  set val := IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v with hval
  -- val x = exp (-(ordv x))
  have hvo : ∀ x : (FractionRing A)ˣ, val (x : FractionRing A) =
      WithZero.exp (-(Ring.TameSymbol.ordv val x)) := by
    intro x
    unfold Ring.TameSymbol.ordv
    rw [neg_neg]
    exact (WithZero.coe_unzero _).symm
  -- ordv of a, b are ≥ 0
  have hnn : ∀ c : A, ∀ hc : algebraMap A (FractionRing A) c ≠ 0,
      0 ≤ Ring.TameSymbol.ordv val (Units.mk0 _ hc) := by
    intro c hc
    have h1 : val (algebraMap A (FractionRing A) c) ≤ 1 :=
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := FractionRing A) v
        (toIcAtPrime A q.1 (algebraMap A (integralClosure A (FractionRing A)) c))
    have h2 := hvo (Units.mk0 _ hc)
    rw [Units.val_mk0] at h2
    rw [h2, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  obtain ⟨E, hE⟩ := Int.eq_ofNat_of_zero_le (hnn a (map_ne_zero_iff _
    (IsFractionRing.injective A (FractionRing A)) |>.mpr ha))
  obtain ⟨F, hF⟩ := Int.eq_ofNat_of_zero_le (hnn b (map_ne_zero_iff _
    (IsFractionRing.injective A (FractionRing A)) |>.mpr hb))
  change Ring.TameSymbol.ordv val f = E at hE
  change Ring.TameSymbol.ordv val g = F at hF
  have hvf : val (algebraMap A (FractionRing A) a) = WithZero.exp (-(E : ℤ)) := by
    rw [← hE]; exact hvo f
  have hvg : val (algebraMap A (FractionRing A) b) = WithZero.exp (-(F : ℤ)) := by
    rw [← hF]; exact hvo g
  set z := Ring.TameSymbol.symbolElt val f g with hzdef
  have hzK : (z : FractionRing A) = (-1) ^ (E * F) * (algebraMap A (FractionRing A) a) ^ F /
      (algebraMap A (FractionRing A) b) ^ E := by
    show (-1 : FractionRing A) ^ (Ring.TameSymbol.ordv val f * Ring.TameSymbol.ordv val g) *
      (f : FractionRing A) ^ (Ring.TameSymbol.ordv val g) /
      (g : FractionRing A) ^ (Ring.TameSymbol.ordv val f) = _
    rw [hE, hF, ← Nat.cast_mul, zpow_natCast, zpow_natCast, zpow_natCast]
    rfl
  have hz1 : val (z : FractionRing A) = 1 := by
    rw [hzK, map_div₀, map_mul, map_pow, map_pow, map_pow, Valuation.map_neg, map_one, one_pow,
      one_mul, hvf, hvg, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_sub,
      ← WithZero.exp_zero, WithZero.exp_inj]
    simp only [nsmul_eq_mul]
    ring
  obtain ⟨y₁, y₂, hy₁, hy₂, hz⟩ := exists_num_den_of_valuation_eq_one q.1 hfinq v (z : FractionRing A) hz1
  letI hloc : IsLocalHom (Ring.TameSymbol.toValuationSubring (Localization.AtPrime q.1.asIdeal) v) :=
    Ring.TameSymbol.isLocalHom_toValuationSubring (Localization.AtPrime q.1.asIdeal) v
  letI algKL : Algebra (IsLocalRing.ResidueField (Localization.AtPrime q.1.asIdeal))
      (IsLocalRing.ResidueField val.valuationSubring) :=
    (IsLocalRing.ResidueField.map
      (Ring.TameSymbol.toValuationSubring (Localization.AtPrime q.1.asIdeal) v)).toAlgebra
  have k1 := ordFrac_norm_residue_eq_exp_lam q.1 hB hfinq q.2 hA v y₁ hy₁
  have k2 := ordFrac_norm_residue_eq_exp_lam q.1 hB hfinq q.2 hA v y₂ hy₂
  have hres : IsLocalRing.residue _ z * IsLocalRing.residue _ (toValuationSubringIC A q.1 v y₂) =
      IsLocalRing.residue _ (toValuationSubringIC A q.1 v y₁) := by
    rw [← map_mul]; congr 1; exact Subtype.ext hz
  have hmul := congrArg (fun w => Ring.ordFrac (A ⧸ q.1.asIdeal) (K := q.1.asIdeal.ResidueField)
    (Algebra.norm (IsLocalRing.ResidueField (Localization.AtPrime q.1.asIdeal)) w)) hres
  simp only [map_mul] at hmul
  rw [k1, k2] at hmul
  have hX := eq_div_of_mul_eq WithZero.exp_ne_zero hmul
  rw [← WithZero.exp_sub] at hX
  -- Hsym = lam y₂ − lam y₁
  have hsymb : ∀ (c : A) (N : ℕ), val (algebraMap A (FractionRing A) c) = WithZero.exp (-(N : ℤ)) →
      algebraMap A (integralClosure A (FractionRing A)) c ∈ symbPow (primeBelow A q.1 v).asIdeal N ∧
      algebraMap A (integralClosure A (FractionRing A)) c ∉
        symbPow (primeBelow A q.1 v).asIdeal (N + 1) := by
    intro c N hc
    refine ⟨(mem_symbPow_primeBelow_iff q.1 hfinq v _ N).mpr (le_of_eq hc), fun h => ?_⟩
    have h' := (mem_symbPow_primeBelow_iff q.1 hfinq v _ (N + 1)).mp h
    change val (algebraMap A (FractionRing A) c) ≤ _ at h'
    rw [hc, WithZero.exp_le_exp] at h'
    push_cast at h'
    omega
  obtain ⟨haE, haE'⟩ := hsymb a E hvf
  obtain ⟨hbF, hbF'⟩ := hsymb b F hvg
  have hbK : algebraMap A (FractionRing A) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr hb
  have hyK : (y₁ : FractionRing A) * (algebraMap A (FractionRing A) b) ^ E =
      (-1) ^ (E * F) * (y₂ : FractionRing A) * (algebraMap A (FractionRing A) a) ^ F := by
    rw [← hz, hzK]
    field_simp
  have hy : y₁ * (algebraMap A (integralClosure A (FractionRing A)) b) ^ E =
      (-1) ^ (E * F) * y₂ * (algebraMap A (integralClosure A (FractionRing A)) a) ^ F := by
    apply Subtype.ext
    push_cast
    exact hyK
  have hH := Hsym_eq_lam_sub (A := A) (primeBelow A q.1 v)
    (fun y hy => lam_ne_top_primeBelow q.1 hB hfinq q.2 hA v y hy) haE haE' hbF hbF' hy₁ hy₂ hy
  change Ring.ordFrac (A ⧸ q.1.asIdeal) (K := q.1.asIdeal.ResidueField)
      (Algebra.norm (IsLocalRing.ResidueField (Localization.AtPrime q.1.asIdeal))
        (IsLocalRing.residue _ z)) = _
  rw [hX, hH]
  congr 1
  ring

end KeyLemma

end
