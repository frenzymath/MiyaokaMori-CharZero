import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Dimension.FiberFiniteHeight

/-! # The finite local model of a finite extension of domains at a height-one prime

Let `R → C` be a ring map, `𝔭 ⊂ R` a prime, `A` a localization of `R` at `𝔭` (any model, `A` local),
`B := C_𝔭 = Localization (algebraMapSubmonoid C 𝔭.primeCompl)`, and `A → B` the induced map. Then:
(1) `R → C` finite ⇒ `A → B` finite; `R → C` injective with `C` a domain ⇒ `A → B` injective and `B`
    a domain; if `L` is a field with `L = Frac C`, the lift `B → L` makes `L = Frac B`, and if `A → L`
    and `R → C → L` agree on `R`, then `A → B → L` is a tower.
(2) If `R → C` is finite, `m ↦ m ∩ C` is a bijection `MaxSpec B ≃ {𝔮 ∈ Spec C | 𝔮 ∩ R = 𝔭}` with
    inverse `𝔮 ↦ 𝔮B`.
(3) For `m ∈ MaxSpec B`, `𝔮 = m ∩ C`, let `S` be any model of the localization of `C` at `𝔮`
    (`S` local) and `φ : A → S` a local homomorphism agreeing with `R → C → S` on `R`. Then
    `[B/m : A/m_A]` (`Ideal.inertiaDeg'`) `= [κ(S) : κ(A)]` (via `ResidueField.map φ`).
(4) In the same setting, with `L ⊇ S` compatible: for `b ∈ B` there is `s ∈ S` with the same image
    as `b` in `L` and `ord_S(s) = ord_{B_m}(b)`.
(5) If `R` is a Noetherian domain, `C` a domain, `R → C` finite injective and `ht 𝔭 = 1`, then every
    prime `𝔮` lying over `𝔭` has `ht 𝔮 = 1`.

Proof:
1. (1): `Module.Finite.of_isLocalization`; `IsLocalization.map_injective_of_injective`;
   `IsLocalization.isDomain_localization`;
   `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization`; the tower follows from the
   universal property of localization (`IsLocalization.ringHom_ext`), checked on `R`.
2. (2): `m` maximal and `B` integral over `A` ⇒ `m ∩ A = m_A`
   (`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`), so `m ∩ R = 𝔭`. Conversely `𝔮 ∩ R = 𝔭` ⇒
   `𝔮` is disjoint from `M` ⇒ `𝔮B` is prime with `𝔮B ∩ C = 𝔮` (`IsLocalization.orderIsoOfPrime`);
   `𝔮B ∩ A` is a prime of `A` meeting `R` in `𝔭`, hence `= 𝔭A = m_A`, maximal; under an integral
   extension `𝔮B` is maximal (`Ideal.isMaximal_of_isIntegral_of_isMaximal_comap`).
3. (3): `ψ : B → S` is the lift of `C → S` (elements of `M` are not in `𝔮`, hence invertible in `S`);
   `ψ ∘ (A → B) = φ` (checked on `R`); `ψ⁻¹(m_S) ⊇ m`, hence `= m`; the induced `j : B/m → κ(S)` is
   injective (a field homomorphism) and surjective (elements of `S` are `c/t` with `t ∉ 𝔮`, and
   `j(t̄) ≠ 0` is invertible); `i = id : A/m_A = κ(A)`; `Algebra.finrank_eq_of_equiv_equiv`.
4. (4): `B_m` is a localization of `C` at `𝔮`
   (`IsLocalization.isLocalization_atPrime_localization_atPrime`), hence isomorphic to `S` as
   `C`-algebras via `e`; `s := e⁻¹(b/1)`; the two ring maps `B → L` agree on `C`, hence are equal;
   `Ring.ord_ringEquiv`.
5. (5): `FiberFiniteHeight` (2) (`R → C` finite ⇒ the fibre ring is finite) gives `ht 𝔮 ≤ 1`;
   `𝔮 ∩ R = 𝔭 ≠ 0` ⇒ `𝔮 ≠ 0` ⇒ `ht 𝔮 ≥ 1`.

Reference: the proof of Stacks 02RT (reducing the geometric local model to the algebraic setting of
02MJ).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

noncomputable section

/-- `Ring.ord` is invariant under ring isomorphisms. -/
theorem Ring.ord_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (x : R) :
    Ring.ord S (e x) = Ring.ord R x := by
  unfold Ring.ord
  let _ : Algebra R S := e.toRingHom.toAlgebra
  have hsurj : Function.Surjective (algebraMap R S) := e.surjective
  rw [← Module.length_eq_of_surjective (S := R) (R := S) (M := S ⧸ Ideal.span {e x}) hsurj]
  symm
  have hmap : (Ideal.span {x} : Ideal R).map e.toRingHom = Ideal.span {e x} := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  let φ : (R ⧸ Ideal.span {x}) ≃+* (S ⧸ Ideal.span {e x}) :=
    Ideal.quotientEquiv _ _ e hmap.symm
  let ψ : (R ⧸ Ideal.span {x}) ≃ₗ[R] (S ⧸ Ideal.span {e x}) :=
    { φ with
      map_smul' := fun r y => by
        induction y using Submodule.Quotient.induction_on with
        | H y =>
          show φ (r • Ideal.Quotient.mk _ y) = r • φ (Ideal.Quotient.mk _ y)
          rw [Algebra.smul_def, Algebra.smul_def, map_mul]
          rfl }
  exact ψ.length_eq

namespace FiniteLocalModel

variable {R : Type u} (C : Type u) [CommRing R] [CommRing C] [Algebra R C]
  (𝔭 : Ideal R) [𝔭.IsPrime]

/-- `B = C_𝔭`. -/
abbrev LocB : Type u := Localization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl)

variable (A : Type u) [CommRing A] [Algebra R A] [IsLocalization.AtPrime A 𝔭]

/-- The map `A → B`. -/
@[instance_reducible] def algAB : Algebra A (LocB C 𝔭) :=
  (IsLocalization.map (M := 𝔭.primeCompl) (T := Algebra.algebraMapSubmonoid C 𝔭.primeCompl)
    (LocB C 𝔭) (algebraMap R C) (Submonoid.le_comap_map _)).toAlgebra

theorem algAB_algebraMap_comp :
    letI := algAB C 𝔭 A
    (algebraMap A (LocB C 𝔭)).comp (algebraMap R A) =
      (algebraMap C (LocB C 𝔭)).comp (algebraMap R C) :=
  IsLocalization.map_comp _

theorem tower_RAB :
    letI := algAB C 𝔭 A
    IsScalarTower R A (LocB C 𝔭) := by
  letI := algAB C 𝔭 A
  refine IsScalarTower.of_algebraMap_eq' ?_
  rw [algAB_algebraMap_comp, IsScalarTower.algebraMap_eq R C (LocB C 𝔭)]

theorem finite_AB [Module.Finite R C] :
    letI := algAB C 𝔭 A
    Module.Finite A (LocB C 𝔭) := by
  letI := algAB C 𝔭 A
  have := tower_RAB C 𝔭 A
  exact Module.Finite.of_isLocalization R C 𝔭.primeCompl

theorem injective_AB (hinj : Function.Injective (algebraMap R C)) :
    letI := algAB C 𝔭 A
    Function.Injective (algebraMap A (LocB C 𝔭)) :=
  haveI : IsLocalization (𝔭.primeCompl.map (algebraMap R C)) (LocB C 𝔭) :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) (LocB C 𝔭))
  IsLocalization.map_injective_of_injective 𝔭.primeCompl A (LocB C 𝔭) hinj

theorem isDomain_B [IsDomain C] (hinj : Function.Injective (algebraMap R C)) :
    IsDomain (LocB C 𝔭) := by
  refine IsLocalization.isDomain_localization ?_
  rintro _ ⟨r, hr, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero fun h ↦ hr ?_
  have : r = 0 := hinj (by rw [h, map_zero])
  rw [this]; exact 𝔭.zero_mem

section Frac

variable (L : Type u) [Field L] [Algebra C L] [IsFractionRing C L] [IsDomain C]

theorem isUnit_of_mem (hinj : Function.Injective (algebraMap R C))
    (c : Algebra.algebraMapSubmonoid C 𝔭.primeCompl) : IsUnit (algebraMap C L c) := by
  obtain ⟨_, r, hr, rfl⟩ := c
  refine IsUnit.mk0 _ fun h ↦ hr ?_
  have h1 : algebraMap R C r = 0 := IsFractionRing.injective C L (by rw [h, map_zero])
  have : r = 0 := hinj (by rw [h1, map_zero])
  rw [this]; exact 𝔭.zero_mem

/-- The map `B → L`. -/
@[instance_reducible] def algBL (hinj : Function.Injective (algebraMap R C)) : Algebra (LocB C 𝔭) L :=
  (IsLocalization.lift (M := Algebra.algebraMapSubmonoid C 𝔭.primeCompl)
    (g := algebraMap C L) (isUnit_of_mem C 𝔭 L hinj)).toAlgebra

theorem tower_CBL (hinj : Function.Injective (algebraMap R C)) :
    letI := algBL C 𝔭 L hinj
    IsScalarTower C (LocB C 𝔭) L := by
  letI := algBL C 𝔭 L hinj
  refine IsScalarTower.of_algebraMap_eq fun c ↦ ?_
  exact (IsLocalization.lift_eq (isUnit_of_mem C 𝔭 L hinj) c).symm

theorem isFractionRing_BL (hinj : Function.Injective (algebraMap R C)) :
    letI := algBL C 𝔭 L hinj
    IsFractionRing (LocB C 𝔭) L := by
  letI := algBL C 𝔭 L hinj
  have := tower_CBL C 𝔭 L hinj
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) (LocB C 𝔭) L

theorem tower_ABL (hinj : Function.Injective (algebraMap R C)) [Algebra A L]
    (h : (algebraMap A L).comp (algebraMap R A) = (algebraMap C L).comp (algebraMap R C)) :
    letI := algAB C 𝔭 A
    letI := algBL C 𝔭 L hinj
    IsScalarTower A (LocB C 𝔭) L := by
  letI := algAB C 𝔭 A
  letI := algBL C 𝔭 L hinj
  have := tower_CBL C 𝔭 L hinj
  refine IsScalarTower.of_algebraMap_eq' ?_
  refine IsLocalization.ringHom_ext 𝔭.primeCompl ?_
  rw [h, RingHom.comp_assoc, algAB_algebraMap_comp, ← RingHom.comp_assoc,
    ← IsScalarTower.algebraMap_eq C (LocB C 𝔭) L]

end Frac

section Max

theorem disjoint_of_comap_eq {𝔮 : Ideal C} (h : 𝔮.comap (algebraMap R C) = 𝔭) :
    Disjoint (Algebra.algebraMapSubmonoid C 𝔭.primeCompl : Set C) (𝔮 : Set C) := by
  rw [Set.disjoint_left]
  rintro _ ⟨r, hr, rfl⟩ hmem
  exact hr (h ▸ (Ideal.mem_comap.mpr hmem))

variable [IsLocalRing A] [Module.Finite R C]

include A

theorem comap_A_of_isMaximal (m : Ideal (LocB C 𝔭)) [hm : m.IsMaximal] :
    letI := algAB C 𝔭 A
    m.comap (algebraMap A (LocB C 𝔭)) = IsLocalRing.maximalIdeal A := by
  letI := algAB C 𝔭 A
  have := finite_AB C 𝔭 A
  have : Algebra.IsIntegral A (LocB C 𝔭) := Algebra.IsIntegral.of_finite _ _
  exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)

theorem comap_R_of_isMaximal (m : Ideal (LocB C 𝔭)) [hm : m.IsMaximal] :
    (m.comap (algebraMap C (LocB C 𝔭))).comap (algebraMap R C) = 𝔭 := by
  letI := algAB C 𝔭 A
  rw [Ideal.comap_comap, ← algAB_algebraMap_comp C 𝔭 A, ← Ideal.comap_comap,
    comap_A_of_isMaximal C 𝔭 A m]
  exact IsLocalization.AtPrime.under_maximalIdeal A 𝔭

theorem isMaximal_map {𝔮 : Ideal C} [h𝔮 : 𝔮.IsPrime] (h : 𝔮.comap (algebraMap R C) = 𝔭) :
    (𝔮.map (algebraMap C (LocB C 𝔭))).IsMaximal := by
  letI := algAB C 𝔭 A
  have := finite_AB C 𝔭 A
  have : Algebra.IsIntegral A (LocB C 𝔭) := Algebra.IsIntegral.of_finite _ _
  have hdisj := disjoint_of_comap_eq C 𝔭 h
  have hprime : (𝔮.map (algebraMap C (LocB C 𝔭))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ 𝔮 h𝔮 hdisj
  have hcomap : (𝔮.map (algebraMap C (LocB C 𝔭))).comap (algebraMap C (LocB C 𝔭)) = 𝔮 :=
    IsLocalization.under_map_of_isPrime_disjoint _ _ h𝔮 hdisj
  set P := (𝔮.map (algebraMap C (LocB C 𝔭))).comap (algebraMap A (LocB C 𝔭)) with hP
  have hPR : P.comap (algebraMap R A) = 𝔭 := by
    rw [hP, Ideal.comap_comap, algAB_algebraMap_comp C 𝔭 A, ← Ideal.comap_comap, hcomap, h]
  have hPmax : P = IsLocalRing.maximalIdeal A := by
    rw [← IsLocalization.map_under 𝔭.primeCompl A P, Ideal.under_def, hPR]
    exact IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 A
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) _
    (by rw [← hP, hPmax]; exact IsLocalRing.maximalIdeal.isMaximal A)

/-- `MaxSpec B ≃ {𝔮 ∈ Spec C | 𝔮 ∩ R = 𝔭}`. -/
def maxEquiv : MaximalSpectrum (LocB C 𝔭) ≃
    {𝔮 : PrimeSpectrum C // 𝔮.asIdeal.comap (algebraMap R C) = 𝔭} where
  toFun m := ⟨⟨m.asIdeal.comap (algebraMap C (LocB C 𝔭)), inferInstance⟩,
    haveI := m.isMaximal; comap_R_of_isMaximal C 𝔭 A m.asIdeal⟩
  invFun 𝔮 := ⟨𝔮.1.asIdeal.map (algebraMap C (LocB C 𝔭)), isMaximal_map C 𝔭 A 𝔮.2⟩
  left_inv m := MaximalSpectrum.ext
    (IsLocalization.map_under (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) _ m.asIdeal)
  right_inv 𝔮 := Subtype.ext (PrimeSpectrum.ext
    (IsLocalization.under_map_of_isPrime_disjoint _ _ 𝔮.1.isPrime
      (disjoint_of_comap_eq C 𝔭 𝔮.2)))

theorem maxEquiv_apply (m : MaximalSpectrum (LocB C 𝔭)) :
    ((maxEquiv C 𝔭 A m).1).asIdeal = m.asIdeal.comap (algebraMap C (LocB C 𝔭)) := rfl

end Max

section PerMax

variable [IsLocalRing A] [Module.Finite R C]
variable (m : Ideal (LocB C 𝔭)) [hm : m.IsMaximal]
variable (S : Type u) [CommRing S] [Algebra C S] [IsLocalRing S]
  [IsLocalization.AtPrime S (m.comap (algebraMap C (LocB C 𝔭)))]

include A m

theorem isUnit_algebraMap_S (c : Algebra.algebraMapSubmonoid C 𝔭.primeCompl) :
    IsUnit (algebraMap C S c) := by
  rw [IsLocalization.AtPrime.isUnit_to_map_iff S (m.comap (algebraMap C (LocB C 𝔭)))]
  exact Set.disjoint_left.mp (disjoint_of_comap_eq C 𝔭 (comap_R_of_isMaximal C 𝔭 A m)) c.2

/-- The lift `ψ : B → S`. -/
def toS : LocB C 𝔭 →+* S :=
  IsLocalization.lift (M := Algebra.algebraMapSubmonoid C 𝔭.primeCompl)
    (g := algebraMap C S) (isUnit_algebraMap_S C 𝔭 A m S)

theorem toS_comp_algebraMap :
    (toS C 𝔭 A m S).comp (algebraMap C (LocB C 𝔭)) = algebraMap C S :=
  IsLocalization.lift_comp _

theorem le_comap_toS : m ≤ (IsLocalRing.maximalIdeal S).comap (toS C 𝔭 A m S) := by
  intro b hb
  obtain ⟨c, t, rfl⟩ := IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) b
  have hc : c ∈ m.comap (algebraMap C (LocB C 𝔭)) :=
    (IsLocalization.mk'_mem_iff (M := Algebra.algebraMapSubmonoid C 𝔭.primeCompl)
      (S := LocB C 𝔭)).mp hb
  rw [Ideal.mem_comap, toS, IsLocalization.lift_mk']
  exact Ideal.mul_mem_right _ _
    ((IsLocalization.AtPrime.to_map_mem_maximal_iff S _ c).mpr hc)

theorem inertiaDeg_eq (φ : A →+* S)
    (hφ : φ.comp (algebraMap R A) = (algebraMap C S).comp (algebraMap R C)) [IsLocalHom φ] :
    letI := algAB C 𝔭 A
    Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) m =
      letI := (IsLocalRing.ResidueField.map φ).toAlgebra
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField S) := by
  letI := algAB C 𝔭 A
  haveI : m.LiesOver (IsLocalRing.maximalIdeal A) := ⟨(comap_A_of_isMaximal C 𝔭 A m).symm⟩
  rw [Ideal.inertiaDeg'_algebraMap]
  letI := (IsLocalRing.ResidueField.map φ).toAlgebra
  set ψ := toS C 𝔭 A m S with hψdef
  have hψ : ψ.comp (algebraMap A (LocB C 𝔭)) = φ := by
    refine IsLocalization.ringHom_ext 𝔭.primeCompl ?_
    rw [RingHom.comp_assoc, algAB_algebraMap_comp, ← RingHom.comp_assoc,
      toS_comp_algebraMap, hφ]
  let j0 : LocB C 𝔭 ⧸ m →+* IsLocalRing.ResidueField S :=
    Ideal.Quotient.lift m ((IsLocalRing.residue S).comp ψ) fun b hb ↦
      (IsLocalRing.residue_eq_zero_iff _).mpr (le_comap_toS C 𝔭 A m S hb)
  letI : Field (LocB C 𝔭 ⧸ m) := Ideal.Quotient.field m
  have hj0 : ∀ c : C, j0 (Ideal.Quotient.mk m (algebraMap C _ c)) =
      IsLocalRing.residue S (algebraMap C S c) := fun c ↦ by
    simp only [j0, Ideal.Quotient.lift_mk, RingHom.comp_apply]
    rw [← RingHom.comp_apply ψ, toS_comp_algebraMap]
  have hinj : Function.Injective j0 := j0.injective
  have hsurj : Function.Surjective j0 := by
    intro y
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨⟨c, t⟩, hst⟩ := IsLocalization.surj (m.comap (algebraMap C (LocB C 𝔭))).primeCompl s
    have ht : IsLocalRing.residue S (algebraMap C S t) ≠ 0 := by
      rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalization.AtPrime.to_map_mem_maximal_iff S
        (m.comap (algebraMap C (LocB C 𝔭)))]
      exact t.2
    refine ⟨Ideal.Quotient.mk m (algebraMap C _ c) * (Ideal.Quotient.mk m (algebraMap C _ t))⁻¹, ?_⟩
    rw [map_mul, map_inv₀, hj0, hj0, ← hst, map_mul, mul_assoc, mul_inv_cancel₀ ht, mul_one]
  refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _) (RingEquiv.ofBijective j0 ⟨hinj, hsurj⟩) ?_
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_)
  show IsLocalRing.ResidueField.map φ (IsLocalRing.residue A a) =
    j0 (algebraMap (A ⧸ IsLocalRing.maximalIdeal A) (LocB C 𝔭 ⧸ m) (Ideal.Quotient.mk _ a))
  rw [IsLocalRing.ResidueField.map_residue, Ideal.Quotient.algebraMap_mk_of_liesOver]
  simp only [j0, Ideal.Quotient.lift_mk, RingHom.comp_apply]
  rw [← RingHom.comp_apply ψ, hψ]

theorem exists_ord_eq (L : Type u) [Field L] [Algebra C L] [IsFractionRing C L] [IsDomain C]
    (hinj : Function.Injective (algebraMap R C)) [Algebra S L] [IsScalarTower C S L]
    (b : LocB C 𝔭) :
    letI := algBL C 𝔭 L hinj
    ∃ s : S, algebraMap S L s = algebraMap (LocB C 𝔭) L b ∧
      Ring.ord S s = Ring.ord (Localization.AtPrime m) (algebraMap (LocB C 𝔭) _ b) := by
  letI := algBL C 𝔭 L hinj
  have := tower_CBL C 𝔭 L hinj
  let T := Localization.AtPrime m
  let e : S ≃ₐ[C] T :=
    IsLocalization.algEquiv (m.comap (algebraMap C (LocB C 𝔭))).primeCompl S T
  refine ⟨e.symm (algebraMap (LocB C 𝔭) T b), ?_, ?_⟩
  · have key : ((algebraMap S L).comp (e.symm : T →+* S)).comp (algebraMap (LocB C 𝔭) T) =
        algebraMap (LocB C 𝔭) L := by
      refine IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) ?_
      ext c
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply C (LocB C 𝔭) T,
        ← IsScalarTower.algebraMap_apply C (LocB C 𝔭) L]
      show algebraMap S L (e.symm (algebraMap C T c)) = _
      rw [e.symm.commutes, ← IsScalarTower.algebraMap_apply C S L]
    exact congr($key b)
  · have := Ring.ord_ringEquiv e.toRingEquiv (e.symm (algebraMap (LocB C 𝔭) T b))
    rw [← this]
    congr 1
    exact e.apply_symm_apply _

end PerMax

theorem height_eq_one_of_comap_eq [IsDomain R] [IsNoetherianRing R] [IsDomain C]
    [Module.Finite R C] (hinj : Function.Injective (algebraMap R C)) (h𝔭 : 𝔭.height = 1)
    {𝔮 : Ideal C} [𝔮.IsPrime] (h : 𝔮.comap (algebraMap R C) = 𝔭) : 𝔮.height = 1 := by
  have : IsNoetherianRing C := IsNoetherianRing.of_finite R C
  have : 𝔮.LiesOver 𝔭 := ⟨h.symm⟩
  refine le_antisymm (h𝔭 ▸ Ideal.height_le_of_liesOver_of_finite_fiber 𝔭 𝔮) ?_
  rw [Order.one_le_iff_pos, pos_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
  rintro rfl
  rw [Ideal.comap_bot_of_injective _ hinj] at h
  exact Ideal.ne_bot_of_height_eq_one h𝔭 h.symm

end FiniteLocalModel

end
