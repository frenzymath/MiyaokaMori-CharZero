import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLineStandardChart
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLinePointZero
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLinePointCoordinates

/-! # The image of the standard chart of the projective line

The standard chart `stdChart : A¹_k → P¹_k` (`t ↦ [1 : t]`, image `D₊(x₀)`) is a `k`-morphism and its
image is the complement of the single point `0 = [0 : 1]` (`ProjectiveLine.zero`).

Source: Theorem 4.2 of the paper (homogenizing in the fibre coordinate),
Hartshorne I.2 / II.2.5 (`P¹ = D₊(x₀) ∪ {[0:1]}`).

Proof of `D₊(x₀) = P¹ ∖ {[0:1]}`: a point of `Proj k[x₀,x₁]` is a relevant homogeneous prime `P`.
`[0:1]` is `P = (x₀)`, so `x₀ ∈ P` for `P = [0:1]`. Conversely if `x₀ ∈ P`, then `x₁ ∉ P` (every point
lies in `D₊(x₀)` or `D₊(x₁)`, `exists_coordinateOpen`), and for a homogeneous `f ∈ P` of degree `n`,
`f = x₀ g + c x₁ⁿ` with `c` the coefficient of `x₁ⁿ`; then `c x₁ⁿ ∈ P`, and `c ≠ 0` would give
`x₁ ∈ P`; so `c = 0` and `f ∈ (x₀)`. Homogeneous ideals are determined by their homogeneous elements
(`HomogeneousIdeal.ext'`), hence `P = (x₀)`.

Proof of `stdChart ≫ (P¹ ↘ Spec k) = (A¹ ↘ Spec k)`: `stdChart = SpecIso.hom ≫ Spec ψ ≫ awayι`, and
`awayι ≫ toSpecZero = Spec (fromZeroRingHom)` (Mathlib `Proj.awayι_toSpecZero`),
`SpecIso.inv ≫ (A¹ ↘ Spec k) = Spec C` (Mathlib `AffineSpace.SpecIso_inv_over`); the composite ring
map `k → 𝒜₀ → 𝒜_(x₀) → k[t]` is `c ↦ c/1 ↦ c(1, t) = c`, i.e. `C`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Algebraic core: a prime `P ⊆ k[x₀, x₁]` with `x₀ ∈ P`, `x₁ ∉ P` contains no homogeneous element
outside `(x₀)`. Write `f = (f - c x₁ⁿ) + c x₁ⁿ` with `c` the coefficient of `x₁ⁿ`; every other monomial
of the homogeneous `f` has positive `x₀`-degree, so `x₀ ∣ f - c x₁ⁿ`; then `c x₁ⁿ ∈ P` forces `c = 0`. -/
theorem MvPolynomial.X_zero_dvd_of_mem_of_isHomogeneous {k : Type u} [Field k]
    (P : Ideal (MvPolynomial (Fin 2) k)) [P.IsPrime]
    (h0 : MvPolynomial.X 0 ∈ P) (h1 : MvPolynomial.X 1 ∉ P) {n : ℕ} {f : MvPolynomial (Fin 2) k}
    (hf : f.IsHomogeneous n) (hfP : f ∈ P) : MvPolynomial.X (0 : Fin 2) ∣ f := by
  classical
  set c := MvPolynomial.coeff (Finsupp.single (1 : Fin 2) n) f with hc
  have hsplit : MvPolynomial.X (0 : Fin 2) ∣ f - MvPolynomial.monomial (Finsupp.single 1 n) c := by
    have hsum : f - MvPolynomial.monomial (Finsupp.single (1 : Fin 2) n) c =
        ∑ v ∈ f.support.erase (Finsupp.single 1 n),
          MvPolynomial.monomial v (MvPolynomial.coeff v f) := by
      by_cases hmem : Finsupp.single (1 : Fin 2) n ∈ f.support
      · rw [Finset.sum_erase_eq_sub hmem, ← MvPolynomial.as_sum]
      · rw [Finset.erase_eq_of_notMem hmem, ← MvPolynomial.as_sum]
        have : c = 0 := MvPolynomial.notMem_support_iff.mp hmem
        rw [this, MvPolynomial.monomial_zero, sub_zero]
    rw [hsum]
    apply Finset.dvd_sum
    intro v hv
    rw [Finset.mem_erase] at hv
    rw [MvPolynomial.X_dvd_monomial]
    right
    intro hv0
    apply hv.1
    have hdeg : v.degree = n := by
      by_contra hne
      exact (MvPolynomial.mem_support_iff.mp hv.2) (hf.coeff_eq_zero hne)
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, hv0, zero_add] at hdeg
    ext i
    fin_cases i
    · simp [hv0]
    · simp [hdeg]
  have hmono : MvPolynomial.monomial (Finsupp.single (1 : Fin 2) n) c ∈ P := by
    have h2 : f - MvPolynomial.monomial (Finsupp.single (1 : Fin 2) n) c ∈ P :=
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h0)) (Ideal.mem_span_singleton.mpr hsplit)
    have := P.sub_mem hfP h2
    simpa using this
  by_cases hc0 : c = 0
  · rw [hc0, MvPolynomial.monomial_zero, sub_zero] at hsplit
    exact hsplit
  · exfalso
    apply h1
    have hmono' : MvPolynomial.C c * MvPolynomial.X (1 : Fin 2) ^ n ∈ P := by
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]
      exact hmono
    have hu : IsUnit (MvPolynomial.C c : MvPolynomial (Fin 2) k) :=
      (isUnit_iff_ne_zero.mpr hc0).map MvPolynomial.C
    have hpow : MvPolynomial.X (1 : Fin 2) ^ n ∈ P := (Ideal.unit_mul_mem_iff_mem P hu).mp hmono'
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance n hpow

/-- `D₊(x₀) = P¹ ∖ {[0 : 1]}`: a point of `P¹_k` lies in the basic open `D₊(x₀)` iff it is not the
marked point `0 = [0 : 1] = V₊(x₀)`. -/
theorem ProjectiveLine.mem_basicOpen_X_zero_iff {k : Type u} [Field k]
    (x : AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k)) :
    x ∈ AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k)
        (MvPolynomial.X 0) ↔ x ≠ ProjectiveLine.zero k := by
  rw [AlgebraicGeometry.Proj.mem_basicOpen]
  constructor
  · intro h hx
    apply h
    rw [hx]
    exact Ideal.mem_span_singleton_self _
  · intro hne hmem
    apply hne
    obtain ⟨i, hi⟩ := AlgebraicGeometry.Proj.ProjectiveLinePointCoordinates.exists_coordinateOpen x
    have hX1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ∉ x.asHomogeneousIdeal := by
      fin_cases i
      · exact absurd hmem hi
      · exact hi
    have : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
    apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.ext'
    intro n f hf
    change f ∈ x.asHomogeneousIdeal ↔ f ∈ Ideal.span {MvPolynomial.X (0 : Fin 2)}
    constructor
    · intro hfP
      exact Ideal.mem_span_singleton.mpr
        (MvPolynomial.X_zero_dvd_of_mem_of_isHomogeneous x.asHomogeneousIdeal.toIdeal hmem hX1
          ((MvPolynomial.mem_homogeneousSubmodule n f).mp hf) hfP)
    · intro hf0
      exact (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)) hf0

/-- Variable-level lemma: the image of `f ≫ g ≫ h` with `f`, `g` isomorphisms is the image of `h`. -/
theorem AlgebraicGeometry.Scheme.Hom.opensRange_isIso_isIso_comp {W X Y Z : AlgebraicGeometry.Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) [IsIso f] [IsIso g] [AlgebraicGeometry.IsOpenImmersion h] :
    (f ≫ g ≫ h).opensRange = h.opensRange := by
  rw [AlgebraicGeometry.Scheme.Hom.opensRange_comp_of_isIso,
    AlgebraicGeometry.Scheme.Hom.opensRange_comp_of_isIso]

/-- The image of the standard chart is the basic open `D₊(x₀)` (Mathlib `Proj.opensRange_awayι`;
the other two factors of `stdChart` are isomorphisms). -/
theorem ProjectiveLine.opensRange_stdChart (k : Type u) [Field k] :
    (ProjectiveLine.stdChart k).opensRange =
      AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k)
        (MvPolynomial.X 0) := by
  have : CategoryTheory.IsIso (CommRingCat.ofHom (ProjectiveLine.stdChartRingHom k)) := by
    rw [ProjectiveLine.stdChartRingHom_eq]
    exact (ProjectiveLine.stdChartRingEquiv k).toCommRingCatIso.isIso_hom
  exact (AlgebraicGeometry.Scheme.Hom.opensRange_isIso_isIso_comp
    (AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)).hom
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (ProjectiveLine.stdChartRingHom k)))
    (AlgebraicGeometry.Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k) (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X k 0)) Nat.one_pos)).trans
    (AlgebraicGeometry.Proj.opensRange_awayι _ _ _ _)

/-- **Leaf.** The image of the standard chart `A¹_k → P¹_k` is `P¹_k ∖ {0}`, `0 = [0 : 1]`. -/
theorem ProjectiveLine.range_stdChart (k : Type u) [Field k] :
    Set.range (ProjectiveLine.stdChart k) = ({ProjectiveLine.zero k}ᶜ : Set (ProjectiveLine k)) := by
  have h1 : ((ProjectiveLine.stdChart k).opensRange : Set (ProjectiveLine k)) =
      ((AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k)
        (MvPolynomial.X 0) : (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k)).Opens) :
          Set (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k))) :=
    congrArg (fun U : (ProjectiveLine k).Opens => (U : Set (ProjectiveLine k)))
      (ProjectiveLine.opensRange_stdChart k)
  have h2 : Set.range (ProjectiveLine.stdChart k) =
      ((ProjectiveLine.stdChart k).opensRange : Set (ProjectiveLine k)) :=
    (AlgebraicGeometry.Scheme.Hom.coe_opensRange _).symm
  refine h2.trans (h1.trans (Set.ext fun x => ?_))
  exact (ProjectiveLine.mem_basicOpen_X_zero_iff x).trans Set.mem_compl_singleton_iff.symm

/-- Variable-level lemma for `stdChart_comp_toSpecBase`. -/
theorem CategoryTheory.comp_comp_comp_eq_of_eq {A B C D E : AlgebraicGeometry.Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : D ⟶ E) (s : B ⟶ E) (t : A ⟶ E)
    (h1 : b ≫ c ≫ d = s) (h2 : a ≫ s = t) : (a ≫ b ≫ c) ≫ d = t := by
  rw [Category.assoc, Category.assoc, h1, h2]

/-- The ring-level computation behind `stdChart_comp_toSpecBase`: `k → 𝒜₀ → 𝒜_(x₀) → k[t]` is `C`. -/
theorem ProjectiveLine.stdChartRingHom_fromZero_algebraMap {k : Type u} [Field k] (c : k) :
    ProjectiveLine.stdChartRingHom k
      (HomogeneousLocalization.fromZeroRingHom (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k)
        (Submonoid.powers (MvPolynomial.X 0))
        (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k 0) c)) =
      MvPolynomial.C c := by
  have hval : (HomogeneousLocalization.fromZeroRingHom (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k)
      (Submonoid.powers (MvPolynomial.X 0))
      (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k 0) c)).val =
      algebraMap (MvPolynomial (Fin (1 + 1)) k)
        (Localization.Away (MvPolynomial.X (0 : Fin (1 + 1)) : MvPolynomial (Fin (1 + 1)) k))
        (MvPolynomial.C c) := by
    rw [← Localization.mk_one_eq_algebraMap]
    rfl
  unfold ProjectiveLine.stdChartRingHom
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, hval, IsLocalization.Away.lift,
    IsLocalization.lift_eq]
  simp [MvPolynomial.algebraMap_eq]

/-- `Spec ψ ≫ awayι ≫ (P¹ → Spec k) = Spec C` (Mathlib `Proj.awayι_toSpecZero`). -/
theorem ProjectiveLine.specMap_stdChartRingHom_comp_awayι_comp_toSpecBase (k : Type u) [Field k] :
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (ProjectiveLine.stdChartRingHom k)) ≫
      AlgebraicGeometry.Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k) (MvPolynomial.X 0)
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X k 0)) Nat.one_pos ≫
      ProjectiveSpace.toSpecBase 1 k =
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := ULift.{u} (Fin 1)) (R := k))) := by
  show AlgebraicGeometry.Spec.map (CommRingCat.ofHom (ProjectiveLine.stdChartRingHom k)) ≫
      AlgebraicGeometry.Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k) (MvPolynomial.X 0)
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X k 0)) Nat.one_pos ≫
      (AlgebraicGeometry.Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k 0)))) = _
  rw [AlgebraicGeometry.Proj.awayι_toSpecZero_assoc, ← AlgebraicGeometry.Spec.map_comp,
    ← AlgebraicGeometry.Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  exact ProjectiveLine.stdChartRingHom_fromZero_algebraMap c

/-- **Leaf.** The standard chart is a `k`-morphism: `stdChart ≫ (P¹ → Spec k) = (A¹ → Spec k)`. -/
theorem ProjectiveLine.stdChart_comp_toSpecBase (k : Type u) [Field k] :
    ProjectiveLine.stdChart k ≫ ProjectiveSpace.toSpecBase 1 k =
      AlgebraicGeometry.Scheme.affineLineOver.toBase (AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  have h2 := congrArg (fun m => (AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)).hom ≫ m)
    (AlgebraicGeometry.AffineSpace.SpecIso_inv_over (n := ULift.{u} (Fin 1)) (CommRingCat.of k))
  simp only [Iso.hom_inv_id_assoc] at h2
  exact CategoryTheory.comp_comp_comp_eq_of_eq _ _ _ _ _ _
    (ProjectiveLine.specMap_stdChartRingHom_comp_awayι_comp_toSpecBase k) h2.symm

end
