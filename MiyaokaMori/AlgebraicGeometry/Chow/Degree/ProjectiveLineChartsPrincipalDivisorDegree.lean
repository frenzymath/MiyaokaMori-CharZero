import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLine
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ProjectiveLineIsSmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceChartPolynomial
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.OrdOpenImmersion
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.PrimeDivisorLocalEquation
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.AffineLinePrincipalDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Morphisms.ResidueDegreeComposition
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLinePointCoordinates

/-! # Charts of the projective line and the degree of a principal divisor

The two standard charts of `P¹_K = Proj K[x₀,x₁]` and the computation, chart by chart, that every rational
function on `P¹_K` has a principal divisor of degree `0` (`sum_ord_mul_residueDegree_eq_zero_proj`, stated for
Mathlib's `Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)`; the version for `(ProjectiveLine.variety K).toScheme`
is the one-line `ProjectiveLine.sum_ord_mul_residueDegree_eq_zero` in `ProjectiveLinePrincipalDivisorDegreeZero.lean`).

Route (Hartshorne II Prop. 6.4(b), `n = 1`, made explicit on the charts):
1. `chartι K i : Spec K[X] ⟶ P¹` is `Spec (chartCoord K i) ≫ Proj.awayι 𝒜 xᵢ`, an open immersion with image
   `D₊(xᵢ)`, `X ↦ x_j/xᵢ` (`chartCoord` is `ProjectiveSpace.chartRingEquiv` followed by
   `MvPolynomial.uniqueAlgEquiv`). `chartι_comp_over`: it is a morphism over `K`.
2. Points: `mem_range_chartι_zero_or_eq_inftyPoint` — every point of `P¹` is in the image of the chart `D₊(x₀)`
   or is `∞ := chartι K 1 (X)` (`= [0:1]`); `inftyPoint_not_mem_range_chartι_zero`. (A point with `x₀ ∈ 𝔭` has
   `x₁ ∉ 𝔭` (`exists_coordinateOpen`), so lies in `D₊(x₁)`, where `x₀/x₁` lies in the corresponding prime of
   `K[X]`, which must then be `(X)`.)
3. `chartSectionHom K i : K[X] →+* K(P¹)` sends `f` to the germ of the section `f(x_j/xᵢ)` of `D₊(xᵢ)`;
   `functionFieldMap_chartι_chartSectionHom`: pulling this germ back along `chartι K i` gives `f ∈ K(𝔸¹)`
   (`Proj.awayι` factors through `IsAffineOpen.fromSpec`, `awayι_eq_SpecMap_fromSpec`; germs of pulled-back
   sections, `germ_app_of_eq_SpecMap_fromSpec`).
4. Transition: on the overlap `D₊(x₀x₁)` both charts restrict via `HomogeneousLocalization.awayMap`
   (`Proj.awayMap_awayToSection`); constants agree (`chartSectionHom_C`) and `(x₁/x₀)·(x₀/x₁) = 1`
   (`chartSectionHom_X_mul_chartSectionHom_X`). Hence `cs₀ a = cs₁ (reverse a) · (cs₀ X)^{deg a}`
   (`Polynomial.eval₂_reverse_mul_pow`), so `ord_∞ (cs₀ a) = -deg a` by the affine-line computation at `(X)`.
5. `finsum_ord_chartSectionHom_zero`: `Σ_y ord_y(cs₀ a)·[κ(y):K] = (Σ over D₊(x₀)) + (term at ∞) = deg a - deg a = 0`
   (`ord` and residue degrees are transported along the open immersions `chartι`:
   `MiyaokaMori.OrdOpenImmersion.ord_functionFieldMap`, `AlgebraicGeometry.Intersection.residueDegree_comp`).
6. A unit `h ∈ K(P¹)` pulls back to `a/b ∈ K(𝔸¹) = Frac K[X]`, so `h = cs₀ a / cs₀ b` and the sum is `0 - 0`.

Edge cases: `K` arbitrary (finite or not algebraically closed — the closed points of `𝔸¹` are the irreducible
polynomials); `h` constant (`a`, `b` units): both partial sums vanish.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

variable (K : Type u) [Field K]


/-- germ at a point of a section pulled back along `Spec R → Spec Γ(X, U) → X`, where the second map
is `IsAffineOpen.fromSpec`: it is the germ of the image under `ρ` (viewed as a global section of
`Spec R` via `ΓSpecIso`). -/
theorem AlgebraicGeometry.germ_app_of_eq_SpecMap_fromSpec {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {R : CommRingCat.{u}} (ρ : Γ(X, U) ⟶ R) (g : Spec R ⟶ X)
    (hg : g = Spec.map ρ ≫ hU.fromSpec) (s : Γ(X, U)) (x : Spec R) (hx : x ∈ g ⁻¹ᵁ U) :
    (Spec R).presheaf.germ (g ⁻¹ᵁ U) x hx (g.app U s) =
      (Spec R).presheaf.germ ⊤ x trivial ((Scheme.ΓSpecIso R).inv (ρ s)) := by
  subst hg
  rw [Scheme.Hom.comp_app]
  erw [CommRingCat.comp_apply]
  rw [IsAffineOpen.fromSpec_app_self]
  erw [CommRingCat.comp_apply]
  have hnat := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso Γ(X, U)).inv s))
    ((Spec.map ρ).naturality (eqToHom hU.fromSpec_preimage_self).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
  erw [hnat]
  have hnat2 := congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso_inv_naturality ρ)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appTop] at hnat2
  erw [← hnat2]
  exact (Spec R).presheaf.germ_res_apply' _ x hx _

/-- `Proj.awayι` factors as `Spec (A_f)₀ ≅ Spec Γ(D₊(f)) → Proj A` through `IsAffineOpen.fromSpec`. -/
theorem AlgebraicGeometry.Proj.awayι_eq_SpecMap_fromSpec {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    Proj.awayι 𝒜 f f_deg hm = Spec.map (Proj.basicOpenIsoAway 𝒜 f f_deg hm).inv ≫
      (Proj.isAffineOpen_basicOpen 𝒜 f f_deg hm).fromSpec := by
  rw [Proj.awayι, IsAffineOpen.fromSpec, ← Category.assoc]
  congr 1
  rw [← cancel_epi (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).hom, Iso.hom_inv_id, Proj.basicOpenIsoSpec_hom,
    Proj.basicOpenToSpec, Category.assoc, ← Spec.map_comp_assoc, ← Proj.basicOpenIsoAway_hom 𝒜 f f_deg hm,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp, ← IsAffineOpen.isoSpec_hom, Iso.hom_inv_id]
  exact Proj.isAffineOpen_basicOpen 𝒜 f f_deg hm

namespace ProjectiveLine

/-- `IsIntegral` for `P¹ = Proj K[x₀,x₁]`, spelled as Mathlib's `Proj` (from `SmoothProjectiveCurve.isIntegral`). -/
theorem projIsIntegral : IsIntegral ((Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K))) :=
  SmoothProjectiveCurve.isIntegral (ProjectiveLine.asSmoothProjectiveCurve K)

/-- `IsLocallyNoetherian` for `P¹ = Proj K[x₀,x₁]`. -/
theorem projIsLocallyNoetherian : IsLocallyNoetherian ((Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K))) :=
  Variety.isLocallyNoetherian (ProjectiveLine.asSmoothProjectiveCurve K).toVariety

/-- the structure morphism of `P¹ = Proj K[x₀,x₁]` over `K` (definitionally the one of
`ProjectiveSpace 1 K` / `ProjectiveLine.variety K`). -/
abbrev projOver : ((Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K))).Over (Spec (CommRingCat.of K)) :=
  ⟨Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) K) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial.homogeneousSubmodule (Fin 2) K 0)))⟩

attribute [local instance] projIsIntegral projIsLocallyNoetherian projOver

/-- the other index -/
def otherIndex (i : Fin 2) : {j : Fin 2 // j ≠ i} := ⟨1 - i, by fin_cases i <;> decide⟩

/-- Not registered as a global instance; used as a local instance below. -/
def uniqueOther (i : Fin 2) : Unique {j : Fin 2 // j ≠ i} where
  default := otherIndex i
  uniq := fun ⟨j, hj⟩ => Subtype.ext (by fin_cases i <;> fin_cases j <;> first | rfl | exact (hj rfl).elim)

attribute [local instance] uniqueOther

/-- chart coordinate ring iso `(K[x₀,x₁]_(xᵢ))₀ ≃+* K[X]`, `X ↦ x_j / x_i` (`j ≠ i`). -/
def chartCoord (i : Fin 2) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X i)
      ≃+* Polynomial K :=
  (ProjectiveSpace.chartRingEquiv 1 K i).trans
    (MvPolynomial.uniqueAlgEquiv K {j : Fin 2 // j ≠ i}).toRingEquiv

/-- the standard chart `Spec K[X] → (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K))`, `X ↦ x_j/x_i` -/
def chartι (i : Fin 2) : Spec (CommRingCat.of (Polynomial K)) ⟶ (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) :=
  Spec.map (chartCoord K i).toCommRingCatIso.hom ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X i)
      (ProjectiveSpace.X_mem 1 K i) Nat.one_pos

/-- Not registered as a global instance; used as a local instance below. -/
theorem chartι_isOpenImmersion (i : Fin 2) : IsOpenImmersion (chartι K i) := by
  unfold chartι
  exact @IsOpenImmersion.comp _ _ _ _ _ inferInstance
    (inferInstanceAs (IsOpenImmersion (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) K)
      (MvPolynomial.X i) (ProjectiveSpace.X_mem 1 K i) Nat.one_pos)))

attribute [local instance] chartι_isOpenImmersion

/-- the point at infinity `[0:1]` as the origin of the second chart -/
def inftyPoint : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) := chartι K 1 (originPoint K)

theorem nonempty_basicOpen (i : Fin 2) :
    Nonempty (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X i)) := by
  refine ⟨⟨chartι K i ⟨⊥, Ideal.isPrime_bot⟩, ?_⟩⟩
  have h : chartι K i ⟨⊥, Ideal.isPrime_bot⟩ ∈ (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) K)
      (MvPolynomial.X i) (ProjectiveSpace.X_mem 1 K i) Nat.one_pos).opensRange := by
    exact ⟨(Spec.map (chartCoord K i).toCommRingCatIso.hom) ⟨⊥, Ideal.isPrime_bot⟩, rfl⟩
  rwa [Proj.opensRange_awayι] at h

attribute [local instance] nonempty_basicOpen

theorem genericPoint_mem_basicOpen (i : Fin 2) :
    genericPoint (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X i) := by
  obtain ⟨⟨y, hy⟩⟩ := nonempty_basicOpen K i
  exact ((genericPoint_spec (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K))).mem_open_set_iff
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X i)).isOpen).mpr
    ⟨y, Set.mem_univ _, hy⟩

theorem genericPoint_mem_basicOpen_mul :
    genericPoint (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X 0 * MvPolynomial.X 1) := by
  rw [Proj.basicOpen_mul]
  exact ⟨genericPoint_mem_basicOpen K 0, genericPoint_mem_basicOpen K 1⟩

/-- polynomial `f ∈ K[X]` as a rational function on `(Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K))` via the `i`-th chart -/
def chartSectionHom (i : Fin 2) : Polynomial K →+* (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).functionField :=
  ((Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).germToFunctionField
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X i))).hom.comp
    (((Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X i)
      (ProjectiveSpace.X_mem 1 K i) Nat.one_pos).hom.hom).comp (chartCoord K i).symm.toRingHom)

theorem chartCoord_algebraMap (i : Fin 2) (c : K) :
    chartCoord K i (algebraMap (MvPolynomial.homogeneousSubmodule (Fin 2) K 0) _
      (algebraMap K (MvPolynomial.homogeneousSubmodule (Fin 2) K 0) c)) = Polynomial.C c := by
  have h1 : ProjectiveSpace.chartRingEquiv 1 K i (algebraMap (MvPolynomial.homogeneousSubmodule (Fin 2) K 0) _
      (algebraMap K (MvPolynomial.homogeneousSubmodule (Fin 2) K 0) c)) = MvPolynomial.C c := by
    rw [← ProjectiveSpace.polyToChart_C]
    exact RingHom.congr_fun (ProjectiveSpace.chartToPoly_comp_polyToChart 1 K i) (MvPolynomial.C c)
  show MvPolynomial.uniqueAlgEquiv K {j : Fin 2 // j ≠ i} (ProjectiveSpace.chartRingEquiv 1 K i _) = _
  rw [h1, ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
  rfl

theorem chartι_comp_over (i : Fin 2) :
    chartι K i ≫ ((Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) ↘ Spec (CommRingCat.of K)) = affineLineOver K := by
  change Spec.map (chartCoord K i).toCommRingCatIso.hom ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X i)
      (ProjectiveSpace.X_mem 1 K i) Nat.one_pos ≫
    (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) K) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial.homogeneousSubmodule (Fin 2) K 0)))) =
    Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  exact chartCoord_algebraMap K i c

/-- `chartCoord i (x_j / x_i) = X` for `j ≠ i`. -/
theorem chartCoord_isLocalizationElem (i j : Fin 2) (hij : j ≠ i) :
    chartCoord K i (HomogeneousLocalization.Away.isLocalizationElem (ProjectiveSpace.X_mem 1 K i)
      (ProjectiveSpace.X_mem 1 K j)) = Polynomial.X := by
  have h1 : ProjectiveSpace.chartRingEquiv 1 K i (HomogeneousLocalization.Away.isLocalizationElem
      (ProjectiveSpace.X_mem 1 K i) (ProjectiveSpace.X_mem 1 K j)) = MvPolynomial.X ⟨j, hij⟩ := by
    show ProjectiveSpace.chartToPoly 1 K i (HomogeneousLocalization.Away.mk _ (ProjectiveSpace.X_mem 1 K i) 1
      (MvPolynomial.X j ^ 1) _) = _
    rw [ProjectiveSpace.chartToPoly_mk, map_pow, ProjectiveSpace.dehomogenize_X_of_ne 1 K i hij, pow_one]
  show MvPolynomial.uniqueAlgEquiv K {j : Fin 2 // j ≠ i} (ProjectiveSpace.chartRingEquiv 1 K i _) = _
  rw [h1]
  show MvPolynomial.uniqueAlgEquiv K {j : Fin 2 // j ≠ i} (MvPolynomial.monomial (Finsupp.single ⟨j, hij⟩ 1) 1) = _
  rw [MvPolynomial.uniqueAlgEquiv_monomial, Subsingleton.elim (default : {j : Fin 2 // j ≠ i}) ⟨j, hij⟩,
    Finsupp.single_eq_same, Polynomial.monomial_one_one_eq_X]

theorem chartι_apply (i : Fin 2) (q : Spec (CommRingCat.of (Polynomial K))) :
    chartι K i q = Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X i)
      (ProjectiveSpace.X_mem 1 K i) Nat.one_pos (Spec.map (chartCoord K i).toCommRingCatIso.hom q) :=
  rfl

/-- membership of `x_j / x_i` in the prime transported to `Spec K[X]`: `x_j/x_i ∈ (Spec e) q ↔ X ∈ q` -/
theorem isLocalizationElem_mem_iff (i j : Fin 2) (hij : j ≠ i) (q : Spec (CommRingCat.of (Polynomial K))) :
    HomogeneousLocalization.Away.isLocalizationElem (ProjectiveSpace.X_mem 1 K i) (ProjectiveSpace.X_mem 1 K j) ∈
        (Spec.map (chartCoord K i).toCommRingCatIso.hom q).asIdeal ↔
      Polynomial.X ∈ q.asIdeal := by
  show chartCoord K i _ ∈ q.asIdeal ↔ _
  rw [chartCoord_isLocalizationElem K i j hij]

theorem mem_range_chartι_zero_or_eq_inftyPoint (y : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K))) :
    (∃ q, chartι K 0 q = y) ∨ y = inftyPoint K := by
  by_cases h0 : MvPolynomial.X (0 : Fin 2) ∈ y.asHomogeneousIdeal
  · right
    have h1 : MvPolynomial.X (1 : Fin 2) ∉ y.asHomogeneousIdeal := by
      obtain ⟨j, hj⟩ := AlgebraicGeometry.Proj.ProjectiveLinePointCoordinates.exists_coordinateOpen
        (y : ProjectiveLine K)
      fin_cases j
      · exact absurd h0 hj
      · exact hj
    have hy1 : y ∈ (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X 1)
        (ProjectiveSpace.X_mem 1 K 1) Nat.one_pos).opensRange := by
      rw [Proj.opensRange_awayι]; exact h1
    obtain ⟨q', hq'⟩ := hy1
    obtain ⟨q, hq⟩ := (Spec.map (chartCoord K 1).toCommRingCatIso.hom).homeomorph.surjective q'
    have hq2 : Spec.map (chartCoord K 1).toCommRingCatIso.hom q = q' := hq
    have hnot : Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X 1)
        (ProjectiveSpace.X_mem 1 K 1) Nat.one_pos (Spec.map (chartCoord K 1).toCommRingCatIso.hom q) ∉
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X 0) := by
      rw [hq2, hq']
      exact not_not.mpr h0
    have hpre : Spec.map (chartCoord K 1).toCommRingCatIso.hom q ∉
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X 1)
          (ProjectiveSpace.X_mem 1 K 1) Nat.one_pos ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X 0) := hnot
    rw [Proj.awayι_preimage_basicOpen _ _ _ (ProjectiveSpace.X_mem 1 K 0) Nat.one_pos] at hpre
    have hpre' : ¬ (HomogeneousLocalization.Away.isLocalizationElem (ProjectiveSpace.X_mem 1 K 1)
        (ProjectiveSpace.X_mem 1 K 0) ∉ (Spec.map (chartCoord K 1).toCommRingCatIso.hom q).asIdeal) := hpre
    have hXq : Polynomial.X ∈ q.asIdeal :=
      (isLocalizationElem_mem_iff K 1 0 zero_ne_one q).mp (not_not.mp hpre')
    have hq_eq : q = originPoint K := by
      apply PrimeSpectrum.ext
      have hle : Ideal.span {(Polynomial.X : Polynomial K)} ≤ q.asIdeal :=
        (Ideal.span_singleton_le_iff_mem _).mpr hXq
      have hmax : (Ideal.span {(Polynomial.X : Polynomial K)}).IsMaximal :=
        PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
      exact (hmax.eq_of_le q.isPrime.ne_top hle).symm
    rw [← hq', ← hq2, inftyPoint, chartι_apply, ← hq_eq]
  · left
    have hy0 : y ∈ (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X 0)
        (ProjectiveSpace.X_mem 1 K 0) Nat.one_pos).opensRange := by
      rw [Proj.opensRange_awayι]; exact h0
    obtain ⟨q', hq'⟩ := hy0
    obtain ⟨q, hq⟩ := (Spec.map (chartCoord K 0).toCommRingCatIso.hom).homeomorph.surjective q'
    have hq2 : Spec.map (chartCoord K 0).toCommRingCatIso.hom q = q' := hq
    exact ⟨q, by rw [chartι_apply, hq2]; exact hq'⟩

theorem inftyPoint_not_mem_range_chartι_zero : inftyPoint K ∉ Set.range (chartι K 0) := by
  rintro ⟨q, hq⟩
  have hmem : chartι K 0 q ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) K)
      (MvPolynomial.X 0) := by
    rw [← Proj.opensRange_awayι _ _ (ProjectiveSpace.X_mem 1 K 0) Nat.one_pos, chartι_apply]
    exact ⟨_, rfl⟩
  rw [hq, inftyPoint, chartι_apply] at hmem
  have hpre : Spec.map (chartCoord K 1).toCommRingCatIso.hom (originPoint K) ∈
      Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X 1)
        (ProjectiveSpace.X_mem 1 K 1) Nat.one_pos ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X 0) := hmem
  rw [Proj.awayι_preimage_basicOpen _ _ _ (ProjectiveSpace.X_mem 1 K 0) Nat.one_pos] at hpre
  have hpre' : HomogeneousLocalization.Away.isLocalizationElem (ProjectiveSpace.X_mem 1 K 1)
      (ProjectiveSpace.X_mem 1 K 0) ∉ (Spec.map (chartCoord K 1).toCommRingCatIso.hom (originPoint K)).asIdeal :=
    hpre
  apply hpre'
  rw [isLocalizationElem_mem_iff K 1 0 zero_ne_one]
  exact Ideal.mem_span_singleton_self _

theorem chartι_eq (i : Fin 2) :
    chartι K i = Spec.map ((Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin 2) K)
        (MvPolynomial.X i) (ProjectiveSpace.X_mem 1 K i) Nat.one_pos).inv ≫
        (chartCoord K i).toCommRingCatIso.hom) ≫
      (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X i)
        (ProjectiveSpace.X_mem 1 K i) Nat.one_pos).fromSpec := by
  rw [chartι, Proj.awayι_eq_SpecMap_fromSpec, Spec.map_comp, Category.assoc]

/-- the ring hom `Γ(P¹, D₊(xᵢ)) → K[X]` underlying the chart -/
def chartRingHom (i : Fin 2) :
    Γ((Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X i)) ⟶
      CommRingCat.of (Polynomial K) :=
  (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X i)
      (ProjectiveSpace.X_mem 1 K i) Nat.one_pos).inv ≫ (chartCoord K i).toCommRingCatIso.hom

/-- a polynomial as a section over `D₊(xᵢ)` -/
def chartSection (i : Fin 2) (f : Polynomial K) :
    Γ((Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X i)) :=
  (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X i)
    (ProjectiveSpace.X_mem 1 K i) Nat.one_pos).hom ((chartCoord K i).symm f)

theorem chartRingHom_chartSection (i : Fin 2) (f : Polynomial K) :
    chartRingHom K i (chartSection K i f) = f := by
  rw [chartRingHom, chartSection]
  erw [CommRingCat.comp_apply, Iso.hom_inv_id_apply]
  exact (chartCoord K i).apply_symm_apply f

theorem chartι_eq' (i : Fin 2) :
    chartι K i = Spec.map (chartRingHom K i) ≫
      (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X i)
        (ProjectiveSpace.X_mem 1 K i) Nat.one_pos).fromSpec :=
  chartι_eq K i

theorem chartSectionHom_apply (i : Fin 2) (f : Polynomial K) :
    chartSectionHom K i f = (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).presheaf.germ
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X i)) (genericPoint _)
      (genericPoint_mem_basicOpen K i) (chartSection K i f) := rfl

theorem functionFieldMap_chartι_chartSectionHom (i : Fin 2) (f : Polynomial K) :
    MiyaokaMori.OrdOpenImmersion.functionFieldMap (chartι K i) (chartSectionHom K i f) =
      polyToFunctionField K f := by
  rw [chartSectionHom_apply, polyToFunctionField_eq_germ]
  show ((Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).presheaf.stalkSpecializes _ ≫
      (chartι K i).stalkMap (genericPoint _)).hom _ = _
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]
  erw [AlgebraicGeometry.germ_app_of_eq_SpecMap_fromSpec _ (chartRingHom K i) (chartι K i) (chartι_eq' K i)
    (chartSection K i f), chartRingHom_chartSection]

/-- a chart section, restricted to the overlap `D₊(x₀x₁)` -/
theorem chartSectionHom_eq_germ_mul (i j : Fin 2)
    (hij : MvPolynomial.X 0 * MvPolynomial.X 1 = (MvPolynomial.X i : MvPolynomial (Fin 2) K) * MvPolynomial.X j)
    (f : Polynomial K) :
    chartSectionHom K i f =
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).presheaf.germ
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X 0 * MvPolynomial.X 1))
        (genericPoint _) (genericPoint_mem_basicOpen_mul K)
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X 0 * MvPolynomial.X 1)
          (HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin 2) K)
            (ProjectiveSpace.X_mem 1 K j) hij ((chartCoord K i).symm f))) := by
  show (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).presheaf.germ
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X i)) (genericPoint _) _
    ((Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X i)
      (ProjectiveSpace.X_mem 1 K i) Nat.one_pos).hom ((chartCoord K i).symm f)) = _
  rw [Proj.basicOpenIsoAway_hom]
  have h := congrArg (fun φ => φ.hom ((chartCoord K i).symm f))
    (Proj.awayMap_awayToSection (MvPolynomial.homogeneousSubmodule (Fin 2) K) (ProjectiveSpace.X_mem 1 K j) hij)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  erw [h]
  exact ((Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).presheaf.germ_res_apply (homOfLE _) (genericPoint _) _ _).symm

theorem chartCoord_symm_C (i : Fin 2) (c : K) :
    (chartCoord K i).symm (Polynomial.C c) =
      HomogeneousLocalization.fromZeroRingHom (MvPolynomial.homogeneousSubmodule (Fin 2) K) _
        (algebraMap K (MvPolynomial.homogeneousSubmodule (Fin 2) K 0) c) := by
  rw [RingEquiv.symm_apply_eq]
  exact (chartCoord_algebraMap K i c).symm

theorem chartCoord_symm_X (i j : Fin 2) (hij : j ≠ i) :
    (chartCoord K i).symm Polynomial.X =
      HomogeneousLocalization.Away.isLocalizationElem (ProjectiveSpace.X_mem 1 K i) (ProjectiveSpace.X_mem 1 K j) := by
  rw [RingEquiv.symm_apply_eq]
  exact (chartCoord_isLocalizationElem K i j hij).symm

theorem chartSectionHom_C (c : K) :
    chartSectionHom K 0 (Polynomial.C c) = chartSectionHom K 1 (Polynomial.C c) := by
  rw [chartSectionHom_eq_germ_mul K 0 1 rfl, chartSectionHom_eq_germ_mul K 1 0 (mul_comm _ _),
    chartCoord_symm_C, chartCoord_symm_C, HomogeneousLocalization.awayMap_fromZeroRingHom,
    HomogeneousLocalization.awayMap_fromZeroRingHom]

/-- `(x₁/x₀) · (x₀/x₁) = 1` in `(K[x₀,x₁]_(x₀x₁))₀` -/
theorem awayMap_isLocalizationElem_mul :
    HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin 2) K) (ProjectiveSpace.X_mem 1 K 1)
        (rfl : MvPolynomial.X 0 * MvPolynomial.X 1 = (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) * MvPolynomial.X 1)
        (HomogeneousLocalization.Away.isLocalizationElem (ProjectiveSpace.X_mem 1 K 0) (ProjectiveSpace.X_mem 1 K 1)) *
      HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin 2) K) (ProjectiveSpace.X_mem 1 K 0)
        (mul_comm (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) (MvPolynomial.X 1))
        (HomogeneousLocalization.Away.isLocalizationElem (ProjectiveSpace.X_mem 1 K 1) (ProjectiveSpace.X_mem 1 K 0)) = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one, HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, Submonoid.coe_one, one_mul, mul_one]
  ring

theorem chartSectionHom_X_mul_chartSectionHom_X :
    chartSectionHom K 0 Polynomial.X * chartSectionHom K 1 Polynomial.X = 1 := by
  rw [chartSectionHom_eq_germ_mul K 0 1 rfl, chartSectionHom_eq_germ_mul K 1 0 (mul_comm _ _)]
  erw [← map_mul, ← map_mul]
  rw [chartCoord_symm_X K 0 1 one_ne_zero, chartCoord_symm_X K 1 0 zero_ne_one,
    awayMap_isLocalizationElem_mul, map_one, map_one]

end ProjectiveLine

/-! ## assembly: the principal divisor of `cs₀ a` has degree `0`, and the theorem for `Proj K[x₀,x₁]` -/

namespace ProjectiveLine

attribute [local instance] projIsIntegral projIsLocallyNoetherian projOver
attribute [local instance] uniqueOther chartι_isOpenImmersion


/-- An open immersion has residue degree `1` at every point (`residueFieldMap` is an isomorphism). -/
theorem residueDegree_eq_one_of_isOpenImmersion {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] (x : U) : f.residueDegree x = 1 := by
  letI : Algebra (X.residueField (f.base x)) (U.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  change Module.finrank (X.residueField (f.base x)) (U.residueField x) = 1
  exact Module.finrank_of_bijective_algebraMap
    ((asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv.bijective)

/-- the residue degree of a point in the `i`-th chart is computed on `Spec K[X]` -/
theorem residueDegree_chartι (i : Fin 2) (q : Spec (CommRingCat.of (Polynomial K))) :
    Scheme.Hom.residueDegree ((Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) ↘ Spec (CommRingCat.of K)) (chartι K i q) =
      (affineLineOver K).residueDegree q := by
  have h := AlgebraicGeometry.Intersection.residueDegree_comp (chartι K i) ((Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) ↘ Spec (CommRingCat.of K)) q
  rw [chartι_comp_over, residueDegree_eq_one_of_isOpenImmersion (chartι K i), mul_one] at h
  exact h.symm

/-- `ord` of a chart-`i` rational function at a point of chart `i` -/
theorem ord_chartι (i : Fin 2) (g : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).functionField) (q : Spec (CommRingCat.of (Polynomial K))) :
    (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).ord g (chartι K i q) = (Spec (CommRingCat.of (Polynomial K))).ord (MiyaokaMori.OrdOpenImmersion.functionFieldMap (chartι K i) g) q :=
  (MiyaokaMori.OrdOpenImmersion.ord_functionFieldMap (chartι K i) g q).symm

theorem chartSectionHom_ne_zero (i : Fin 2) {a : Polynomial K} (ha : a ≠ 0) :
    chartSectionHom K i a ≠ 0 := by
  intro h0
  apply ha
  apply polyToFunctionField_injective K
  rw [map_zero, ← functionFieldMap_chartι_chartSectionHom, h0, map_zero]

/-- `cs₀ a = cs₁ (reverse a) · (cs₀ X)^N` (`Polynomial.eval₂_reverse_mul_pow`) -/
theorem chartSectionHom_zero_eq (a : Polynomial K) :
    chartSectionHom K 0 a =
      chartSectionHom K 1 a.reverse * chartSectionHom K 0 Polynomial.X ^ a.natDegree := by
  letI : Invertible (chartSectionHom K 0 Polynomial.X) := ⟨chartSectionHom K 1 Polynomial.X,
    by rw [mul_comm]; exact chartSectionHom_X_mul_chartSectionHom_X K,
    chartSectionHom_X_mul_chartSectionHom_X K⟩
  have hinv : ⅟(chartSectionHom K 0 Polynomial.X) = chartSectionHom K 1 Polynomial.X := rfl
  have h := Polynomial.eval₂_reverse_mul_pow ((chartSectionHom K 0).comp Polynomial.C)
    (chartSectionHom K 0 Polynomial.X) a
  have h0 : ∀ p : Polynomial K, Polynomial.eval₂ ((chartSectionHom K 0).comp Polynomial.C)
      (chartSectionHom K 0 Polynomial.X) p = chartSectionHom K 0 p := fun p => by
    conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq p]
    simp only [Polynomial.eval₂_eq_sum, Polynomial.sum, map_sum, map_mul, map_pow,
      RingHom.comp_apply]
  have h1 : ∀ p : Polynomial K, Polynomial.eval₂ ((chartSectionHom K 0).comp Polynomial.C)
      (⅟(chartSectionHom K 0 Polynomial.X)) p = chartSectionHom K 1 p := fun p => by
    conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq p]
    simp only [Polynomial.eval₂_eq_sum, Polynomial.sum, map_sum, map_mul, map_pow,
      RingHom.comp_apply, chartSectionHom_C, hinv]
  rw [h0, h1] at h
  exact h.symm

theorem functionFieldMap_chartι_one_chartSectionHom_zero (a : Polynomial K) :
    MiyaokaMori.OrdOpenImmersion.functionFieldMap (chartι K 1) (chartSectionHom K 0 a) =
      polyToFunctionField K a.reverse / polyToFunctionField K Polynomial.X ^ a.natDegree := by
  rw [chartSectionHom_zero_eq, map_mul, map_pow, functionFieldMap_chartι_chartSectionHom]
  have hX : MiyaokaMori.OrdOpenImmersion.functionFieldMap (chartι K 1) (chartSectionHom K 0 Polynomial.X) *
      polyToFunctionField K Polynomial.X = 1 := by
    rw [← functionFieldMap_chartι_chartSectionHom K 1, ← map_mul,
      chartSectionHom_X_mul_chartSectionHom_X, map_one]
  rw [eq_inv_of_mul_eq_one_left hX, inv_pow, div_eq_mul_inv]

/-- finiteness of the support of the principal divisor of `cs₀ a` -/
theorem finite_support_chartSectionHom_zero {a : Polynomial K} (ha : a ≠ 0) :
    (Function.support fun y : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) => (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).ord (chartSectionHom K 0 a) y * ((Scheme.Hom.residueDegree ((Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) ↘ Spec (CommRingCat.of K)) y : ℕ) : ℤ)).Finite := by
  have hS := affineLine_finite_support_ord K a ha
  refine Set.Finite.subset ((hS.image (chartι K 0)).insert (inftyPoint K)) ?_
  intro y hy
  rcases mem_range_chartι_zero_or_eq_inftyPoint K y with ⟨q, rfl⟩ | rfl
  · refine Set.mem_insert_of_mem _ ⟨q, ?_, rfl⟩
    intro hq
    apply hy
    show (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).ord (chartSectionHom K 0 a) (chartι K 0 q) * _ = 0
    rw [ord_chartι, functionFieldMap_chartι_chartSectionHom]
    simp only at hq
    rw [hq, zero_mul]
  · exact Set.mem_insert _ _

/-- the principal divisor of `cs₀ a` has degree `0` -/
theorem finsum_ord_chartSectionHom_zero {a : Polynomial K} (ha : a ≠ 0) :
    ∑ᶠ y : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)), (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).ord (chartSectionHom K 0 a) y * ((Scheme.Hom.residueDegree ((Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) ↘ Spec (CommRingCat.of K)) y : ℕ) : ℤ) = 0 := by
  set F : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) → ℤ := fun y => (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).ord (chartSectionHom K 0 a) y * ((Scheme.Hom.residueDegree ((Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) ↘ Spec (CommRingCat.of K)) y : ℕ) : ℤ) with hF
  have huniv : (Set.univ : Set (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K))) = insert (inftyPoint K) (Set.range (chartι K 0)) := by
    ext y
    simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_range, true_iff]
    rcases mem_range_chartι_zero_or_eq_inftyPoint K y with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hfin := finite_support_chartSectionHom_zero K ha
  calc ∑ᶠ y : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)), F y = ∑ᶠ y ∈ (Set.univ : Set (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K))), F y := (finsum_mem_univ F).symm
    _ = ∑ᶠ y ∈ insert (inftyPoint K) (Set.range (chartι K 0)), F y := by rw [huniv]
    _ = F (inftyPoint K) + ∑ᶠ y ∈ Set.range (chartι K 0), F y :=
        finsum_mem_insert' F (inftyPoint_not_mem_range_chartι_zero K) (hfin.subset Set.inter_subset_right)
    _ = F (inftyPoint K) + ∑ᶠ q : Spec (CommRingCat.of (Polynomial K)), F (chartι K 0 q) := by
        rw [finsum_mem_range (chartι K 0).isOpenEmbedding.injective]
    _ = -(a.natDegree : ℤ) + a.natDegree := by
        congr 1
        · simp only [hF, inftyPoint, ord_chartι, residueDegree_chartι,
            functionFieldMap_chartι_one_chartSectionHom_zero, affineLine_ord_originPoint K a ha,
            affineLine_residueDegree_originPoint, Nat.cast_one, mul_one]
        · simp only [hF, ord_chartι, residueDegree_chartι, functionFieldMap_chartι_chartSectionHom]
          exact affineLine_finsum_ord_mul_residueDegree K a ha
    _ = 0 := by ring

/-- The principal divisor of any rational function on `Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)`
has degree zero. -/
theorem sum_ord_mul_residueDegree_eq_zero_proj
    (h : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).functionFieldˣ) :
    ∑ᶠ y : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)),
      Scheme.ord (h : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).functionField) y *
        ((Scheme.Hom.residueDegree
          ((Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) ↘ Spec (CommRingCat.of K)) y : ℕ) : ℤ) = 0 := by
  let _ := AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (Polynomial K))
  have _ := AlgebraicGeometry.functionField_isFractionRing_of_affine (CommRingCat.of (Polynomial K))
  set ψ := MiyaokaMori.OrdOpenImmersion.functionFieldMap (chartι K 0) with hψ
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := CommRingCat.of (Polynomial K))
    (ψ (h : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).functionField))
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hψh : ψ (h : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).functionField) ≠ 0 := by
    rw [map_ne_zero_iff ψ ψ.injective]
    exact h.ne_zero
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hψh
    rw [← hab, map_zero, zero_div]
  have hh : (h : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).functionField) = chartSectionHom K 0 a / chartSectionHom K 0 b := by
    apply ψ.injective
    rw [map_div₀, hψ, functionFieldMap_chartι_chartSectionHom, functionFieldMap_chartι_chartSectionHom]
    exact hab.symm
  have hfa := finite_support_chartSectionHom_zero K ha0
  have hfb := finite_support_chartSectionHom_zero K hb0
  have hpt : ∀ y : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)), (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).ord (h : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).functionField) y * ((Scheme.Hom.residueDegree ((Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) ↘ Spec (CommRingCat.of K)) y : ℕ) : ℤ) =
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).ord (chartSectionHom K 0 a) y * ((Scheme.Hom.residueDegree ((Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) ↘ Spec (CommRingCat.of K)) y : ℕ) : ℤ) - (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)).ord (chartSectionHom K 0 b) y * ((Scheme.Hom.residueDegree ((Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) ↘ Spec (CommRingCat.of K)) y : ℕ) : ℤ) := by
    intro y
    rw [hh, Scheme.ord_div_eq_sub (chartSectionHom_ne_zero K 0 ha0) (chartSectionHom_ne_zero K 0 hb0),
      sub_mul]
  rw [finsum_congr hpt, finsum_sub_distrib hfa hfb, finsum_ord_chartSectionHom_zero K ha0,
    finsum_ord_chartSectionHom_zero K hb0, sub_zero]

end ProjectiveLine


end
