import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOverTwist
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.WeightedProjCoordinateFormula
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModuleChartPullback

/-! # The standard chart of projective space over a ring and its coordinate ratios

The standard affine chart `D_+(T_j) ⊆ P^N_R = Proj R[T_0..T_N]` over a **commutative ring** `R`:
the coordinate ratios `T_i/T_j ∈ (R[T]_{T_j})_0`, the ring map `(R[T]_{T_j})_0 → Γ(T, O)` induced by an
evaluation `e : R[T] → Γ(T, O)` with `e(T_j)` a unit (`chartEvaluation`), the chart morphism
`T → D_+(T_j)` (`chartMap`), its compatibility with Mathlib's `Proj.fromOfGlobalSections`
(`chartMap_ι`), the pullback formula `chartMap^♯(T_i/T_j) · e(T_j) = e(T_i)`, surjectivity of the chart
evaluation when `e` is surjective and `e(T_j) = 1`, and the frame `T_j` of `O(1)` on `D_+(T_j)`
(`targetFrameIso`, sending `T_i|_{D_+(T_j)}` to `T_i/T_j`).

This is the one definition of the standard chart data; the field-specific material
(`fieldEvaluation`, `fieldTupleMorphism`, …) is in `ProjectiveCoordinateRatio` as constructions about
these definitions (`AlgebraicGeometry.Proj.projectiveGrading k n` is an `abbrev` of
`MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k`). The graded ring is spelled
`MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R` so that the target scheme is literally
`ProjectiveSpaceOver n R`.

Source: Stacks 01M6/01M9 (the standard charts of Proj), Hartshorne II.7.1.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjectiveSpaceOverChart

open AlgebraicGeometry

variable {R : Type u} [CommRing R]

/-- The equal-degree fraction `T_i/T_j` in the chart ring `(R[T]_{T_j})_0`. -/
def ratioElement (n : ℕ) (i j : Fin (n + 1)) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X j) :=
  HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (MvPolynomial.isHomogeneous_X R j) 1 (MvPolynomial.X i)
    (by simpa using MvPolynomial.isHomogeneous_X R i)

/-- The structure-sheaf section `T_i/T_j` on `D_+(T_j)`. -/
def ratioSection (n : ℕ) (i j : Fin (n + 1)) :
    Γ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X j)).toScheme, ⊤) :=
  (Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)
    (MvPolynomial.isHomogeneous_X R j) Nat.zero_lt_one).hom.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of
        (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (MvPolynomial.X j)))).inv
          (ratioElement (R := R) n i j))

/-- The ring map `(R[T]_{T_j})_0 → S` induced by `e : R[T] → S` when `e(T_j)` is a unit. -/
def chartEvaluation {S : Type u} [CommRing S] (n : ℕ)
    (e : MvPolynomial (Fin (n + 1)) R →+* S) (j : Fin (n + 1))
    (hj : IsUnit (e (MvPolynomial.X j))) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X j) →+* S :=
  (IsLocalization.Away.lift (S := Localization.Away (MvPolynomial.X (R := R) j))
    (MvPolynomial.X j) hj).comp
      (algebraMap (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X j)) (Localization.Away (MvPolynomial.X j)))

/-- `chartEvaluation (T_i/T_j) · e(T_j) = e(T_i)`. -/
theorem chartEvaluation_ratio_mul {S : Type u} [CommRing S] (n : ℕ)
    (e : MvPolynomial (Fin (n + 1)) R →+* S) (j : Fin (n + 1))
    (hj : IsUnit (e (MvPolynomial.X j))) (i : Fin (n + 1)) :
    chartEvaluation n e j hj (ratioElement n i j) * e (MvPolynomial.X j) =
      e (MvPolynomial.X i) := by
  let l := IsLocalization.Away.lift (S := Localization.Away (MvPolynomial.X (R := R) j))
    (MvPolynomial.X j) hj
  have h := congrArg l
    (IsLocalization.mk'_spec (Localization.Away (MvPolynomial.X (R := R) j))
      (MvPolynomial.X i)
      (⟨MvPolynomial.X j, ⟨1, pow_one _⟩⟩ :
        Submonoid.powers (MvPolynomial.X (R := R) j)))
  simpa only [chartEvaluation, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    ratioElement, HomogeneousLocalization.Away.mk, HomogeneousLocalization.val_mk,
    pow_one, Localization.mk_eq_mk',
    map_mul, l, IsLocalization.Away.lift_eq] using h

/-- Degree-`d` homogeneous fraction evaluated: `chartEvaluation (a/T_j^d) · e(T_j)^d = e(a)`. -/
theorem chartEvaluation_mk_mul_pow {S : Type u} [CommRing S] (n : ℕ)
    (e : MvPolynomial (Fin (n + 1)) R →+* S) (j : Fin (n + 1))
    (hj : IsUnit (e (MvPolynomial.X j))) (d : ℕ) (a : MvPolynomial (Fin (n + 1)) R)
    (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R (d • 1)) :
    chartEvaluation n e j hj
        (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (MvPolynomial.isHomogeneous_X R j) d a ha) * e (MvPolynomial.X j) ^ d =
      e a := by
  let l := IsLocalization.Away.lift (S := Localization.Away (MvPolynomial.X (R := R) j))
    (MvPolynomial.X j) hj
  have h := congrArg l
    (IsLocalization.mk'_spec (Localization.Away (MvPolynomial.X (R := R) j)) a
      (⟨MvPolynomial.X j ^ d, ⟨d, rfl⟩⟩ : Submonoid.powers (MvPolynomial.X (R := R) j)))
  simpa only [chartEvaluation, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk', map_mul, map_pow, l,
    IsLocalization.Away.lift_eq] using h

/-- If `e` is surjective and `e (T_j) = 1`, the chart evaluation is surjective. -/
theorem chartEvaluation_surjective {S : Type u} [CommRing S] (n : ℕ)
    (e : MvPolynomial (Fin (n + 1)) R →+* S) (j : Fin (n + 1))
    (hj1 : e (MvPolynomial.X j) = 1) (he : Function.Surjective e) :
    Function.Surjective (chartEvaluation n e j (hj1 ▸ isUnit_one)) := by
  have hj : IsUnit (e (MvPolynomial.X j)) := hj1 ▸ isUnit_one
  set φ := chartEvaluation n e j hj with hφ
  have key : ∀ p : MvPolynomial (Fin (n + 1)) R, e p ∈ φ.range := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      refine ⟨HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.isHomogeneous_X R j) 0 (MvPolynomial.C c) ?_, ?_⟩
      · simp
      · have h := chartEvaluation_mk_mul_pow n e j hj 0 (MvPolynomial.C c) (by simp)
        rwa [pow_zero, mul_one] at h
    | add p q hp hq =>
      rw [map_add]
      exact φ.range.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      refine φ.range.mul_mem hp ⟨ratioElement n i j, ?_⟩
      have h := chartEvaluation_ratio_mul n e j hj i
      rwa [hj1, mul_one] at h
  intro y
  obtain ⟨p, rfl⟩ := he y
  exact key p

/-- The chart morphism `T → D_+(T_j) ⊆ P^n_R` attached to an evaluation with `e(T_j)` a unit:
`T → Spec Γ(T) → Spec (R[T]_{T_j})_0 ≅ D_+(T_j)`. -/
def chartMap (T : Scheme.{u}) (n : ℕ)
    (e : MvPolynomial (Fin (n + 1)) R →+* Γ(T, ⊤)) (j : Fin (n + 1))
    (hj : IsUnit (e (MvPolynomial.X j))) :
    T ⟶ (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X j)).toScheme :=
  T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chartEvaluation n e j hj)) ≫
    (Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X R j) Nat.zero_lt_one).inv

/-- `chartMap ≫ D_+(T_j).ι = Proj.fromOfGlobalSections e`. -/
theorem chartMap_ι (T : Scheme.{u}) (n : ℕ)
    (e : MvPolynomial (Fin (n + 1)) R →+* Γ(T, ⊤))
    (he : (HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toIdeal.map e = ⊤)
    (j : Fin (n + 1)) (hj : IsUnit (e (MvPolynomial.X j))) :
    chartMap T n e j hj ≫
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)).ι =
      Proj.fromOfGlobalSections (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) e he := by
  let t : MvPolynomial (Fin (n + 1)) R := MvPolynomial.X j
  let x : Γ(T, ⊤) := e t
  let L : (T.basicOpen x).toScheme ⟶ Spec (.of (Localization.Away x)) :=
    (T.isoOfEq (T.toSpecΓ_preimage_basicOpen x)).inv ≫
      T.toSpecΓ ∣_ PrimeSpectrum.basicOpen x ≫ (basicOpenIsoSpecAway x).hom
  let m : Localization.Away t →+* Localization.Away x :=
    IsLocalization.map (M := Submonoid.powers t) (T := Submonoid.powers x)
      (Localization.Away x) e (by
        intro b hb
        obtain ⟨d, rfl⟩ := hb
        exact ⟨d, (map_pow e t d).symm⟩)
  let l : Localization.Away x →+* Γ(T, ⊤) :=
    IsLocalization.Away.lift x (show IsUnit ((RingHom.id Γ(T, ⊤)) x) from hj)
  let a : Localization.Away t →+* Γ(T, ⊤) := IsLocalization.Away.lift t hj
  have hl : l.comp (algebraMap Γ(T, ⊤) (Localization.Away x)) = RingHom.id _ :=
    IsLocalization.Away.lift_comp x _
  have hm : l.comp m = a := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers t)
    refine RingHom.ext fun b ↦ ?_
    change l (m (algebraMap _ _ b)) = a (algebraMap _ _ b)
    simp only [m, IsLocalization.map_eq, l, a, IsLocalization.Away.lift_eq,
      RingHom.id_apply]
  have key : ∀ (V : (Spec Γ(T, ⊤)).Opens) (hV : T.toSpecΓ ⁻¹ᵁ V = T.basicOpen x),
      (T.isoOfEq hV).inv ≫ T.toSpecΓ ∣_ V ≫ V.ι = (T.basicOpen x).ι ≫ T.toSpecΓ := by
    intro V hV
    rw [morphismRestrict_ι, ← Category.assoc, Scheme.isoOfEq_inv_ι]
  have hL : L = (T.basicOpen x).ι ≫ T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom l) := by
    apply (cancel_mono
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (Localization.Away x))))).mp
    simp only [L, Category.assoc, basicOpenIsoSpecAway_hom_SpecMap, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hl, CommRingCat.ofHom_id, Spec.map_id]
    exact (key _ (T.toSpecΓ_preimage_basicOpen x)).trans (Category.comp_id _).symm
  have hlocal :
      Proj.toBasicOpenOfGlobalSections (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) e rfl
          Nat.zero_lt_one (MvPolynomial.isHomogeneous_X R j) =
        (T.basicOpen x).ι ≫ chartMap T n e j hj := by
    change L ≫ Spec.map (CommRingCat.ofHom
      (m.comp (algebraMap
        (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) t)
        (Localization.Away t)))) ≫
        (Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) t
          (MvPolynomial.isHomogeneous_X R j) Nat.zero_lt_one).inv = _
    rw [hL]
    simp only [chartMap, chartEvaluation, Category.assoc,
      ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hm, a, t]
  have htop : T.basicOpen x = ⊤ := T.basicOpen_of_isUnit hj
  have : IsIso (T.basicOpen x).ι := by
    rw [htop]
    change IsIso T.topIso.hom
    infer_instance
  apply (cancel_epi (T.basicOpen x).ι).mp
  rw [← Category.assoc, ← hlocal]
  rw [← Proj.fromOfGlobalSections_resLE (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) e he
    Nat.zero_lt_one (MvPolynomial.isHomogeneous_X R j)]
  exact Scheme.Hom.resLE_comp_ι _ _

/-- Pulling back the ratio section along the chart map evaluates the same fraction. -/
theorem chartMap_appTop_ratio (T : Scheme.{u}) (n : ℕ)
    (e : MvPolynomial (Fin (n + 1)) R →+* Γ(T, ⊤)) (j : Fin (n + 1))
    (hj : IsUnit (e (MvPolynomial.X j))) (i : Fin (n + 1)) :
    (chartMap T n e j hj).appTop (ratioSection n i j) =
      chartEvaluation n e j hj (ratioElement n i j) := by
  let φ := chartEvaluation n e j hj
  let z := ratioElement (R := R) n i j
  have hnat : (Spec.map (CommRingCat.ofHom φ)).appTop
      ((Scheme.ΓSpecIso _).inv z) = (Scheme.ΓSpecIso _).inv (φ z) := by
    simpa only [CommRingCat.comp_apply, CategoryTheory.comp_apply,
      CommRingCat.hom_ofHom, CommRingCat.of_carrier] using
      congrArg (fun h ↦ h z) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
  change ((chartMap T n e j hj) ≫
    (Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X R j) Nat.zero_lt_one).hom).appTop
        ((Scheme.ΓSpecIso _).inv z) = φ z
  simp only [chartMap, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hnat, Scheme.toSpecΓ_appTop,
    Iso.inv_hom_id_apply]

/-- `chartMap^♯(T_i/T_j) · e(T_j) = e(T_i)` as sections. -/
theorem chartMap_appTop_ratio_mul (T : Scheme.{u}) (n : ℕ)
    (e : MvPolynomial (Fin (n + 1)) R →+* Γ(T, ⊤)) (j : Fin (n + 1))
    (hj : IsUnit (e (MvPolynomial.X j))) (i : Fin (n + 1)) :
    (chartMap T n e j hj).appTop (ratioSection n i j) * e (MvPolynomial.X j) =
      e (MvPolynomial.X i) := by
  rw [chartMap_appTop_ratio]
  exact chartEvaluation_ratio_mul n e j hj i

/-! ## The frame `T_j` of `O(1)` on `D_+(T_j)` -/

open MiyaokaMori.WeightedJets AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback

set_option backward.isDefEq.respectTransparency false in
/-- The restricted ratio element is the coordinate-ratio section of the chart. -/
theorem awayToSection_ratioElement_eq_ratioSection (N : ℕ) (i l : Fin (N + 1)) :
    ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (MvPolynomial.X i)).ι.appIso ⊤).hom
      ((Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).presheaf.map
        (homOfLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          (MvPolynomial.X i)).ι_image_top.le).op
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)
          (ratioElement N l i))) =
      ratioSection N l i := by
  rw [Scheme.Opens.ι_appIso]
  unfold ratioSection
  rw [Proj.basicOpenIsoSpec_hom]
  change _ = (Proj.basicOpenToSpec (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
    (MvPolynomial.X i)).app ⊤ _
  rw [Proj.basicOpenToSpec_app_top]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply, Scheme.Opens.topIso_inv]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Dividing `T_l` by `T_i` on `D_+(T_i)` gives the coordinate-ratio element. -/
theorem divide_coordinate_eq_ratioElement (N : ℕ) (i l : Fin (N + 1)) :
    ProjTwisting.divideSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) 1
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X R i)
      (U := (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)))
      (fun x ↦ x.2)
      (ProjTwisting.homogeneousSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) 1
        (MvPolynomial.X l) (MvPolynomial.isHomogeneous_X R l)
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))) =
      Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)
        (ratioElement N l i) := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  rw [ProjTwisting.divideSection_val]
  change Localization.mk (MvPolynomial.X l) 1 *
    Localization.mk 1 ⟨MvPolynomial.X i, x.2⟩ = _
  rw [Localization.mk_mul, mul_one, one_mul]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  simp only [ratioElement, HomogeneousLocalization.Away.val_mk, pow_one, Localization.mk_eq_mk',
    IsLocalization.map_mk', RingHom.id_apply]

/-- Division by `T_i` trivializes `O(1)` on `D_+(T_i)` (`O(1)` spelled `ProjTwisting.sheaf 𝒜 ((1 : ℕ) : ℤ)`,
which is `projectiveSpaceOverTwist R N 1` definitionally). -/
def targetFrameIso (N : ℕ) (i : Fin (N + 1)) :
    (ProjTwisting.sheaf (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) ((1 : ℕ) : ℤ)).restrict
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)).ι ≅
      SheafOfModules.unit (R :=
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          (MvPolynomial.X i)).toScheme.ringCatSheaf) :=
  ProjTwisting.homogeneousCoordinateFrameIso (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) 1
    (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X R i)
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))
    (fun x ↦ x.2)

/-- The target frame sends `T_l|_{D_+(T_i)}` to the ratio section `T_l/T_i`. -/
theorem targetFrameIso_coordinate (N : ℕ) (i l : Fin (N + 1)) :
    (targetFrameIso (R := R) N i).hom.app ⊤
        (restrictedGlobalSection
          (ProjTwisting.sheaf (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) ((1 : ℕ) : ℤ))
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))
          (ProjTwisting.homogeneousSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) 1
            (MvPolynomial.X l) (MvPolynomial.isHomogeneous_X R l) ⊤)) =
      ratioSection N l i :=
  (ProjTwisting.homogeneousCoordinateFrameIso_hom_app_top_of_eq
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) 1
    (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X R i)
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))
    (fun x ↦ x.2)
    (MvPolynomial.X l) (MvPolynomial.isHomogeneous_X R l)
    (V' := (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)))
    (fun x ↦ x.2)
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X i)).ι_image_top.le rfl (targetFrameIso (R := R) N i) rfl _ rfl _
    (divide_coordinate_eq_ratioElement N i l)).trans
    (awayToSection_ratioElement_eq_ratioSection N i l)

end ProjectiveSpaceOverChart

/-! ## The target frame on the coordinate sections

The namespace `AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback` is kept because
`ProjectivizationOfNowhereZeroTuple` and `ProjectiveLineStdChartTrivialization` use the qualified name. -/

namespace AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback

open AlgebraicGeometry MiyaokaMori.WeightedJets

/-- The target frame `Xᵢ` of `O(1)` on `D₊(Xᵢ)` (`ProjectiveSpaceOverChart.targetFrameIso`) sends the
coordinate section `Xₗ` to the coordinate-ratio section `Xₗ/Xᵢ`. This is
`ProjectiveSpaceOverChart.targetFrameIso_coordinate` with the coordinate section spelled through the
`projectiveSpaceCoordinate` (definitionally `ProjTwisting.homogeneousSection … (X l) … ⊤`). -/
theorem targetFrameIso_coordinate {k : Type u} [Field k] {N : ℕ} (i l : Fin (N + 1)) :
    (ProjectiveSpaceOverChart.targetFrameIso (R := k) N i).hom.app ⊤
        (restrictedGlobalSection (ProjTwisting.sheaf (AlgebraicGeometry.Proj.projectiveGrading k N) 1)
          (Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X i))
          (projectiveSpaceCoordinate k N l)) =
      ProjectiveSpaceOverChart.ratioSection N l i :=
  ProjectiveSpaceOverChart.targetFrameIso_coordinate N i l

end AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback

end
