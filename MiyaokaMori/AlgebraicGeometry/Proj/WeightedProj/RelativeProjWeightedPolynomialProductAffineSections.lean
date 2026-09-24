import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualFreeSheafFree
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQCAlgebraSpecPolynomialIso
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.OfGradedQCAlgebra

/-! # Sections of the weighted polynomial algebra

Sections of the weighted polynomial algebra: for every scheme `X`, every open `U` and every weight
vector `w` with all `w i ≥ 1`, the graded sections ring `Γ(U, weightedPolynomialQCAlgebra X w hw)`
is the weighted polynomial ring `Γ(X, U)[x_σ]` (degree `j` piece ↔ weighted homogeneous polynomials
of weight `j`; the structure map `sectionsUnitHom U` ↔ the constants `C`).

This is step 2 of the affine base case `relativeProj_weightedPolynomialQCAlgebra_spec_iso`.

Proof. The `j`-th piece is `Γ(U, O_U^{(I_j)})` with `I_j = weightedMonomials w j` **finite** (all weights
are `≥ 1`, so every exponent is `≤ j`), and a section of the free sheaf on a finite index set is
`∑ coord_d s • e_d` (`section_decomp'`, `coord_e`). The generators satisfy
`e_d · e_{d'} = e_{d+d'}` in the sections ring (the multiplication of the algebra is
`freeTensorFreeIso ≫ freeMap (+)`, `ιM_tensor_ιM_mulHom`, evaluated on sections through
`tensorHom_tensorSections` and `leftUnitor_app_tensorSections`) and `e_0 = 1`. Hence
`d ↦ e_d` is a monoid homomorphism `Multiplicative (σ →₀ ℕ) →* A` and, with the structure map
`Γ(X,U) →+* A`, `AddMonoidAlgebra.liftNCRingHom` gives a ring homomorphism
`Γ(X,U)[x_σ] →+* A` sending `monomial d c ↦ unit c · e_d`. Its two-sided inverse is the additive map
`of j s ↦ ∑_d monomial d (coord_d s)`; both composites are checked on additive generators
(`DirectSum.addHom_ext`, `MvPolynomial.induction_on'`). Grading and unit compatibility follow from the
monomial formula. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra

variable {X : Scheme.{u}} {σ : Type u} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i) (U : X.Opens)

/-- All weights are `≥ 1`, so the exponents of a monomial of weight `m` are bounded by `m`:
`weightedMonomials w m` is finite. -/
theorem finite_weightedMonomials (hw : ∀ i, 0 < w i) (m : ℕ) : Finite (weightedMonomials w m) := by
  classical
  refine Finite.of_injective
    (fun d : weightedMonomials w m => fun i : σ => (⟨d.1 i, ?_⟩ : Fin (m + 1))) ?_
  · have h1 : d.1 i * w i ≤ Finsupp.weight w d.1 := by
      rw [Finsupp.weight_eq_sum]
      exact Finset.single_le_sum (f := fun j => d.1 j • w j) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ i)
    rw [d.2] at h1
    exact Nat.lt_succ_of_le (le_trans (Nat.le_mul_of_pos_right _ (hw i)) h1)
  · intro d d' h
    refine Subtype.ext (Finsupp.ext fun i => ?_)
    exact congrArg Fin.val (congrFun h i)

/-- A fixed `Fintype` structure on `weightedMonomials w m` (used only inside proofs/definitions of
this file, always through `letI`, so that all `Finset.univ` occurrences agree syntactically). -/
@[instance_reducible] def wmFintype (m : ℕ) : Fintype (weightedMonomials w m) :=
  @Fintype.ofFinite _ (finite_weightedMonomials w hw m)

/-- The `Γ(X, U)`-module structure on the `m`-th piece (Mathlib's instance lives on
`Γ((weightedPolynomialQCAlgebra X w hw).part m, U)`, a different spelling of the same type). -/
local instance pieceModule (m : ℕ) :
    Module Γ(X, U) ((weightedPolynomialQCAlgebra X w hw).sectionsPiece U m) :=
  inferInstanceAs (Module Γ(X, U) Γ((weightedPolynomialQCAlgebra X w hw).part m, U))

/-- The generator `e_d` of the `m`-th piece `Γ(U, O^{(weightedMonomials w m)})`. -/
def sectionsGen (m : ℕ) (d : weightedMonomials w m) :
    (weightedPolynomialQCAlgebra X w hw).sectionsPiece U m :=
  MiyaokaMori.FreeStalk.e (weightedMonomials w m) d U

/-- The `d`-th coordinate of a section of the `m`-th piece. -/
def sectionsCoord (m : ℕ) (d : weightedMonomials w m)
    (s : (weightedPolynomialQCAlgebra X w hw).sectionsPiece U m) : Γ(X, U) :=
  MiyaokaMori.DualFreeScratch.coord (X := X) (I := weightedMonomials w m) d s

theorem sectionsCoord_add (m : ℕ) (d : weightedMonomials w m)
    (s t : (weightedPolynomialQCAlgebra X w hw).sectionsPiece U m) :
    sectionsCoord w hw U m d (s + t) = sectionsCoord w hw U m d s + sectionsCoord w hw U m d t :=
  MiyaokaMori.DualFreeScratch.coord_add d s t

theorem sectionsCoord_zero (m : ℕ) (d : weightedMonomials w m) :
    sectionsCoord w hw U m d (0 : (weightedPolynomialQCAlgebra X w hw).sectionsPiece U m) = 0 := by
  have h := map_zero (MiyaokaMori.DualFreeScratch.coordLin (X := X) (I := weightedMonomials w m) d U)
  rw [MiyaokaMori.DualFreeScratch.coordLin_apply] at h
  exact h

theorem sectionsCoord_smul (m : ℕ) (d : weightedMonomials w m) (r : Γ(X, U))
    (s : (weightedPolynomialQCAlgebra X w hw).sectionsPiece U m) :
    sectionsCoord w hw U m d (r • s) = r * sectionsCoord w hw U m d s :=
  MiyaokaMori.DualFreeScratch.coord_smul d r s

open Classical in
theorem sectionsCoord_sectionsGen (m : ℕ) (d d' : weightedMonomials w m) :
    sectionsCoord w hw U m d (sectionsGen w hw U m d') = if d' = d then 1 else 0 :=
  (MiyaokaMori.DualFreeScratch.coord_e d d' U).trans (by congr)

/-- A section of the `m`-th piece is the sum of its coordinates times the generators. -/
theorem sectionsGen_decomp (m : ℕ) (s : (weightedPolynomialQCAlgebra X w hw).sectionsPiece U m) :
    letI := wmFintype w hw m
    s = ∑ d : weightedMonomials w m, sectionsCoord w hw U m d s • sectionsGen w hw U m d := by
  letI := wmFintype w hw m
  exact MiyaokaMori.DualFreeScratch.section_decomp' U s

/-- `e_d = (ιFree d).app U 1`. -/
theorem sectionsGen_eq (m : ℕ) (d : weightedMonomials w m) :
    sectionsGen w hw U m d = Scheme.Modules.Hom.app (ιM X d) U (1 : Γ(X, U)) :=
  MiyaokaMori.FreeStalk.e_eq _ _ _

/-- `e_0 = 1` in the `0`-th piece. -/
theorem sectionsGen_zero :
    sectionsGen w hw U 0 ⟨0, map_zero _⟩ = (weightedPolynomialQCAlgebra X w hw).sectionsGOne U :=
  MiyaokaMori.FreeStalk.e_eq _ _ _

/-- **Multiplication of generators**: `e_d · e_{d'} = e_{d + d'}`. -/
theorem sectionsGMul_sectionsGen (m n : ℕ) (d : weightedMonomials w m) (d' : weightedMonomials w n) :
    (weightedPolynomialQCAlgebra X w hw).sectionsGMul U (sectionsGen w hw U m d) (sectionsGen w hw U n d') =
      sectionsGen w hw U (m + n) ⟨d.1 + d'.1, by simp [map_add, d.2, d'.2]⟩ := by
  set T := weightedPolynomialQCAlgebra X w hw with hT
  have h1 : Scheme.Modules.tensorSections (T.part m) (T.part n) U
      (sectionsGen w hw U m d) (sectionsGen w hw U n d') =
      Scheme.Modules.Hom.app (MonoidalCategoryStruct.tensorHom (C := X.Modules) (ιM X d) (ιM X d')) U
        (Scheme.Modules.tensorSections (𝟙_ X.Modules) (𝟙_ X.Modules) U (1 : Γ(X, U)) (1 : Γ(X, U))) := by
    rw [sectionsGen_eq, sectionsGen_eq]
    exact (GradedQCAlgebra.tensorHom_app_tensorSections (ιM X d) (ιM X d') U _ _).symm
  show Scheme.Modules.Hom.app (mulHom X w m n) U
    (Scheme.Modules.tensorSections (T.part m) (T.part n) U (sectionsGen w hw U m d) (sectionsGen w hw U n d')) = _
  rw [h1]
  change Scheme.Modules.Hom.app
    (MonoidalCategoryStruct.tensorHom (C := X.Modules) (ιM X d) (ιM X d') ≫ mulHom X w m n) U _ = _
  rw [ιM_tensor_ιM_mulHom]
  change Scheme.Modules.Hom.app (ιM X (⟨d.1 + d'.1, _⟩ : weightedMonomials w (m + n))) U
    (Scheme.Modules.Hom.app (λ_ (𝟙_ X.Modules)).hom U
      (Scheme.Modules.tensorSections (𝟙_ X.Modules) (𝟙_ X.Modules) U (1 : Γ(X, U)) (1 : Γ(X, U)))) = _
  have h2 : Scheme.Modules.Hom.app (λ_ (𝟙_ X.Modules)).hom U
      (Scheme.Modules.tensorSections (𝟙_ X.Modules) (𝟙_ X.Modules) U (1 : Γ(X, U)) (1 : Γ(X, U))) =
      (1 : Γ(X, U)) :=
    (Scheme.Modules.leftUnitor_app_tensorSections (X := X) (𝟙_ X.Modules) U
      (1 : Γ(X, U)) (1 : Γ(X, U))).trans (one_smul Γ(X, U) (1 : Γ(X, U)))
  refine Eq.trans (congrArg (fun x => Scheme.Modules.Hom.app
    (ιM X (⟨d.1 + d'.1, _⟩ : weightedMonomials w (m + n))) U x) h2) ?_
  exact (sectionsGen_eq w hw U _ _).symm

/-- Index transport for generators inside `GradedMonoid`. -/
theorem gradedMonoid_mk_sectionsGen_congr {m m' : ℕ} (d : weightedMonomials w m)
    (d' : weightedMonomials w m') (h : d.1 = d'.1) :
    (GradedMonoid.mk m (sectionsGen w hw U m d) :
        GradedMonoid ((weightedPolynomialQCAlgebra X w hw).sectionsPiece U)) =
      GradedMonoid.mk m' (sectionsGen w hw U m' d') := by
  have hm : m = m' := d.2.symm.trans (h ▸ d'.2)
  subst hm
  rw [Subtype.ext h]

/-- Index transport for generators inside the sections ring. -/
theorem ofPiece_sectionsGen_congr {m m' : ℕ} (d : weightedMonomials w m)
    (d' : weightedMonomials w m') (h : d.1 = d'.1) :
    (weightedPolynomialQCAlgebra X w hw).ofPiece U m (sectionsGen w hw U m d) =
      (weightedPolynomialQCAlgebra X w hw).ofPiece U m' (sectionsGen w hw U m' d') :=
  DirectSum.of_eq_of_gradedMonoid_eq (gradedMonoid_mk_sectionsGen_congr w hw U d d' h)

/-- `d ↦ e_d` as a monoid homomorphism `Multiplicative (σ →₀ ℕ) →* Γ(U, S)`. -/
def sectionsGenMonoidHom : Multiplicative (σ →₀ ℕ) →* (weightedPolynomialQCAlgebra X w hw).sectionsRing U where
  toFun d := (weightedPolynomialQCAlgebra X w hw).ofPiece U (Finsupp.weight w (Multiplicative.toAdd d))
    (sectionsGen w hw U _ ⟨Multiplicative.toAdd d, rfl⟩)
  map_one' := by
    show (weightedPolynomialQCAlgebra X w hw).ofPiece U (Finsupp.weight w 0)
      (sectionsGen w hw U _ ⟨0, rfl⟩) = 1
    rw [ofPiece_sectionsGen_congr w hw U ⟨0, rfl⟩ ⟨0, map_zero _⟩ rfl, sectionsGen_zero]
    rfl
  map_mul' d d' := by
    refine Eq.trans ?_ (DirectSum.of_mul_of
      (A := (weightedPolynomialQCAlgebra X w hw).sectionsPiece U) _ _).symm
    refine DirectSum.of_eq_of_gradedMonoid_eq ?_
    change GradedMonoid.mk _ (sectionsGen w hw U _ ⟨Multiplicative.toAdd d + Multiplicative.toAdd d', rfl⟩) =
      GradedMonoid.mk _ ((weightedPolynomialQCAlgebra X w hw).sectionsGMul U
        (sectionsGen w hw U _ ⟨Multiplicative.toAdd d, rfl⟩) (sectionsGen w hw U _ ⟨Multiplicative.toAdd d', rfl⟩))
    rw [sectionsGMul_sectionsGen]
    exact gradedMonoid_mk_sectionsGen_congr w hw U _ _ rfl

/-- The ring homomorphism `Γ(X,U)[x_σ] →+* Γ(U, S)`, `monomial d c ↦ unit c · e_d`. -/
def polyToSections : MvPolynomial σ Γ(X, U) →+* (weightedPolynomialQCAlgebra X w hw).sectionsRing U :=
  AddMonoidAlgebra.liftNCRingHom ((weightedPolynomialQCAlgebra X w hw).sectionsUnitHom U)
    (sectionsGenMonoidHom w hw U) (fun _ _ => Commute.all _ _)

theorem polyToSections_monomial (d : σ →₀ ℕ) (c : Γ(X, U)) :
    polyToSections w hw U (MvPolynomial.monomial d c) =
      (weightedPolynomialQCAlgebra X w hw).sectionsUnitHom U c *
        (weightedPolynomialQCAlgebra X w hw).ofPiece U (Finsupp.weight w d) (sectionsGen w hw U _ ⟨d, rfl⟩) := by
  rw [← MvPolynomial.single_eq_monomial]
  exact AddMonoidAlgebra.liftNCRingHom_single _ _ _ _ _

theorem polyToSections_C (c : Γ(X, U)) :
    polyToSections w hw U (MvPolynomial.C c) = (weightedPolynomialQCAlgebra X w hw).sectionsUnitHom U c := by
  rw [MvPolynomial.C_apply, polyToSections_monomial,
    ofPiece_sectionsGen_congr w hw U ⟨0, rfl⟩ ⟨0, map_zero _⟩ rfl, sectionsGen_zero]
  exact mul_one _

/-- The `m`-th piece to polynomials: `s ↦ ∑_d monomial d (coord_d s)`. -/
def pieceToPoly (m : ℕ) : (weightedPolynomialQCAlgebra X w hw).sectionsPiece U m →+ MvPolynomial σ Γ(X, U) :=
  letI := wmFintype w hw m
  { toFun := fun s => ∑ d : weightedMonomials w m, MvPolynomial.monomial d.1 (sectionsCoord w hw U m d s)
    map_zero' := by simp [sectionsCoord_zero]
    map_add' := fun s t => by simp [sectionsCoord_add, Finset.sum_add_distrib] }

/-- The additive map `Γ(U, S) →+ Γ(X,U)[x_σ]` (inverse of `polyToSections`). -/
def sectionsToPoly : (weightedPolynomialQCAlgebra X w hw).sectionsRing U →+ MvPolynomial σ Γ(X, U) :=
  DirectSum.toAddMonoid (pieceToPoly w hw U)

theorem sectionsToPoly_ofPiece (m : ℕ) (s : (weightedPolynomialQCAlgebra X w hw).sectionsPiece U m) :
    sectionsToPoly w hw U ((weightedPolynomialQCAlgebra X w hw).ofPiece U m s) = pieceToPoly w hw U m s :=
  DirectSum.toAddMonoid_of _ m s

theorem polyToSections_pieceToPoly (m : ℕ) (s : (weightedPolynomialQCAlgebra X w hw).sectionsPiece U m) :
    polyToSections w hw U (pieceToPoly w hw U m s) = (weightedPolynomialQCAlgebra X w hw).ofPiece U m s := by
  letI := wmFintype w hw m
  show polyToSections w hw U (∑ d : weightedMonomials w m,
    MvPolynomial.monomial d.1 (sectionsCoord w hw U m d s)) = _
  rw [map_sum]
  have h : ∀ d : weightedMonomials w m,
      polyToSections w hw U (MvPolynomial.monomial d.1 (sectionsCoord w hw U m d s)) =
        (weightedPolynomialQCAlgebra X w hw).ofPiece U m (sectionsCoord w hw U m d s • sectionsGen w hw U m d) := by
    intro d
    rw [polyToSections_monomial, ofPiece_sectionsGen_congr w hw U ⟨d.1, rfl⟩ d rfl]
    exact GradedQCAlgebra.sectionsUnitHom_mul_ofPiece _ U _ _
  rw [Finset.sum_congr rfl fun d _ => h d]
  change ∑ d : weightedMonomials w m, DirectSum.of _ m _ = DirectSum.of _ m s
  rw [← map_sum]
  exact congrArg _ (sectionsGen_decomp w hw U m s).symm

theorem polyToSections_sectionsToPoly (a : (weightedPolynomialQCAlgebra X w hw).sectionsRing U) :
    polyToSections w hw U (sectionsToPoly w hw U a) = a := by
  have h : (polyToSections w hw U).toAddMonoidHom.comp (sectionsToPoly w hw U) = AddMonoidHom.id _ := by
    refine DirectSum.addHom_ext fun m s => ?_
    show polyToSections w hw U (sectionsToPoly w hw U ((weightedPolynomialQCAlgebra X w hw).ofPiece U m s)) =
      (weightedPolynomialQCAlgebra X w hw).ofPiece U m s
    rw [sectionsToPoly_ofPiece]
    exact polyToSections_pieceToPoly w hw U m s
  exact DFunLike.congr_fun h a

theorem sectionsToPoly_polyToSections (p : MvPolynomial σ Γ(X, U)) :
    sectionsToPoly w hw U (polyToSections w hw U p) = p := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [polyToSections_monomial, ofPiece_sectionsGen_congr w hw U ⟨d, rfl⟩ ⟨d, rfl⟩ rfl,
      GradedQCAlgebra.sectionsUnitHom_mul_ofPiece]
    refine (sectionsToPoly_ofPiece w hw U _ _).trans ?_
    letI := wmFintype w hw (Finsupp.weight w d)
    show ∑ d' : weightedMonomials w (Finsupp.weight w d),
      MvPolynomial.monomial d'.1 (sectionsCoord w hw U _ d' (c • sectionsGen w hw U _ ⟨d, rfl⟩)) = _
    rw [Finset.sum_eq_single (⟨d, rfl⟩ : weightedMonomials w (Finsupp.weight w d))]
    · rw [sectionsCoord_smul, sectionsCoord_sectionsGen, if_pos rfl, mul_one]
    · intro d' _ hd'
      rw [sectionsCoord_smul, sectionsCoord_sectionsGen, if_neg (Ne.symm hd'), mul_zero, map_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq]

/-- **The sections ring of the weighted polynomial algebra is the weighted polynomial ring**
(`Γ(X,U)[x_σ] ≃+* Γ(U, S)`, `monomial d c ↦ unit c · e_d`). -/
def polySectionsRingEquiv : MvPolynomial σ Γ(X, U) ≃+* (weightedPolynomialQCAlgebra X w hw).sectionsRing U :=
  { polyToSections w hw U with
    invFun := sectionsToPoly w hw U
    left_inv := sectionsToPoly_polyToSections w hw U
    right_inv := polyToSections_sectionsToPoly w hw U }

/-- The inverse direction `Γ(U, S) ≃+* Γ(X,U)[x_σ]`; as a function it is `sectionsToPoly`. -/
def sectionsRingEquiv : (weightedPolynomialQCAlgebra X w hw).sectionsRing U ≃+* MvPolynomial σ Γ(X, U) :=
  (polySectionsRingEquiv w hw U).symm

theorem sectionsRingEquiv_apply (a : (weightedPolynomialQCAlgebra X w hw).sectionsRing U) :
    sectionsRingEquiv w hw U a = sectionsToPoly w hw U a := rfl

theorem sectionsRingEquiv_symm_apply (p : MvPolynomial σ Γ(X, U)) :
    (sectionsRingEquiv w hw U).symm p = polyToSections w hw U p := rfl

/-- Weighted homogeneous polynomials land in the corresponding graded piece. -/
theorem polyToSections_mem_sectionsGrading {m : ℕ} {p : MvPolynomial σ Γ(X, U)}
    (hp : p.IsWeightedHomogeneous w m) :
    polyToSections w hw U p ∈ (weightedPolynomialQCAlgebra X w hw).sectionsGrading U m := by
  rw [p.as_sum, map_sum]
  refine AddSubgroup.sum_mem _ fun d hd => ?_
  have hd' : Finsupp.weight w d = m := hp (MvPolynomial.mem_support_iff.mp hd)
  rw [polyToSections_monomial, ofPiece_sectionsGen_congr w hw U ⟨d, rfl⟩ ⟨d, hd'⟩ rfl,
    GradedQCAlgebra.sectionsUnitHom_mul_ofPiece]
  exact ⟨_, rfl⟩

/-- **Grading compatibility**: `a` lies in the `m`-th piece iff its polynomial is weighted homogeneous
of weight `m`. -/
theorem mem_sectionsGrading_iff_isWeightedHomogeneous (m : ℕ)
    (a : (weightedPolynomialQCAlgebra X w hw).sectionsRing U) :
    a ∈ (weightedPolynomialQCAlgebra X w hw).sectionsGrading U m ↔
      (sectionsRingEquiv w hw U a).IsWeightedHomogeneous w m := by
  rw [sectionsRingEquiv_apply]
  constructor
  · rintro ⟨s, rfl⟩
    rw [show DirectSum.of _ m s = (weightedPolynomialQCAlgebra X w hw).ofPiece U m s from rfl,
      sectionsToPoly_ofPiece]
    letI := wmFintype w hw m
    rw [← MvPolynomial.mem_weightedHomogeneousSubmodule]
    exact Submodule.sum_mem _ fun d _ => (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2
      (MvPolynomial.isWeightedHomogeneous_monomial w d.1 _ d.2)
  · intro h
    rw [← polyToSections_sectionsToPoly w hw U a]
    exact polyToSections_mem_sectionsGrading w hw U h

/-- **Unit compatibility**: the structure map goes to the constants. -/
theorem sectionsRingEquiv_sectionsUnitHom (r : Γ(X, U)) :
    sectionsRingEquiv w hw U ((weightedPolynomialQCAlgebra X w hw).sectionsUnitHom U r) = MvPolynomial.C r := by
  rw [sectionsRingEquiv_apply, ← polyToSections_C, sectionsToPoly_polyToSections]

end AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra

end
