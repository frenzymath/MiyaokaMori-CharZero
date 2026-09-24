import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SchemeOverResidue

/-!
# Common invertible changes of homogeneous coordinates

The polynomial coordinates of Theorem 4.2 of the paper are sections of
one coefficient line bundle. A change of its local frame multiplies every
coordinate by the same unit. These helpers support the gluing of the
projectivized tuple; they do not introduce another tuple or gluing object.

The central algebra calculation takes place in the actual homogeneous
localization. Both numerator and denominator have the same degree, so their
common power of the unit cancels. No reducedness or domain hypothesis is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Proj.ProjectiveTupleFrameChange

universe u v w

section HomogeneousEvaluation

variable {k : Type u} {R : Type v} {ι : Type w} [CommSemiring k] [CommSemiring R]

/-- Evaluating a degree-`d` homogeneous polynomial on a scaled tuple multiplies
its value by the `d`th power of the scale. -/
theorem eval₂Hom_scale (c : k →+* R) (p : ι → R) (a : R)
    {F : MvPolynomial ι k} {d : ℕ} (hF : F.IsHomogeneous d) :
    MvPolynomial.eval₂Hom c (fun i ↦ a * p i) F =
      a ^ d * MvPolynomial.eval₂Hom c p F := by
  classical
  induction hF using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add F G hF hG ihF ihG => simp only [map_add, ihF, ihG, mul_add]
  | monomial m b hm =>
    have hdegree : (∑ i ∈ m.support, m i) = d := by
      simpa [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul] using hm
    simp only [MvPolynomial.eval₂Hom_monomial, Finsupp.prod, mul_pow,
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdegree]
    ac_rfl

end HomogeneousEvaluation

section GradedRing

variable {A : Type u} {R : Type v} {σ : Type w} [CommRing A] [CommRing R]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

private theorem irrelevant_map_le_of_scale (f g : A →+* R) (a : R)
    (hscale : ∀ (d : ℕ) (x : A), x ∈ 𝒜 d → g x = a ^ d * f x) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g ≤
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f := by
  rw [Ideal.map_le_iff_le_comap, HomogeneousIdeal.toIdeal_irrelevant_le]
  intro d hd x hx
  change g x ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f
  rw [hscale d x hx]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem f
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd hx))

/-- Scaling each homogeneous degree by the corresponding power of one unit
preserves the image of the irrelevant ideal. -/
theorem irrelevant_map_eq_of_unit_scale (f g : A →+* R) (a : Rˣ)
    (hscale : ∀ (d : ℕ) (x : A), x ∈ 𝒜 d → g x = (a : R) ^ d * f x) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g =
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f := by
  apply le_antisymm (irrelevant_map_le_of_scale 𝒜 f g a hscale)
  apply irrelevant_map_le_of_scale 𝒜 g f (↑(a⁻¹) : R)
  intro d x hx
  rw [hscale d x hx, ← mul_assoc, ← mul_pow]
  simp

/-- Homogeneous-localization evaluation is unchanged by a common unit scaling.

The localization maps are actual ring homomorphisms. Their restrictions agree
on every equal-degree fraction, not merely at residue-field points.
-/
theorem homogeneousLocalization_lift_eq (M : Submonoid A) (f g : A →+* R) (a : Rˣ)
    (hscale : ∀ (d : ℕ) (x : A), x ∈ 𝒜 d → g x = (a : R) ^ d * f x)
    (hf : ∀ x : M, IsUnit (f x)) (hg : ∀ x : M, IsUnit (g x)) :
    (IsLocalization.lift (S := Localization M) hg).comp
        (algebraMap (HomogeneousLocalization 𝒜 M) (Localization M)) =
      (IsLocalization.lift (S := Localization M) hf).comp
        (algebraMap (HomogeneousLocalization 𝒜 M) (Localization M)) := by
  ext z
  obtain ⟨z, rfl⟩ := HomogeneousLocalization.mk_surjective z
  simp only [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk']
  apply (IsLocalization.lift_mk'_spec (S := Localization M) hg _ _ _).mpr
  rw [hscale z.deg z.num z.num.property, hscale z.deg z.den z.den.property, mul_assoc]
  apply congrArg (fun x : R ↦ (a : R) ^ z.deg * x)
  exact (IsLocalization.lift_mk'_spec (S := Localization M) hf
    (z.num : A) _ ⟨z.den, z.den_mem⟩).mp rfl

/-- On a homogeneous affine chart, invertibility for the scaled map follows
from invertibility for the original map. The resulting chart ring maps agree. -/
theorem away_lift_eq_unit_scale (f g : A →+* R) (a : Rˣ)
    (hscale : ∀ (d : ℕ) (x : A), x ∈ 𝒜 d → g x = (a : R) ^ d * f x)
    {t : A} {d : ℕ} (ht : t ∈ 𝒜 d) (hf : IsUnit (f t)) :
    (IsLocalization.Away.lift (S := Localization.Away t) t
      (show IsUnit (g t) by rw [hscale d t ht]; exact (a.isUnit.pow d).mul hf)).comp
        (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t)) =
      (IsLocalization.Away.lift (S := Localization.Away t) t hf).comp
        (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t)) := by
  exact homogeneousLocalization_lift_eq 𝒜 (Submonoid.powers t) f g a hscale _ _

/-- The same fraction calculation applies to any actual localization extensions
of the two graded evaluations. -/
theorem homogeneousLocalization_eq_of_extensions (M : Submonoid A)
    (f g : A →+* R) (a : Rˣ)
    (hscale : ∀ (d : ℕ) (x : A), x ∈ 𝒜 d → g x = (a : R) ^ d * f x)
    (hf : ∀ x : M, IsUnit (f x)) (hg : ∀ x : M, IsUnit (g x))
    (F G : Localization M →+* R)
    (hF : ∀ x, F (algebraMap A (Localization M) x) = f x)
    (hG : ∀ x, G (algebraMap A (Localization M) x) = g x) :
    G.comp (algebraMap (HomogeneousLocalization 𝒜 M) (Localization M)) =
      F.comp (algebraMap (HomogeneousLocalization 𝒜 M) (Localization M)) := by
  rw [← IsLocalization.lift_unique hf hF, ← IsLocalization.lift_unique hg hG]
  exact homogeneousLocalization_lift_eq 𝒜 M f g a hscale hf hg

end GradedRing

section ProjectiveTuple

variable {k : Type u} [Field k] {R : Type v} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The scaled tuple satisfies the same irrelevant-ideal condition, derived
from the condition on the original tuple. -/
theorem irrelevant_map_eq_top_scale (n : ℕ) (c : k →+* R)
    (p : Fin (n + 1) → R) (a : Rˣ)
    (hp : (HomogeneousIdeal.irrelevant (projectiveGrading k n)).toIdeal.map
      (MvPolynomial.eval₂Hom c p) = ⊤) :
    (HomogeneousIdeal.irrelevant (projectiveGrading k n)).toIdeal.map
      (MvPolynomial.eval₂Hom c (fun i ↦ (a : R) * p i)) = ⊤ := by
  rw [irrelevant_map_eq_of_unit_scale (projectiveGrading k n)
    (MvPolynomial.eval₂Hom c p) (MvPolynomial.eval₂Hom c (fun i ↦ (a : R) * p i)) a
      (fun _ _ hF ↦ eval₂Hom_scale c p a hF)]
  exact hp

/-- Equal actual ring maps on the affine projective coordinate chart. -/
theorem coordinateChart_lift_eq_scale (n : ℕ) (c : k →+* R)
    (p : Fin (n + 1) → R) (a : Rˣ) (i : Fin (n + 1)) (hi : IsUnit (p i)) :
    (IsLocalization.Away.lift (S := Localization.Away (MvPolynomial.X (R := k) i))
      (MvPolynomial.X i)
      (show IsUnit (MvPolynomial.eval₂Hom c (fun j ↦ (a : R) * p j)
        (MvPolynomial.X i)) by simpa using a.isUnit.mul hi)).comp
        (algebraMap
          (HomogeneousLocalization.Away (projectiveGrading k n) (MvPolynomial.X i))
          (Localization.Away (MvPolynomial.X i))) =
      (IsLocalization.Away.lift (S := Localization.Away (MvPolynomial.X (R := k) i))
        (MvPolynomial.X i)
        (show IsUnit (MvPolynomial.eval₂Hom c p (MvPolynomial.X i)) by simpa using hi)).comp
          (algebraMap
            (HomogeneousLocalization.Away (projectiveGrading k n) (MvPolynomial.X i))
            (Localization.Away (MvPolynomial.X i))) := by
  exact away_lift_eq_unit_scale (projectiveGrading k n) (MvPolynomial.eval₂Hom c p)
    (MvPolynomial.eval₂Hom c (fun j ↦ (a : R) * p j)) a
    (fun _ _ hF ↦ eval₂Hom_scale c p a hF) (MvPolynomial.isHomogeneous_X k i)
    (by simpa using hi)

/-- The actual basic open of each coordinate is unchanged by a unit. -/
theorem basicOpen_unit_mul (T : Scheme.{u}) (a : Γ(T, ⊤)ˣ) (p : Γ(T, ⊤)) :
    T.basicOpen ((a : Γ(T, ⊤)) * p) = T.basicOpen p := by
  rw [Scheme.basicOpen_mul, T.basicOpen_of_isUnit a.isUnit]
  simp

end ProjectiveTuple

section SchemeLocalization

variable {A : Type u} [CommRing A] {T : Scheme.{u}}

/-- The actual source-to-localization leg used in Mathlib's Proj chart map. -/
private def toAffineBasicOpen (T : Scheme.{u}) (x : Γ(T, ⊤)) :
    (T.basicOpen x).toScheme ⟶ Spec (.of (Localization.Away x)) :=
  (T.isoOfEq (T.toSpecΓ_preimage_basicOpen x)).inv ≫
    T.toSpecΓ ∣_ PrimeSpectrum.basicOpen x ≫ (basicOpenIsoSpecAway x).hom

private theorem toAffineBasicOpen_comp (T : Scheme.{u}) (x : Γ(T, ⊤)) :
    toAffineBasicOpen T x ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (Localization.Away x))) =
        (T.basicOpen x).ι ≫ T.toSpecΓ := by
  simp only [toAffineBasicOpen, Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
  rw [morphismRestrict_ι T.toSpecΓ (PrimeSpectrum.basicOpen x)]
  exact Scheme.isoOfEq_inv_ι_assoc T (T.toSpecΓ_preimage_basicOpen x) T.toSpecΓ

private theorem toAffineBasicOpen_change (T : Scheme.{u}) {x y : Γ(T, ⊤)}
    (hxy : T.basicOpen x = T.basicOpen y)
    (l : Localization.Away y →+* Localization.Away x)
    (hl : l.comp (algebraMap Γ(T, ⊤) (Localization.Away y)) =
      algebraMap Γ(T, ⊤) (Localization.Away x)) :
    toAffineBasicOpen T x ≫ Spec.map (CommRingCat.ofHom l) =
      (T.isoOfEq hxy).hom ≫ toAffineBasicOpen T y := by
  apply (cancel_mono
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (Localization.Away y))))).mp
  simp only [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hl,
    toAffineBasicOpen_comp, Scheme.isoOfEq_hom_ι_assoc]

/-- The polynomial evaluation extended to the usual localization on a chart. -/
private def evaluationLocalization (f : A →+* Γ(T, ⊤)) (t : A) :
    Localization.Away t →+* Localization.Away (f t) :=
  IsLocalization.map (M := Submonoid.powers t) (T := Submonoid.powers (f t))
    (Localization.Away (f t)) f (by
      intro x hx
      change f x ∈ Submonoid.powers (f t)
      obtain ⟨m, hm⟩ := hx
      rw [← hm, map_pow]
      exact ⟨m, rfl⟩)

private theorem evaluationLocalization_eq (f : A →+* Γ(T, ⊤)) (t x : A) :
    evaluationLocalization f t (algebraMap A (Localization.Away t) x) =
      algebraMap Γ(T, ⊤) (Localization.Away (f t)) (f x) := by
  exact IsLocalization.map_eq _ _

variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The ring maps exposed here are precisely the ones in Mathlib's local Proj
construction, including the actual source localization leg. -/
private theorem toBasicOpenOfGlobalSections_eq (f : A →+* Γ(T, ⊤))
    {t : A} {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) :
    Proj.toBasicOpenOfGlobalSections 𝒜 f rfl hd ht =
      toAffineBasicOpen T (f t) ≫
        Spec.map (CommRingCat.ofHom ((evaluationLocalization f t).comp
          (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t)))) ≫
        (Proj.basicOpenIsoSpec 𝒜 t ht hd).inv := by
  simp only [Proj.toBasicOpenOfGlobalSections, toAffineBasicOpen,
    evaluationLocalization, Category.assoc]

/-- The common unit scale preserves the source basic open of every homogeneous element. -/
theorem basicOpen_homogeneous_unit_scale (f g : A →+* Γ(T, ⊤)) (a : Γ(T, ⊤)ˣ)
    (hscale : ∀ (d : ℕ) (x : A), x ∈ 𝒜 d → g x = (a : Γ(T, ⊤)) ^ d * f x)
    {t : A} {d : ℕ} (ht : t ∈ 𝒜 d) :
    T.basicOpen (g t) = T.basicOpen (f t) := by
  rw [hscale d t ht]
  simpa only [Units.val_pow_eq_pow_val] using basicOpen_unit_mul T (a ^ d) (f t)

/-- Mathlib's actual local Proj maps agree after identifying their equal source
opens. The proof compares their localization ring maps, including sheaf maps. -/
theorem toBasicOpenOfGlobalSections_unit_scale (f g : A →+* Γ(T, ⊤))
    (a : Γ(T, ⊤)ˣ)
    (hscale : ∀ (d : ℕ) (x : A), x ∈ 𝒜 d → g x = (a : Γ(T, ⊤)) ^ d * f x)
    {t : A} {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) :
    (T.isoOfEq (basicOpen_homogeneous_unit_scale 𝒜 f g a hscale ht).symm).hom ≫
        Proj.toBasicOpenOfGlobalSections 𝒜 g rfl hd ht =
      Proj.toBasicOpenOfGlobalSections 𝒜 f rfl hd ht := by
  let af : Γ(T, ⊤) →+* Localization.Away (f t) := algebraMap _ _
  let F := evaluationLocalization f t
  let G := evaluationLocalization g t
  have hgUnit : IsUnit (af (g t)) := by
    rw [hscale d t ht, map_mul, map_pow]
    exact ((a.isUnit.map af).pow d).mul (IsLocalization.Away.algebraMap_isUnit (f t))
  let l : Localization.Away (g t) →+* Localization.Away (f t) :=
    IsLocalization.Away.lift (g t) hgUnit
  have hl : l.comp (algebraMap Γ(T, ⊤) (Localization.Away (g t))) = af :=
    IsLocalization.Away.lift_comp (g t) hgUnit
  have hF : ∀ x, F (algebraMap A (Localization.Away t) x) = (af.comp f) x :=
    fun x ↦ evaluationLocalization_eq f t x
  have hG : ∀ x, (l.comp G) (algebraMap A (Localization.Away t) x) = (af.comp g) x := by
    intro x
    change l (evaluationLocalization g t (algebraMap A (Localization.Away t) x)) = af (g x)
    rw [evaluationLocalization_eq]
    exact DFunLike.congr_fun hl (g x)
  have hloc : (l.comp G).comp
        (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t)) =
      F.comp (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t)) := by
    refine homogeneousLocalization_eq_of_extensions 𝒜 (Submonoid.powers t)
      (af.comp f) (af.comp g) (Units.map af.toMonoidHom a) ?_ ?_ ?_ F (l.comp G) hF hG
    · intro m x hx
      change af (g x) = af (a : Γ(T, ⊤)) ^ m * af (f x)
      rw [hscale m x hx, map_mul, map_pow]
    · intro x
      rw [← hF x]
      exact (IsLocalization.map_units (Localization.Away t) x).map F
    · intro x
      rw [← hG x]
      exact (IsLocalization.map_units (Localization.Away t) x).map (l.comp G)
  let hxy := (basicOpen_homogeneous_unit_scale 𝒜 f g a hscale ht).symm
  have hsource := toAffineBasicOpen_change T hxy l hl
  change (T.isoOfEq hxy).hom ≫ Proj.toBasicOpenOfGlobalSections 𝒜 g rfl hd ht = _
  rw [toBasicOpenOfGlobalSections_eq, toBasicOpenOfGlobalSections_eq,
    ← Category.assoc (T.isoOfEq hxy).hom (toAffineBasicOpen T (g t)), ← hsource]
  have hspec :
      Spec.map (CommRingCat.ofHom l) ≫
          Spec.map (CommRingCat.ofHom (G.comp
            (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t)))) =
        Spec.map (CommRingCat.ofHom (F.comp
          (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t)))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hloc]
  simpa only [Category.assoc] using
    congrArg (fun m ↦ toAffineBasicOpen T (f t) ≫ m ≫
      (Proj.basicOpenIsoSpec 𝒜 t ht hd).inv) hspec

private theorem basicOpen_ι_fromOfGlobalSections (f : A →+* Γ(T, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    {t : A} {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) :
    (T.basicOpen (f t)).ι ≫ Proj.fromOfGlobalSections 𝒜 f hf =
      Proj.toBasicOpenOfGlobalSections 𝒜 f rfl hd ht ≫ (Proj.basicOpen 𝒜 t).ι := by
  rw [← Proj.fromOfGlobalSections_resLE 𝒜 f hf hd ht]
  exact (Scheme.Hom.resLE_comp_ι (Proj.fromOfGlobalSections 𝒜 f hf)
    (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf hd ht).ge).symm

/-- A homogeneous unit change of evaluation leaves Mathlib's canonical global
Proj morphism unchanged. The equality is one of scheme morphisms. -/
theorem fromOfGlobalSections_unit_scale (f g : A →+* Γ(T, ⊤)) (a : Γ(T, ⊤)ˣ)
    (hscale : ∀ (d : ℕ) (x : A), x ∈ 𝒜 d → g x = (a : Γ(T, ⊤)) ^ d * f x)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    Proj.fromOfGlobalSections 𝒜 g
        (by rw [irrelevant_map_eq_of_unit_scale 𝒜 f g a hscale]; exact hf) =
      Proj.fromOfGlobalSections 𝒜 f hf := by
  let hg : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g = ⊤ := by
    rw [irrelevant_map_eq_of_unit_scale 𝒜 f g a hscale]
    exact hf
  change Proj.fromOfGlobalSections 𝒜 g hg = Proj.fromOfGlobalSections 𝒜 f hf
  refine (Proj.openCoverOfMapIrrelevantEqTop 𝒜 f hf).hom_ext _ _ fun ri ↦ ?_
  change (T.basicOpen (f ri.2.1)).ι ≫ Proj.fromOfGlobalSections 𝒜 g hg =
    (T.basicOpen (f ri.2.1)).ι ≫ Proj.fromOfGlobalSections 𝒜 f hf
  let hxy := (basicOpen_homogeneous_unit_scale 𝒜 f g a hscale ri.2.2.2).symm
  calc
    _ = (T.isoOfEq hxy).hom ≫ (T.basicOpen (g ri.2.1)).ι ≫
        Proj.fromOfGlobalSections 𝒜 g hg := by
      simp only [Scheme.isoOfEq_hom_ι_assoc]
    _ = (T.isoOfEq hxy).hom ≫
        Proj.toBasicOpenOfGlobalSections 𝒜 g rfl ri.2.2.1 ri.2.2.2 ≫
          (Proj.basicOpen 𝒜 ri.2.1).ι := by
      rw [basicOpen_ι_fromOfGlobalSections]
    _ = Proj.toBasicOpenOfGlobalSections 𝒜 f rfl ri.2.2.1 ri.2.2.2 ≫
        (Proj.basicOpen 𝒜 ri.2.1).ι := by
      rw [← Category.assoc,
        toBasicOpenOfGlobalSections_unit_scale 𝒜 f g a hscale ri.2.2.1 ri.2.2.2]
    _ = _ := (basicOpen_ι_fromOfGlobalSections 𝒜 f hf ri.2.2.1 ri.2.2.2).symm

end SchemeLocalization

section SchemeChart

variable {k : Type u} [Field k]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Common multiplication of a projective tuple by one invertible global
section does not change its canonical morphism to projective space. -/
theorem fromOfGlobalSections_scale (T : Scheme.{u}) (n : ℕ)
    (c : k →+* Γ(T, ⊤)) (p : Fin (n + 1) → Γ(T, ⊤)) (a : Γ(T, ⊤)ˣ)
    (hp : (HomogeneousIdeal.irrelevant (projectiveGrading k n)).toIdeal.map
      (MvPolynomial.eval₂Hom c p) = ⊤) :
    Proj.fromOfGlobalSections (projectiveGrading k n)
        (MvPolynomial.eval₂Hom c (fun j ↦ (a : Γ(T, ⊤)) * p j))
        (irrelevant_map_eq_top_scale n c p a hp) =
      Proj.fromOfGlobalSections (projectiveGrading k n) (MvPolynomial.eval₂Hom c p) hp := by
  exact fromOfGlobalSections_unit_scale (projectiveGrading k n)
    (MvPolynomial.eval₂Hom c p)
    (MvPolynomial.eval₂Hom c (fun j ↦ (a : Γ(T, ⊤)) * p j)) a
    (fun _ _ hF ↦ eval₂Hom_scale c p a hF) hp

/-- The two canonical Proj morphisms have the same inverse image of every
standard coordinate chart. Their local ring-map equality is recorded below. -/
theorem fromOfGlobalSections_preimage_basicOpen_X_scale (T : Scheme.{u}) (n : ℕ)
    (c : k →+* Γ(T, ⊤)) (p : Fin (n + 1) → Γ(T, ⊤)) (a : Γ(T, ⊤)ˣ)
    (hp : (HomogeneousIdeal.irrelevant (projectiveGrading k n)).toIdeal.map
      (MvPolynomial.eval₂Hom c p) = ⊤) (i : Fin (n + 1)) :
    Proj.fromOfGlobalSections (projectiveGrading k n)
        (MvPolynomial.eval₂Hom c (fun j ↦ (a : Γ(T, ⊤)) * p j))
        (irrelevant_map_eq_top_scale n c p a hp) ⁻¹ᵁ
      Proj.basicOpen (projectiveGrading k n) (MvPolynomial.X i) =
    Proj.fromOfGlobalSections (projectiveGrading k n) (MvPolynomial.eval₂Hom c p) hp ⁻¹ᵁ
      Proj.basicOpen (projectiveGrading k n) (MvPolynomial.X i) := by
  rw [Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.zero_lt_one
      (MvPolynomial.isHomogeneous_X k i),
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.zero_lt_one
      (MvPolynomial.isHomogeneous_X k i)]
  simpa only [MvPolynomial.eval₂Hom_X'] using basicOpen_unit_mul T a (p i)

/-- The morphisms into the actual affine chart of projective space agree under
a common unit change of coordinates. This equality retains the structure sheaf.

The chart is presented by its canonical homogeneous-localization ring. The
global canonical morphism comparison is `fromOfGlobalSections_scale`.
-/
theorem coordinateChart_schemeMap_eq_scale (T : Scheme.{u}) (n : ℕ)
    (c : k →+* Γ(T, ⊤)) (p : Fin (n + 1) → Γ(T, ⊤)) (a : Γ(T, ⊤)ˣ)
    (i : Fin (n + 1)) (hi : IsUnit (p i)) :
    T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      ((IsLocalization.Away.lift (S := Localization.Away (MvPolynomial.X (R := k) i))
        (MvPolynomial.X i)
        (show IsUnit (MvPolynomial.eval₂Hom c (fun j ↦ (a : Γ(T, ⊤)) * p j)
          (MvPolynomial.X i)) by simpa using a.isUnit.mul hi)).comp
            (algebraMap
              (HomogeneousLocalization.Away (projectiveGrading k n) (MvPolynomial.X i))
              (Localization.Away (MvPolynomial.X i))))) ≫
        (Proj.basicOpenIsoSpec (projectiveGrading k n) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one).inv =
      T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
        ((IsLocalization.Away.lift (S := Localization.Away (MvPolynomial.X (R := k) i))
          (MvPolynomial.X i)
          (show IsUnit (MvPolynomial.eval₂Hom c p (MvPolynomial.X i)) by
            simpa using hi)).comp
              (algebraMap
                (HomogeneousLocalization.Away (projectiveGrading k n) (MvPolynomial.X i))
                (Localization.Away (MvPolynomial.X i))))) ≫
          (Proj.basicOpenIsoSpec (projectiveGrading k n) (MvPolynomial.X i)
            (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one).inv := by
  rw [coordinateChart_lift_eq_scale n c p a i hi]

end SchemeChart

end AlgebraicGeometry.Proj.ProjectiveTupleFrameChange
