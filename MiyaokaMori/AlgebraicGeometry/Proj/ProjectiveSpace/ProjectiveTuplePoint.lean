import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveTupleRestriction
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveTupleFrameChange

/-! # The `R`-point of projective space defined by a tuple generating the unit ideal

A tuple `b ∈ R^{N+1}` over a `k`-algebra `R` generating the unit ideal defines the
`R`-point `[b_0 : … : b_N] : Spec R → P^N_k` (the affine, trivial-line-bundle case of
Hartshorne II Thm 7.1). We prove its naturality along ring homomorphisms and its
invariance under multiplication by a unit.

References: Hartshorne II Thm 7.1(b) (p. 150); Debarre, *Introduction to Mori theory*, 2.18.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The evaluation homomorphism `k[X_0, …, X_N] → Γ(Spec R, ⊤)`, `X_i ↦ b_i`. -/
def ProjectiveSpace.tupleEval (k : Type u) [Field k] (N : ℕ) (R : Type u) [CommRing R] (c : k →+* R)
    (b : Fin (N + 1) → R) :
    MvPolynomial (Fin (N + 1)) k →+* Γ(AlgebraicGeometry.Spec (CommRingCat.of R), ⊤) :=
  (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp
    (MvPolynomial.eval₂Hom c b)

/-- If `b` generates the unit ideal, the image of the irrelevant ideal generates the unit
ideal (the hypothesis of `Proj.fromOfGlobalSections`). -/
theorem ProjectiveSpace.tupleEval_irrelevant (k : Type u) [Field k] (N : ℕ) (R : Type u)
    [CommRing R] (c : k →+* R) (b : Fin (N + 1) → R) (hb : Ideal.span (Set.range b) = ⊤) :
    (HomogeneousIdeal.irrelevant (AlgebraicGeometry.Proj.projectiveGrading k N)).toIdeal.map
      (ProjectiveSpace.tupleEval k N R c b) = ⊤ := by
  rw [eq_top_iff]
  have hle : (Ideal.span (Set.range b)).map
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ≤
      (HomogeneousIdeal.irrelevant (AlgebraicGeometry.Proj.projectiveGrading k N)).toIdeal.map
        (ProjectiveSpace.tupleEval k N R c b) := by
    rw [Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hX : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈
        (HomogeneousIdeal.irrelevant (AlgebraicGeometry.Proj.projectiveGrading k N)).toIdeal :=
      HomogeneousIdeal.mem_irrelevant_of_mem (AlgebraicGeometry.Proj.projectiveGrading k N) Nat.zero_lt_one
        (MvPolynomial.isHomogeneous_X k i)
    have h := Ideal.mem_map_of_mem (ProjectiveSpace.tupleEval k N R c b) hX
    simpa [ProjectiveSpace.tupleEval] using h
  rw [hb, Ideal.map_top] at hle
  exact hle

/-- The `R`-point `[b_0 : … : b_N] : Spec R → P^N_k` of a tuple `b` generating the unit ideal. -/
def ProjectiveSpace.tuplePoint (k : Type u) [Field k] (N : ℕ) (R : Type u) [CommRing R] (c : k →+* R)
    (b : Fin (N + 1) → R) (hb : Ideal.span (Set.range b) = ⊤) :
    AlgebraicGeometry.Spec (CommRingCat.of R) ⟶ ProjectiveSpace N k :=
  AlgebraicGeometry.Proj.fromOfGlobalSections (AlgebraicGeometry.Proj.projectiveGrading k N)
    (ProjectiveSpace.tupleEval k N R c b) (ProjectiveSpace.tupleEval_irrelevant k N R c b hb)

/-- The `R`-point depends only on the evaluation homomorphism: two tuples with equal
evaluation homomorphisms give equal `R`-points (used to eliminate dependent proof terms). -/
theorem ProjectiveSpace.tuplePoint_congr (k : Type u) [Field k] (N : ℕ) (R : Type u) [CommRing R]
    (c : k →+* R) (b b' : Fin (N + 1) → R) (hb : Ideal.span (Set.range b) = ⊤)
    (hb' : Ideal.span (Set.range b') = ⊤) (h : b = b') :
    ProjectiveSpace.tuplePoint k N R c b hb = ProjectiveSpace.tuplePoint k N R c b' hb' := by
  subst h; rfl

/-- `Proj.fromOfGlobalSections` depends only on the ring homomorphism (proof irrelevance). -/
theorem ProjectiveSpace.fromOfGlobalSections_congr {k : Type u} [Field k] {N : ℕ}
    {T : AlgebraicGeometry.Scheme.{u}}
    {f f' : MvPolynomial (Fin (N + 1)) k →+* Γ(T, ⊤)} (h : f = f')
    (hf : (HomogeneousIdeal.irrelevant (AlgebraicGeometry.Proj.projectiveGrading k N)).toIdeal.map f = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant (AlgebraicGeometry.Proj.projectiveGrading k N)).toIdeal.map f' = ⊤) :
    AlgebraicGeometry.Proj.fromOfGlobalSections (AlgebraicGeometry.Proj.projectiveGrading k N) f hf =
      AlgebraicGeometry.Proj.fromOfGlobalSections (AlgebraicGeometry.Proj.projectiveGrading k N) f' hf' := by
  subst h; rfl

/-- Naturality: pulling back along a `k`-algebra homomorphism `g : R → R'` turns `[b]`
into `[g ∘ b]`. -/
theorem ProjectiveSpace.tuplePoint_map (k : Type u) [Field k] (N : ℕ) {R R' : Type u} [CommRing R]
    [CommRing R'] (c : k →+* R) (c' : k →+* R') (g : R →+* R')
    (hg : g.comp c = c')
    (b : Fin (N + 1) → R) (hb : Ideal.span (Set.range b) = ⊤)
    (hb' : Ideal.span (Set.range (fun i => g (b i))) = ⊤) :
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom g) ≫ ProjectiveSpace.tuplePoint k N R c b hb =
      ProjectiveSpace.tuplePoint k N R' c' (fun i => g (b i)) hb' := by
  have hnat := AlgebraicGeometry.Proj.ProjectiveTupleRestriction.fromOfGlobalSections_naturality
    (AlgebraicGeometry.Proj.projectiveGrading k N) (AlgebraicGeometry.Spec.map (CommRingCat.ofHom g))
    (ProjectiveSpace.tupleEval k N R c b) (ProjectiveSpace.tupleEval_irrelevant k N R c b hb)
  refine hnat.trans ?_
  refine ProjectiveSpace.fromOfGlobalSections_congr ?_ _
    (ProjectiveSpace.tupleEval_irrelevant k N R' c' (fun i => g (b i)) hb')
  have nat : ∀ x : R, (AlgebraicGeometry.Spec.map (CommRingCat.ofHom g)).appTop.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) =
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (g x) := fun x => by
    have h := AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)
    exact (congrArg (fun φ => φ.hom x) h).symm
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
  · simp only [ProjectiveSpace.tupleEval, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, nat]
    rw [← hg]; rfl
  · simp only [ProjectiveSpace.tupleEval, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', nat]

/-- Scalar invariance: multiplying the whole tuple by a unit does not change the `R`-point. -/
theorem ProjectiveSpace.tuplePoint_smul_unit (k : Type u) [Field k] (N : ℕ) {R : Type u} [CommRing R]
    (c : k →+* R) (u : Rˣ) (b : Fin (N + 1) → R) (hb : Ideal.span (Set.range b) = ⊤)
    (hb' : Ideal.span (Set.range (fun i => (u : R) * b i)) = ⊤) :
    ProjectiveSpace.tuplePoint k N R c (fun i => (u : R) * b i) hb' =
      ProjectiveSpace.tuplePoint k N R c b hb := by
  let e := (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have h1 : ∀ b' : Fin (N + 1) → R, ProjectiveSpace.tupleEval k N R c b' =
      MvPolynomial.eval₂Hom (e.comp c) (fun i => e (b' i)) := fun b' => by
    unfold ProjectiveSpace.tupleEval
    exact MvPolynomial.comp_eval₂Hom _ _ _
  have hp : (HomogeneousIdeal.irrelevant (AlgebraicGeometry.Proj.projectiveGrading k N)).toIdeal.map
      (MvPolynomial.eval₂Hom (e.comp c) (fun i => e (b i))) = ⊤ := by
    rw [← h1]; exact ProjectiveSpace.tupleEval_irrelevant k N R c b hb
  have key := AlgebraicGeometry.Proj.ProjectiveTupleFrameChange.fromOfGlobalSections_scale
    (AlgebraicGeometry.Spec (CommRingCat.of R)) N (e.comp c) (fun i => e (b i))
    (Units.map e.toMonoidHom u) hp
  have h2 : ProjectiveSpace.tupleEval k N R c (fun i => (u : R) * b i) =
      MvPolynomial.eval₂Hom (e.comp c)
        (fun j => ((Units.map e.toMonoidHom u : Γ(AlgebraicGeometry.Spec (CommRingCat.of R), ⊤)ˣ) :
          Γ(AlgebraicGeometry.Spec (CommRingCat.of R), ⊤)) * e (b j)) := by
    rw [h1]
    congr 1
    funext i
    simp
  exact (ProjectiveSpace.fromOfGlobalSections_congr h2
      (ProjectiveSpace.tupleEval_irrelevant k N R c _ hb') _).trans
    (key.trans (ProjectiveSpace.fromOfGlobalSections_congr (h1 b).symm hp
      (ProjectiveSpace.tupleEval_irrelevant k N R c b hb)))

end
