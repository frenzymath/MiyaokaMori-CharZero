import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAtlas
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.OfGradedQCAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.FiniteTypeOfFiniteAffineSections
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra

/-! # Graded pieces of a locally weighted polynomial algebra are of finite type

If a graded quasi-coherent algebra `S` is locally isomorphic to a weighted polynomial algebra with
positive weights on a finite index set `σ`, then every graded piece `S.part m` is a finite type
sheaf of modules.

Proof: take the weighted polynomial atlas provided by
`S.toGradedAffineAlgebra.IsLocallyWeightedPolynomial w`; on each chart the degree-`m` piece
consists of the monomials of weight `m`, and positivity plus finiteness of `σ` give finitely many
such monomials (`Finsupp.finite_of_nat_weight_eq`), so the piece is finitely generated on the chart.
The local criterion for finite type quasi-coherent modules then gives `(S.part m).IsFiniteType`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Every graded piece of a locally weighted polynomial graded quasi-coherent algebra is a
finite type module. -/
theorem locallyWeighted_part_isFiniteType {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) {σ : Type u} [Finite σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (hS : S.toGradedAffineAlgebra.IsLocallyWeightedPolynomial w) (m : ℕ) :
    (S.part m).IsFiniteType := by
  obtain ⟨atlas⟩ := hS
  letI : (S.part m).IsQuasicoherent := S.quasicoherent m
  apply AlgebraicGeometry.Scheme.Modules.isFiniteType_of_finite_affine_sections (S.part m)
  intro x
  obtain ⟨i, hxi⟩ := atlas.covers x
  let U := (atlas.chart i).toOpens
  refine ⟨U, (atlas.chart i).2, hxi, ?_⟩
  letI : Module Γ(X, U) (S.sectionsPiece U m) :=
    inferInstanceAs (Module Γ(X, U) Γ(S.part m, U))
  let P := MvPolynomial.weightedHomogeneousSubmodule Γ(X, U) w m
  let f : S.sectionsPiece U m →ₗ[Γ(X, U)] P :=
    { toFun := fun a =>
        ⟨atlas.equiv i (S.ofPiece U m a),
          (atlas.equiv_grading i m (S.ofPiece U m a)).mp ⟨a, rfl⟩⟩
      map_add' := fun a b => by
        apply Subtype.ext
        change atlas.equiv i (S.ofPiece U m (a + b)) =
          atlas.equiv i (S.ofPiece U m a) + atlas.equiv i (S.ofPiece U m b)
        have hadd : S.ofPiece U m (a + b) =
            S.ofPiece U m a + S.ofPiece U m b :=
          map_add (DirectSum.of (S.sectionsPiece U) m) a b
        rw [hadd]
        exact map_add (atlas.equiv i) (S.ofPiece U m a) (S.ofPiece U m b)
      map_smul' := fun r a => by
        apply Subtype.ext
        change atlas.equiv i (S.ofPiece U m (r • a)) =
          r • atlas.equiv i (S.ofPiece U m a)
        have hmul : S.ofPiece U m (r • a) =
            S.sectionsUnitHom U r * S.ofPiece U m a :=
          (S.sectionsPieceEquivGrading_smul U m r a).symm
        have heMul : atlas.equiv i (S.sectionsUnitHom U r * S.ofPiece U m a) =
            atlas.equiv i (S.sectionsUnitHom U r) * atlas.equiv i (S.ofPiece U m a) :=
          map_mul (atlas.equiv i) (S.sectionsUnitHom U r) (S.ofPiece U m a)
        have heUnit : atlas.equiv i (S.sectionsUnitHom U r) = MvPolynomial.C r :=
          atlas.equiv_unit i r
        rw [hmul, heMul, heUnit]
        exact (Algebra.smul_def r _).symm }
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have hv := congrArg Subtype.val hab
      exact S.ofPiece_injective U m ((atlas.equiv i).injective hv)
    · intro p
      let z : S.sectionsGrading U m :=
        ⟨(atlas.equiv i).symm p.1, (atlas.equiv_grading i m _).mpr (by
          rw [RingEquiv.apply_symm_apply]
          exact p.2)⟩
      refine ⟨(S.sectionsPieceEquivGrading U m).symm z, ?_⟩
      apply Subtype.ext
      change atlas.equiv i
        (S.ofPiece U m ((S.sectionsPieceEquivGrading U m).symm z)) = p.1
      have hz : S.ofPiece U m ((S.sectionsPieceEquivGrading U m).symm z) = z.1 :=
        congrArg Subtype.val ((S.sectionsPieceEquivGrading U m).apply_symm_apply z)
      rw [hz]
      exact (atlas.equiv i).apply_symm_apply p.1
  letI : Module.Finite Γ(X, U) P :=
    (Module.Finite.iff_fg).2
      (MvPolynomial.weightedHomogeneousSubmodule_fg Γ(X, U) w
        (fun i => Nat.ne_of_gt (hw i)) m)
  exact Module.Finite.equiv (LinearEquiv.ofBijective f hf).symm

end
