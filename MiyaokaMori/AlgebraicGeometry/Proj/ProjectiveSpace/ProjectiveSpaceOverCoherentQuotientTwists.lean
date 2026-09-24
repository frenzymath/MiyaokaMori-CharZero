import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOverTwist
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleFiniteTypeQuotient
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleZpowAddIso

/-! # Coherent sheaves on projective space over a ring are quotients of sums of twists

Stacks 01YS(1) over an arbitrary commutative ring `R`: a coherent module `G` on `P^N_R`
(`ProjectiveSpaceOver N R`) is a quotient of a finite direct sum of
Serre twists: there are `r`, `d : Fin r → ℤ` and an epimorphism `⨁_j O(d_j) ↠ G`.

The version over a field is `exists_epi_biproduct_twists_projectiveSpace`, a specialisation of this
one. Route (Stacks 01YS(1), 01Q3):
`O(1)` is ample on `P^N_R` (`projectiveSpaceOverTwist_one_isAmple`, Stacks 01MW(5)), `G` coherent means
quasi-coherent of finite type, so Stacks 01Q3 (1)⇒(8) (`IsAmple.exists_epi_biproduct_zpow_neg`) gives `n > 0`, `r` and an epimorphism `⨁_{j<r} O(1)^{⊗-n} ↠ G`.
Finally `O(1)^{⊗ -n} ≅ O(-n)`: `O(1)^∨ ≅ O(-1)` (`projectiveSpaceOverTwist_dual`, from
`O(a) ⊗ O(b) ≅ O(a+b)` and the tensor-inverse characterisation of the dual) and induction on `n`
(`projectiveSpaceOverTwist_tensor`); transport the epimorphism along `biproduct.mapIso`.

Source: Stacks 01YS (coherent-lemma-coherent-projective) (1); Stacks 01Q3; Hartshorne II.5.17 / II.5.18.
Edge cases: `R = 0` (`P^N_R = ∅`, every module is `0`, `r = 0` works — the proof gives some `r`);
`G = 0` (any `r`); `N = 0` (`P^0_R ≅ Spec R`, `O(d) ≅ O`: the statement is "finite `R`-modules are
finitely presented-quotients of free modules").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `O(a)^∨ ≅ O(-a)` on `P^N_R` (Stacks 01MT: `O(-a) ⊗ O(a) ≅ O(0) ≅ O`, and a tensor inverse of a line
bundle is its dual). Proof copied from the field version `projectiveSpaceTwist_dual`. -/
theorem projectiveSpaceOverTwist_dual (R : Type u) [CommRing R] (N : ℕ) (a : ℤ) :
    Nonempty (AlgebraicGeometry.Scheme.Modules.dual (projectiveSpaceOverTwist R N a) ≅
      projectiveSpaceOverTwist R N (-a)) := by
  let A : (ProjectiveSpaceOver N R).Modules := projectiveSpaceOverTwist R N 0
  let FA := CategoryTheory.MonoidalCategory.tensorRight A
  let _ : FA.IsEquivalence :=
    AlgebraicGeometry.Scheme.Modules.isEquivalence_tensorRight_of_isLineBundle A
  have eAA₀ : A ⊗ A ≅ A := by
    let e : AlgebraicGeometry.Scheme.Modules.tensor
        (projectiveSpaceOverTwist R N 0) (projectiveSpaceOverTwist R N 0) ≅
        projectiveSpaceOverTwist R N (0 + 0) := Classical.choice (projectiveSpaceOverTwist_tensor R N 0 0)
    simpa [A] using
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A A).symm ≪≫ e
  have eAunit : A ≅ 𝟙_ (ProjectiveSpaceOver N R).Modules := by
    let eF : FA.obj A ≅ FA.obj (𝟙_ (ProjectiveSpaceOver N R).Modules) :=
      eAA₀ ≪≫ (CategoryTheory.MonoidalCategory.leftUnitor A).symm
    exact (FA.asEquivalence.fullyFaithfulFunctor).preimageIso eF
  have eML₀ :
      (projectiveSpaceOverTwist R N (-a) : (ProjectiveSpaceOver N R).Modules) ⊗
        projectiveSpaceOverTwist R N a ≅ A := by
    exact (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
      (projectiveSpaceOverTwist R N (-a)) (projectiveSpaceOverTwist R N a)).symm ≪≫
      (Classical.choice (projectiveSpaceOverTwist_tensor R N (-a) a)) ≪≫
      CategoryTheory.eqToIso (by
        rw [show (-a) + a = 0 by ring])
  let L : (ProjectiveSpaceOver N R).Modules := projectiveSpaceOverTwist R N a
  let M : (ProjectiveSpaceOver N R).Modules := projectiveSpaceOverTwist R N (-a)
  let FL := CategoryTheory.MonoidalCategory.tensorRight L
  let _ : FL.IsEquivalence :=
    AlgebraicGeometry.Scheme.Modules.isEquivalence_tensorRight_of_isLineBundle L
  have eDual :
      FL.obj (AlgebraicGeometry.Scheme.Modules.dual L) ≅ FL.obj M := by
    let u : (AlgebraicGeometry.Scheme.Modules.dual (projectiveSpaceOverTwist R N a)) ⊗
        projectiveSpaceOverTwist R N a ≅ 𝟙_ (ProjectiveSpaceOver N R).Modules :=
      β_ _ _ ≪≫
        (AlgebraicGeometry.Scheme.Modules.nonempty_tensorObj_dual_iso_tensorUnit
          (projectiveSpaceOverTwist R N a)).some
    simpa [FL, L, M, A] using (u ≪≫ eAunit.symm) ≪≫ eML₀.symm
  exact ⟨(FL.asEquivalence.fullyFaithfulFunctor).preimageIso eDual⟩

/-- `mpow (O(1)^∨) (m+1) ≅ O(-(m+1))` on `P^N_R`: induction on `m`, base case
`O(1)^∨ ⊗ 𝟙 ≅ O(1)^∨ ≅ O(-1)` (`projectiveSpaceOverTwist_dual`), step
`O(1)^∨ ⊗ mpow (O(1)^∨) (m+1) ≅ O(-1) ⊗ O(-(m+1)) ≅ O(-(m+2))` (`projectiveSpaceOverTwist_tensor`). -/
noncomputable def projectiveSpaceOverTwist_mpowDualIso (R : Type u) [CommRing R] (N : ℕ) :
    (m : ℕ) →
      (AlgebraicGeometry.Scheme.Modules.mpow
        (AlgebraicGeometry.Scheme.Modules.dual (projectiveSpaceOverTwist R N 1)) (m + 1) ≅
        projectiveSpaceOverTwist R N (-((m + 1 : ℕ) : ℤ)))
  | 0 =>
    (CategoryTheory.MonoidalCategory.rightUnitor
        (AlgebraicGeometry.Scheme.Modules.dual (projectiveSpaceOverTwist R N 1))) ≪≫
      Classical.choice (projectiveSpaceOverTwist_dual R N 1) ≪≫
      CategoryTheory.eqToIso (by norm_num)
  | m + 1 =>
    CategoryTheory.MonoidalCategory.tensorIso
        (Classical.choice (projectiveSpaceOverTwist_dual R N 1))
        (projectiveSpaceOverTwist_mpowDualIso R N m) ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).symm ≪≫
      Classical.choice (projectiveSpaceOverTwist_tensor R N (-1) (-((m + 1 : ℕ) : ℤ))) ≪≫
      CategoryTheory.eqToIso (by congr 1; push_cast; ring)

/-- The ℤ-power `O(1) ^ (-(n:ℤ))` of the line bundle `O(1)` is `O(-n)` for `n > 0`. -/
noncomputable def projectiveSpaceOverTwist_zpowNegIso (R : Type u) [CommRing R] (N : ℕ) (n : ℕ)
    (hn : 0 < n) :
    (projectiveSpaceOverTwist R N 1 ^ (-(n : ℤ)) : (ProjectiveSpaceOver N R).Modules) ≅
      projectiveSpaceOverTwist R N (-(n : ℤ)) :=
  match n, hn with
  | m + 1, _ =>
    (AlgebraicGeometry.Scheme.Modules.tensorPowerIsoMpow
        (AlgebraicGeometry.Scheme.Modules.dual (projectiveSpaceOverTwist R N 1)) (m + 1) :
      AlgebraicGeometry.Scheme.Modules.moduleTensorPower
        (AlgebraicGeometry.Scheme.Modules.dual (projectiveSpaceOverTwist R N 1)) (m + 1) ≅ _) ≪≫
      projectiveSpaceOverTwist_mpowDualIso R N m

/-- **Stacks 01YS(1) over a ring**: a coherent module on `P^N_R` is a quotient of a finite direct sum of
twists `⨁_j O(d_j)`. -/
theorem exists_epi_biproduct_twists_projectiveSpaceOver (R : Type u) [CommRing R] (N : ℕ)
    (G : (ProjectiveSpaceOver N R).Modules) [G.IsCoherent] :
    ∃ (r : ℕ) (d : Fin r → ℤ)
      (p : CategoryTheory.Limits.biproduct (fun j => projectiveSpaceOverTwist R N (d j)) ⟶ G),
      CategoryTheory.Epi p := by
  have : G.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
  have : G.IsFiniteType := AlgebraicGeometry.Scheme.Modules.IsCoherent.finiteType
  obtain ⟨n, hn, r, p, hp⟩ :=
    (projectiveSpaceOverTwist_one_isAmple R N).exists_epi_biproduct_zpow_neg
      (projectiveSpaceOverTwist R N 1) G
  refine ⟨r, fun _ => -(n : ℤ),
    (CategoryTheory.Limits.biproduct.mapIso
      fun _ : Fin r => (projectiveSpaceOverTwist_zpowNegIso R N n hn).symm).hom ≫ p, ?_⟩
  exact CategoryTheory.epi_comp _ _

end
