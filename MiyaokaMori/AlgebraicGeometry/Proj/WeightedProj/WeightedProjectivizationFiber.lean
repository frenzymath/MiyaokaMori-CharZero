import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectivizationFiberLocalAlgIso
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistingSheaf
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.RelativeProjWeightedPolynomialProduct
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjIsoOfAlgebraIso
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedGradedAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01o3

/-! # Fibers of the weighted projectivization

The fibers of the relative Proj `π_k` of a locally weighted polynomial algebra are weighted
projective spaces over the residue fields: `n+1` coordinates of each weight `1, …, k`, of dimension
`(n+1)k − 1` (proof of the Veronese polarization lemma of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Over `Spec k`, the relative Proj of the weighted polynomial algebra is `P_k(w)` (compatibly with
the structure morphisms), with `O(m)` corresponding to `weightedProjTwist k w hw m`: the case
`U = Spec k` of `relativeProj_weightedPolynomialAlgebra_iso`. -/
private theorem weightedProjectivizationFiber_prod_data {k : Type u} [Field k]
    {σ : Type u} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    ∃ e : (AlgebraicGeometry.Scheme.relativeProj
      (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra
        (AlgebraicGeometry.Spec (CommRingCat.of k)) w hw)).left ≅
      weightedProjectiveSpace k w hw,
      e.hom ≫ (weightedProjectiveSpace k w hw ↘
          AlgebraicGeometry.Spec (CommRingCat.of k)) =
        (AlgebraicGeometry.Scheme.relativeProj
          (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra
            (AlgebraicGeometry.Spec (CommRingCat.of k)) w hw)).hom ∧
      ∀ m : ℤ, Nonempty (AlgebraicGeometry.Scheme.relativeProj.twist
          (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra
            (AlgebraicGeometry.Spec (CommRingCat.of k)) w hw) m ≅
        (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj
          (weightedProjTwist k w hw m)) := by
  obtain ⟨φ, hφ, htw⟩ := relativeProj_weightedPolynomialAlgebra_iso
    (k := k) (U := AlgebraicGeometry.Spec (CommRingCat.of k))
    (CategoryTheory.CategoryStruct.id _) w hw
  let e := φ ≪≫ asIso (CategoryTheory.Limits.pullback.snd
    (CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of k)))
    (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
  refine ⟨e, ?_, ?_⟩
  · dsimp [e]
    simp only [Iso.trans_hom, Category.assoc]
    rw [← CategoryTheory.Limits.pullback.condition]
    simpa using hφ
  · intro m
    obtain ⟨h⟩ := htw m
    exact ⟨by simpa [e] using h⟩

/-- The fiber of `Proj_X S → X` over `x` is the weighted projective space over the residue field
`κ(x)`, compatibly with the structure morphisms, and `O(m)` restricts to `O_{P(w)}(m)`. Proof:
`S` pulled back to `Spec κ(x)` is the weighted polynomial algebra
(`weightedProjectivizationFiber_local_alg_iso`), the relative Proj commutes with base change
(`relativeProj_baseChange`, Stacks 01O3), and over `Spec κ(x)` it is `P(w)`. -/
theorem relativeProj_fiber_weightedProjectiveSpace {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) {σ : Type u} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (hS : S.IsLocallyWeightedPolynomial w hw) (x : X) :
    ∃ e : (AlgebraicGeometry.Scheme.relativeProj S).hom.fiber x ≅
        weightedProjectiveSpace (X.residueField x) w hw,
      e.hom ≫ (weightedProjectiveSpace (X.residueField x) w hw ↘
          AlgebraicGeometry.Spec (CommRingCat.of (X.residueField x))) =
        (AlgebraicGeometry.Scheme.relativeProj S).hom.fiberToSpecResidueField x ∧
      ∀ m : ℤ, Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
            ((AlgebraicGeometry.Scheme.relativeProj S).hom.fiberι x)).obj
            (AlgebraicGeometry.Scheme.relativeProj.twist S m) ≅
          (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj
            (weightedProjTwist (X.residueField x) w hw m)) := by
  let p := X.fromSpecResidueField x
  obtain ⟨α, _⟩ := weightedProjectivizationFiber_local_alg_iso S w hw hS x
  obtain ⟨ε, hε, hεtw⟩ := AlgebraicGeometry.Scheme.relativeProj.exists_iso_of_algebra_iso α
  obtain ⟨β, hβ, hβtw⟩ := AlgebraicGeometry.Scheme.relativeProj_baseChange p S
  obtain ⟨δ, hδ, hδtw⟩ := weightedProjectivizationFiber_prod_data (k := X.residueField x) w hw
  let γ : (AlgebraicGeometry.Scheme.relativeProj S).hom.fiber x ≅
      (AlgebraicGeometry.Scheme.relativeProj (S.pullback p)).left :=
    (show CategoryTheory.Limits.pullback
        (AlgebraicGeometry.Scheme.relativeProj S).hom
        (X.fromSpecResidueField x) ≅ _ from
      (CategoryTheory.Limits.pullbackSymmetry (X.fromSpecResidueField x)
        (AlgebraicGeometry.Scheme.relativeProj S).hom).symm) ≪≫ β.symm
  let e : (AlgebraicGeometry.Scheme.relativeProj S).hom.fiber x ≅
      weightedProjectiveSpace (X.residueField x) w hw := γ ≪≫ ε ≪≫ δ
  refine ⟨e, ?_, ?_⟩
  · have hγ : γ.hom ≫ β.hom ≫ CategoryTheory.Limits.pullback.snd p
        (AlgebraicGeometry.Scheme.relativeProj S).hom =
        (AlgebraicGeometry.Scheme.relativeProj S).hom.fiberι x := by
      dsimp [γ, p, AlgebraicGeometry.Scheme.Hom.fiber]
      change _ = CategoryTheory.Limits.pullback.fst
        (AlgebraicGeometry.Scheme.relativeProj S).hom
        (X.fromSpecResidueField x)
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [CategoryTheory.Limits.pullbackSymmetry_inv_comp_snd]
    have hb : β.hom ≫ CategoryTheory.Limits.pullback.fst p
        (AlgebraicGeometry.Scheme.relativeProj S).hom =
        (AlgebraicGeometry.Scheme.relativeProj (S.pullback p)).hom := hβ
    have hγbase : γ.hom ≫ (AlgebraicGeometry.Scheme.relativeProj (S.pullback p)).hom =
        (AlgebraicGeometry.Scheme.relativeProj S).hom.fiberToSpecResidueField x := by
      dsimp [γ, p, AlgebraicGeometry.Scheme.Hom.fiber]
      change _ = CategoryTheory.Limits.pullback.snd
        (AlgebraicGeometry.Scheme.relativeProj S).hom
        (X.fromSpecResidueField x)
      rw [← hb]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [CategoryTheory.Limits.pullbackSymmetry_inv_comp_fst]
    calc
      e.hom ≫ (weightedProjectiveSpace (X.residueField x) w hw ↘
          AlgebraicGeometry.Spec (CommRingCat.of (X.residueField x))) =
          γ.hom ≫ ε.hom ≫ δ.hom ≫
            (weightedProjectiveSpace (X.residueField x) w hw ↘
              AlgebraicGeometry.Spec (CommRingCat.of (X.residueField x))) := by
                simp [e, Category.assoc]
      _ = γ.hom ≫ ε.hom ≫
          (AlgebraicGeometry.Scheme.relativeProj
            (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra
              (AlgebraicGeometry.Spec (CommRingCat.of (X.residueField x))) w hw)).hom := by
        rw [hδ]
      _ = γ.hom ≫ (AlgebraicGeometry.Scheme.relativeProj (S.pullback p)).hom := by
        rw [← hε]
      _ = _ := hγbase
  · intro m
    have hγ : γ.hom ≫ β.hom ≫ CategoryTheory.Limits.pullback.snd p
        (AlgebraicGeometry.Scheme.relativeProj S).hom =
        (AlgebraicGeometry.Scheme.relativeProj S).hom.fiberι x := by
      dsimp [γ, p, AlgebraicGeometry.Scheme.Hom.fiber]
      change _ = CategoryTheory.Limits.pullback.fst
        (AlgebraicGeometry.Scheme.relativeProj S).hom
        (X.fromSpecResidueField x)
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [CategoryTheory.Limits.pullbackSymmetry_inv_comp_snd]
    have hpb : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
        ((AlgebraicGeometry.Scheme.relativeProj S).hom.fiberι x)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S m) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback γ.hom).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist (S.pullback p) m)) := by
      let q := β.hom ≫ CategoryTheory.Limits.pullback.snd p
          (AlgebraicGeometry.Scheme.relativeProj S).hom
      have hγq : γ.hom ≫ q =
          (AlgebraicGeometry.Scheme.relativeProj S).hom.fiberι x := by
        simpa [q, Category.assoc] using hγ
      let c := (AlgebraicGeometry.Scheme.Modules.pullbackComp γ.hom
        q).app (AlgebraicGeometry.Scheme.relativeProj.twist S m)
      have hb' : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback q).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist S m) ≅
        AlgebraicGeometry.Scheme.relativeProj.twist (S.pullback p) m) := by
        simpa [q] using hβtw m
      obtain ⟨b'⟩ := hb'
      exact ⟨(AlgebraicGeometry.Scheme.Modules.pullbackCongr hγq.symm).app _ ≪≫
        c.symm ≪≫ (AlgebraicGeometry.Scheme.Modules.pullback γ.hom).mapIso b'⟩
    obtain ⟨a⟩ := hpb
    obtain ⟨b⟩ := hεtw m
    obtain ⟨c⟩ := hδtw m
    exact ⟨a ≪≫ (AlgebraicGeometry.Scheme.Modules.pullback γ.hom).mapIso b ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp γ.hom ε.hom).app _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback (γ.hom ≫ ε.hom)).mapIso c ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp (γ.hom ≫ ε.hom) δ.hom).app _⟩

end
