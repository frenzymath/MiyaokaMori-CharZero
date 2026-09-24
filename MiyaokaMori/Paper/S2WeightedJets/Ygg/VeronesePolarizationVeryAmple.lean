import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.VeroneseGenerationMultiple
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.VeroneseTwistPullback
import MiyaokaMori.AlgebraicGeometry.Modules.RelativelyVeryAmple
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistInvertibleSufficientlyDivisible

/-! # The Veronese polarization is relatively very ample

For a locally weighted polynomial graded algebra `S` with weights in `[1, k]` and
`m = c · (card σ · w_k)`, the twisting sheaf `B_k = O_{Y_k^GG}(m)` is a line bundle and is
relatively very ample over the base; this follows from the generation of the Veronese
subalgebra in degree one (Lemma 2.2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem twist_isLineBundle_relativelyVeryAmple {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) {σ : Type u} [Fintype σ] [Nonempty σ] {k : ℕ} (w : σ → ℕ)
    (hw : ∀ i, w i ∈ Finset.Icc 1 k)
    (hS : S.IsLocallyWeightedPolynomial w (fun i => (Finset.mem_Icc.mp (hw i)).1))
    (c m : ℕ) (hc : 0 < c) (hm : m = c * (Fintype.card σ * jetWeight k)) :
    (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)).IsLineBundle ∧
      AlgebraicGeometry.Scheme.Modules.IsRelativelyVeryAmple
        (AlgebraicGeometry.Scheme.relativeProj S).hom
        (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)) := by
  have hSD0 := veronese_generation_multiple S w hw hS c hc
  have hSD : S.SufficientlyDivisible m := by
    simpa [hm] using hSD0
  have hL := AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist S m hSD
  have hgen : (S.veronese m).GeneratedInDegreeOne := hSD.2
  have hmpos : 0 < m := hSD.1
  let e := AlgebraicGeometry.Scheme.relativeProj.veroneseIso S m hmpos
  have hi : AlgebraicGeometry.IsClosedImmersion e.inv.left := by
    have hleft : e.inv.left ≫ e.hom.left = 𝟙 _ := by
      exact congrArg CategoryTheory.Over.Hom.left e.inv_hom_id
    have hcomp : AlgebraicGeometry.IsClosedImmersion (e.inv.left ≫ e.hom.left) := by
      rw [hleft]
      infer_instance
    exact AlgebraicGeometry.IsClosedImmersion.of_comp e.inv.left e.hom.left
  have hover : e.inv.left ≫
      (AlgebraicGeometry.Scheme.relativeProj (S.veronese m)).hom =
      (AlgebraicGeometry.Scheme.relativeProj S).hom := by
    exact CategoryTheory.Over.w e.inv
  refine ⟨hL, ?_⟩
  refine ⟨S.veronese m, e.inv.left, hgen, hi, hover, ?_⟩
  exact AlgebraicGeometry.Scheme.relativeProj.veronese_twist_pullback_iso S m hmpos

end
