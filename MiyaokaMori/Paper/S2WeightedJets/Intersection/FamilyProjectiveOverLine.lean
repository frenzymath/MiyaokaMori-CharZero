import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformationFamilyProj
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Morphisms.FamilyProjectiveOverLineGeneral
import MiyaokaMori.Paper.S2WeightedJets.Ygg.VeronesePolarizationVeryAmple

/-! # The deformation family is projective over the line

A sufficiently divisible Veronese makes `𝒴` projective over `C × 𝔸¹`; since `C` is projective, `𝒴` is projective
over `𝔸¹`, with an invertible sheaf `O(m)` (Lemma 2.3 of the paper).

Proof. Write `S = deformedJetAlgebra Z sec hs r` (the Rees deformation of the jet graded algebra on
`C × A¹`) and `σ = Fin (n+1) × Fin r` with weights `w(i, q) = q + 1 ∈ [1, r]`; `σ ≠ ∅` since `r ≥ 1`
and `|σ| = (n+1) r`, so `m = |σ| · lcm(1,…,r)`. `deformedJetAlgebra_spec`
says `S` is locally a weighted polynomial algebra with these weights.
* Line bundle: `twist_isLineBundle_relativelyVeryAmple` with `c = 1` gives that `O_𝒴(m)` is invertible.
* Projectivity: `relativeProj_locallyWeighted_isProjective_over_line`: `𝒴 → C × A¹` is projective by the
  Veronese argument (`S^{(m)}` generated in degree one, `S_m` of finite type, `𝒴 ≅ Proj S^{(m)}`),
  `C × A¹ → A¹_k` is the base change of the projective `C → Spec k`, and `A¹_k` is affine, so the
  composite is projective.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem deformationFamily_projective {k : Type u} [Field k] [CharZero k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) (n r : ℕ)
    (E : AlgebraicGeometry.VectorBundle C.toVariety) (hE : E.rank = n + 1)
    (hEZ : Nonempty (E.toModules ≅ coneTangentBundle Z.hom sec hs))
    (hloc : ((jetGradedAlgebra (k := k) Z sec hs r).1).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _))
    (hr : 1 ≤ r) (m : ℕ) (hm : m = (n + 1) * r * jetWeight r) :
    AlgebraicGeometry.IsProjectiveMorphism ((deformationFamily Z sec hs r).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme) ∧
      (AlgebraicGeometry.Scheme.relativeProj.twist
        (deformedJetAlgebra Z sec hs r) (m : ℤ)).IsLineBundle := by
  have hspec := deformedJetAlgebra_isLocallyWeightedPolynomial Z sec hs n r hloc
  have : Nonempty (ULift.{u} (Fin (n + 1) × Fin r)) := ⟨⟨(0, ⟨0, hr⟩)⟩⟩
  have hw : ∀ iq : ULift.{u} (Fin (n + 1) × Fin r), ((iq.down.2 : ℕ) + 1) ∈ Finset.Icc 1 r :=
    fun iq => Finset.mem_Icc.mpr ⟨Nat.succ_pos _, Nat.succ_le_of_lt iq.down.2.isLt⟩
  have hcard : Fintype.card (ULift.{u} (Fin (n + 1) × Fin r)) = (n + 1) * r := by
    simp [Fintype.card_ulift, Fintype.card_prod, Fintype.card_fin]
  have hm' : m = 1 * (Fintype.card (ULift.{u} (Fin (n + 1) × Fin r)) * jetWeight r) := by
    rw [hcard, one_mul, hm]
  refine ⟨?_, (twist_isLineBundle_relativelyVeryAmple (deformedJetAlgebra Z sec hs r) _ hw hspec
    1 m one_pos hm').1⟩
  exact relativeProj_locallyWeighted_isProjective_over_line C.projective
    (deformedJetAlgebra Z sec hs r) _ hw hspec

end
