import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOver
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundle
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformationFamilyProj
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.FamilyFiberAtZeroFiberOverLine
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjIsoOfAlgebraIso
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectivizationOfBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymAlgebra

/-! # The fiber of the deformation family at `λ = 0`

The fiber of `𝒴` at `λ = 0` is the weighted projectivization of `k` copies of `E` in the weights `1, …, k`
(Lemma 2.3 of the paper, "removing the nonlinear terms").

Proof:
1. `deformedJetAlgebra_spec`: the restriction `R|_{λ=0} = R.pullback (sectionAt 0)` of `R := deformedJetAlgebra`
   is isomorphic (`φ`) to the weighted symmetric algebra `W` of `r` copies of `E`.
2. `relativeProj_fiber_over_line` (Stacks 01O3 and gluing of pullbacks): the fiber of
   `𝒴 = Proj R → C × 𝔸¹ → 𝔸¹_k` at `λ = 0` is `≅ Proj_C (R|_{λ=0})` (`ε`), over `C`, with `O(m)` corresponding.
3. `relativeProj.exists_iso_of_algebra_iso`: `φ` induces `Proj_C (R|_{λ=0}) ≅ Proj_C W = weightedProjBundle(E,…,E)`
   (`ψ`), over `C`, with `O(m)` corresponding.
4. `e := ε ≪≫ ψ`; the correspondence of `O(m)` is the composite of the two steps (`Modules.pullbackComp`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem deformationFamily_fiber_zero {k : Type u} [Field k] [CharZero k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) [AlgebraicGeometry.IsClosedImmersion sec]
    (Zx : Z.left.Opens) (hsZx : ∀ c, sec.base c ∈ Zx) (n r : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom)]
    (E : AlgebraicGeometry.VectorBundle C.toVariety) (hE : E.rank = n + 1)
    (hEZ : Nonempty (E.toModules ≅ coneTangentBundle Z.hom sec hs))
    (hloc : ((jetGradedAlgebra (k := k) Z sec hs r).1).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _)) :
    ∃ e : (((deformationFamily Z sec hs r).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme).fiber (AlgebraicGeometry.Scheme.affineLineOver.point k 0) ≅ (@AlgebraicGeometry.Scheme.weightedProjBundle _ r (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree) (fun _ => E.isFiniteType)).left),
      e.hom ≫ (@AlgebraicGeometry.Scheme.weightedProjBundle _ r (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree) (fun _ => E.isFiniteType)).hom =
          ((deformationFamily Z sec hs r).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme).fiberι (AlgebraicGeometry.Scheme.affineLineOver.point k 0) ≫ (deformationFamily Z sec hs r).hom ≫
          AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ∧
      ∀ m : ℤ, Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback (((deformationFamily Z sec hs r).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme).fiberι (AlgebraicGeometry.Scheme.affineLineOver.point k 0))).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist (deformedJetAlgebra Z sec hs r) m) ≅
        (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist ((@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree) (fun _ => E.isFiniteType))) m)) := by
  obtain ⟨-, -, ⟨φ⟩⟩ := deformedJetAlgebra_spec Z sec hs Zx hsZx n r E hE hEZ hloc
  obtain ⟨ε, hε, hεtw⟩ := AlgebraicGeometry.Scheme.relativeProj_fiber_over_line (X := C.toScheme)
    (deformedJetAlgebra Z sec hs r) (0 : k)
  obtain ⟨ψ, hψ, hψtw⟩ := AlgebraicGeometry.Scheme.relativeProj.exists_iso_of_algebra_iso φ
  refine ⟨ε ≪≫ ψ, ?_, fun m => ?_⟩
  · show (ε ≪≫ ψ).hom ≫ (AlgebraicGeometry.Scheme.relativeProj
        (@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r (fun _ : Fin r => E.toModules)
          (fun _ => E.locallyFree) (fun _ => E.isFiniteType))).hom = _
    rw [Iso.trans_hom, Category.assoc, hψ]
    exact hε
  · obtain ⟨a⟩ := hεtw m
    obtain ⟨b⟩ := hψtw m
    exact ⟨a ≪≫ (AlgebraicGeometry.Scheme.Modules.pullback ε.hom).mapIso b ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp ε.hom ψ.hom).app _⟩

end
