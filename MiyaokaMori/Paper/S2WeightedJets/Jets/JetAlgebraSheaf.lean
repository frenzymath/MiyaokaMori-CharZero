import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetScheme
import MiyaokaMori.Paper.S2WeightedJets.Jets.CoeffSystemInstances
import MiyaokaMori.RingTheory.GradedRing.GradedRingAddSubgroup
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProj

/-! # The jet coordinate algebra as a graded affine algebra

The graded coordinate algebra `𝒮 = ⊕_m 𝒮_m` of §2 of the paper as a graded quasi-coherent algebra on `C`,
`jetGradedAffineAlgebra Z s hs r : C.GradedAffineAlgebra`: an affine open `U` is sent to `J_r(B_U, ε_U)`
(`BasedJetAlgebra`, `B_U = Γ(Z, π⁻¹U)`, `ε_U = s^♯`), and the `m`-th piece consists of the classes of the jet coordinate
polynomials of weight `m` (`BasedJetAlgebra.grading`, `d_q b` having weight `q+1`). Its `toAffineAlgebra` is
`jetAffineAlgebra Z s hs r` (`RelativeJetScheme`), and `J_r^s(Z/C) = relativeJetScheme` is the `relativeSpec` of that
algebra. We prove `jetGradedAffineAlgebra_isConnected` (`𝒮_0 = O_C`).

All data is constructive: rings, restrictions and structure maps are `relativeJetScheme.chartFunctor` /
`coefficientMap`, the grading is `BasedJetAlgebra.grading`, and restriction preserves the grading by `map_mem_grading`.
The quasi-coherence is `coefficientMap_coequifibered` (`J_r(B_f) ≅ J_r(B)_f`, the affine version of Ein–Mustață
Lemma 2.3).

References: §2 of the paper; Ein–Mustață §2; Vojta §1.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

variable {C : AlgebraicGeometry.Scheme.{u}} (Z : CategoryTheory.Over C)
  [AlgebraicGeometry.IsAffineHom Z.hom] (s : C ⟶ Z.left)
  (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)

/-- The grading of the chart ring over `U` (the weight-`m` piece), valued in `AddSubgroup`. -/
def relativeJetScheme.chartGrading (U : C.AffineZariskiSite) :
    ℕ → AddSubgroup (relativeJetScheme.chartRing Z s hs r U.toOpens) :=
  letI := relativeJetScheme.sectionsAlgebra Z U.toOpens
  GradedRing.addSubgroupGrading
    (BasedJetAlgebra.grading (relativeJetScheme.augmentation Z s hs U.toOpens) r)

instance relativeJetScheme.chartGrading_gradedRing (U : C.AffineZariskiSite) :
    GradedRing (relativeJetScheme.chartGrading Z s hs r U) :=
  letI := relativeJetScheme.sectionsAlgebra Z U.toOpens
  GradedRing.addSubgroup
    (BasedJetAlgebra.grading (relativeJetScheme.augmentation Z s hs U.toOpens) r)

/-- **The jet coordinate algebra `𝒮`** (§2 of the paper): a graded quasi-coherent algebra on `C`. -/
def jetGradedAffineAlgebra : C.GradedAffineAlgebra where
  toAffineAlgebra := jetAffineAlgebra Z s hs r
  grading U := relativeJetScheme.chartGrading Z s hs r U
  graded U := relativeJetScheme.chartGrading_gradedRing Z s hs r U
  restrict_mem {U V} h {m a} ha := by
    let _ := relativeJetScheme.sectionsAlgebra Z U.toOpens
    let _ := relativeJetScheme.sectionsAlgebra Z V.toOpens
    have hle : U.toOpens ≤ V.toOpens := AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono h
    exact BasedJetAlgebra.map_mem_grading _ r _ _ _
      (relativeJetScheme.chartFunctor_smul Z hle)
      (fun b => congrArg
        (fun φ : Γ(Z.left, Z.hom ⁻¹ᵁ V.toOpens) ⟶ Γ(C, U.toOpens) => CommRingCat.Hom.hom φ b)
        (relativeJetScheme.augmentation_naturality Z s hs hle)) ha
  unit_mem U a := by
    let _ := relativeJetScheme.sectionsAlgebra Z U.toOpens
    exact BasedJetAlgebra.algebraMap_mem_grading_zero _ r a

/-- `𝒮_0 = O_C`: the degree-`0` piece is exactly the structure sheaf (all generators have positive weight, and the
constant jet gives the augmentation). -/
theorem jetGradedAffineAlgebra_isConnected : (jetGradedAffineAlgebra Z s hs r).IsConnected := by
  intro U
  let _ := relativeJetScheme.sectionsAlgebra Z U.toOpens
  constructor
  · intro a b hab
    exact BasedJetAlgebra.CoeffSystem.algebraMap_injective
      (relativeJetScheme.augmentation Z s hs U.toOpens) r (congrArg Subtype.val hab)
  · rintro ⟨x, hx⟩
    have hx' : x ∈ BasedJetAlgebra.grading (relativeJetScheme.augmentation Z s hs U.toOpens) r 0 := hx
    rw [BasedJetAlgebra.grading_zero] at hx'
    obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hx'
    exact ⟨a, Subtype.ext rfl⟩

end
