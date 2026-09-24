import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.DivisorDL
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetChartTrivialization
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleFrame

/-! # Normalization under a change of frame

Under a change of frame `ε' = uε` one has `γ' = γ/u`: the weight-`q` coefficients are multiplied by `u^q` and the
source coordinate becomes `t' = u^{-1}t`, so the normalized coefficients satisfy the same jet transition relation
(§3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem normalized_coefficients_frame_change {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} {n κ : ℕ} {U : Ct.toScheme.Opens} [Nonempty U]
    (hU : genericPoint Ct.toScheme ∈ U)
    (L : LineBundle Ct.toVariety) (ε ε' : LineBundle.Frame L U) (u : Γ(Ct.toScheme, U)ˣ)
    (hu : ε'.section_ = (u : Γ(Ct.toScheme, U)) • ε.section_)
    /- The paper's "rational section `1 = γε`": `s` is a rational section of `L` (an element of the stalk at the
       generic point; for `L = O(D_L)` take `s = 1`), and `γ`, `γ'` are its coefficients in the two frames. -/
    (s : L.toModules.stalk (genericPoint Ct.toScheme))
    (γ γ' : Ct.toScheme.functionField)
    (hγ : s = γ • (L.toModules.presheaf.germ U (genericPoint Ct.toScheme) hU ε.section_ :
      L.toModules.stalk (genericPoint Ct.toScheme)))
    (hγ' : s = γ' • (L.toModules.presheaf.germ U (genericPoint Ct.toScheme) hU ε'.section_ :
      L.toModules.stalk (genericPoint Ct.toScheme)))
    (a : Fin (n + 1) → Fin κ → Ct.toScheme.functionField) :
    γ' = γ * (Ct.toScheme.germToFunctionField U (u : Γ(Ct.toScheme, U)))⁻¹ ∧
    ∀ i (q : Fin κ), γ' ^ (-((q : ℕ) + 1 : ℤ)) * a i q
      = (Ct.toScheme.germToFunctionField U (u : Γ(Ct.toScheme, U))) ^ ((q : ℕ) + 1)
        * (γ ^ (-((q : ℕ) + 1 : ℤ)) * a i q) := by
  have he : (L.toModules.presheaf.germ U (genericPoint Ct.toScheme) hU ε.section_ :
      L.toModules.stalk (genericPoint Ct.toScheme)) ≠ 0 := by
    intro hz
    have hspan := ε.generates (genericPoint Ct.toScheme) hU
    rw [hz] at hspan
    have hbot : (⊥ : Submodule (Ct.toVariety.toScheme.presheaf.stalk (genericPoint Ct.toScheme))
        (L.toModules.stalk (genericPoint Ct.toScheme))) = ⊤ := by
      rw [← Submodule.span_zero]
      exact hspan
    have hzero : ∀ y : L.toModules.stalk (genericPoint Ct.toScheme), y = 0 := by
      intro y
      have hy : y ∈ (⊥ : Submodule (Ct.toVariety.toScheme.presheaf.stalk
          (genericPoint Ct.toScheme)) (L.toModules.stalk (genericPoint Ct.toScheme))) := by
        rw [hbot]
        exact Submodule.mem_top
      simpa using hy
    letI : Subsingleton (L.toModules.stalk (genericPoint Ct.toScheme)) :=
      ⟨fun a b => (hzero a).trans (hzero b).symm⟩
    have hzeroRank : AlgebraicGeometry.Scheme.Modules.rankAtStalk L.toModules
        (genericPoint Ct.toScheme) = 0 := by
      unfold AlgebraicGeometry.Scheme.Modules.rankAtStalk
      letI := (Ct.toScheme.residue (genericPoint Ct.toScheme)).hom.toAlgebra
      exact Module.finrank_zero_of_subsingleton
    have honeRank : AlgebraicGeometry.Scheme.Modules.rankAtStalk L.toModules
        (genericPoint Ct.toScheme) = 1 := by
      rw [L.toVectorBundle.rankAtStalk_eq (genericPoint Ct.toScheme), L.rank_eq_one]
    omega
  have hEq := hγ.symm.trans hγ'
  dsimp [AlgebraicGeometry.Scheme.Modules.stalk, AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor] at hEq
  dsimp [AlgebraicGeometry.Scheme.Modules.presheaf] at hEq
  rw [hu] at hEq
  erw [PresheafOfModules.germ_smul (R := Ct.toScheme.presheaf) L.toModules.val] at hEq
  have hEq'' : γ • (L.toModules.presheaf.germ U (genericPoint Ct.toScheme) hU ε.section_ :
      L.toModules.stalk (genericPoint Ct.toScheme)) =
      γ' • (Ct.toScheme.presheaf.germ U (genericPoint Ct.toScheme) hU
        (u : Γ(Ct.toScheme, U))) •
        (L.toModules.presheaf.germ U (genericPoint Ct.toScheme) hU ε.section_ :
          L.toModules.stalk (genericPoint Ct.toScheme)) := by
    exact hEq
  rw [← IsScalarTower.algebraMap_smul
    Ct.toScheme.functionField] at hEq''
  rw [← mul_smul] at hEq''
  have hEq' : γ • (L.toModules.presheaf.germ U (genericPoint Ct.toScheme) hU ε.section_ :
      L.toModules.stalk (genericPoint Ct.toScheme)) =
      (γ' * Ct.toScheme.germToFunctionField U (u : Γ(Ct.toScheme, U))) •
        (L.toModules.presheaf.germ U (genericPoint Ct.toScheme) hU ε.section_ :
          L.toModules.stalk (genericPoint Ct.toScheme)) := by
    rw [← Ct.toScheme.algebraMap_germ_eq_germToFunctionField hU (u : Γ(Ct.toScheme, U))]
    simpa [Algebra.smul_def, mul_comm] using hEq''
  have hcoeff : γ = γ' * Ct.toScheme.germToFunctionField U (u : Γ(Ct.toScheme, U)) := by
    exact (smul_left_injective Ct.toScheme.functionField he) hEq'
  have huK : Ct.toScheme.germToFunctionField U (u : Γ(Ct.toScheme, U)) ≠ 0 := by
    exact (IsUnit.map (Ct.toScheme.germToFunctionField U).hom (Units.isUnit u)).ne_zero
  have hmain : γ' = γ * (Ct.toScheme.germToFunctionField U (u : Γ(Ct.toScheme, U)))⁻¹ := by
    rw [hcoeff, mul_assoc, mul_inv_cancel₀ huK]
    simp
  constructor
  · exact hmain
  · intro i q
    let m : ℕ := (q : ℕ) + 1
    change γ' ^ (-(m : ℤ)) * a i q =
      (Ct.toScheme.germToFunctionField U (u : Γ(Ct.toScheme, U))) ^ m *
        (γ ^ (-(m : ℤ)) * a i q)
    rw [hmain, mul_zpow, inv_zpow]
    simp only [zpow_neg]
    simp [huK, mul_assoc, mul_comm, mul_left_comm]

end
