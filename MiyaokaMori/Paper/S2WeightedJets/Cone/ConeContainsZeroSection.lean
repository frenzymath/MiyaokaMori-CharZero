import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousAtSections
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousLocalFormula
import MiyaokaMori.AlgebraicGeometry.Modules.HomogeneousEquationAsSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.ScalarActionOnConeHomogeneousPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivCoordinates
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivNaturality
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSection
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineCone
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ConeScalingActionIdealSheafOfSectionLeKer
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.Stacks02or

/-! # The cone contains the zero section

The zero section lands in `𝒵` (each `F_j` is homogeneous of degree `≥ 1`, hence vanishes at the zero
vector) (Definition 2.1 of the paper).

Route:
1. The tautological section `τ ∈ Γ(Tot V, π^*V)` pulls back to `0` along the zero section `σ_0`
   (`totalSpaceHomEquiv_eq_zero_of_factors_zeroSection` + `totalSpaceHomEquiv_naturality`; the same
   proof as `sectionPullbackAlong_zeroSection_tautological` of `SeedSectionInPunctured`, restated here
   because of the import direction).
2. `homogeneousEquationSection` is by definition the homogeneous evaluation of `F` on the coordinates
   `τ_i = π^*(pr_i)(τ)`; pulling back along `σ_0` (`evalHomogeneousAtSections_pullback`) gives the
   evaluation of `F` at `σ_0^*τ_i = 0` (`sectionPullbackAlong_naturality`), and for `e ≥ 1` one has
   `F(0, …, 0) = 0` (`evalHomogeneousAtSections_smul_pow` with `a = 0`: `F(0 • f) = 0^e • F(f) = 0`).
3. The section criterion `idealSheafOfSection_le_ker_iff`: `I(F_j) ≤ ker σ_0` for all `j`, hence
   `⨆_j I(F_j) = ker ι ≤ ker σ_0` (`IdealSheafData.ker_subschemeι`, `iSup_le`); the lift along the
   closed immersion, `IsClosedImmersion.lift`, gives `σ : C → Z` with `σ ≫ ι = σ_0` (`lift_fac`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The tautological section `τ = totalSpaceHomEquiv V Tot(V) (𝟙) ∈ Γ(Tot V, π^*V)` pulls back to zero
along the zero section.
Proof: `totalSpaceHomEquiv_naturality` identifies `σ_0^*τ` (through `pullbackComp`) with the section
corresponding to `σ_0 ≫ 𝟙`, which is `0` because it factors through the zero section
(`totalSpaceHomEquiv_eq_zero_of_factors_zeroSection`); an isomorphism preserves `= 0`.
(Same statement and proof as `SeedSectionInPunctured.sectionPullbackAlong_zeroSection_tautological`;
that file imports this one, hence the separate name.) -/
theorem AlgebraicGeometry.Scheme.zeroSection_pullback_tautologicalSection_eq_zero
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] :
    sectionPullbackAlong (AlgebraicGeometry.Scheme.zeroSection V)
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (AlgebraicGeometry.Scheme.totalSpace V)
        (CategoryTheory.CategoryStruct.id _)) = 0 := by
  let σ := AlgebraicGeometry.Scheme.zeroSection V
  let T := AlgebraicGeometry.Scheme.totalSpace V
  have hn := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality V T σ (𝟙 T)
  have hz := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_eq_zero_of_factors_zeroSection V
    (CategoryTheory.Over.mk (σ ≫ T.hom))
    ((CategoryTheory.Over.homMk σ rfl : CategoryTheory.Over.mk (σ ≫ T.hom) ⟶ T) ≫ 𝟙 T)
    (by
      change σ ≫ 𝟙 _ = (σ ≫ T.hom) ≫ σ
      rw [AlgebraicGeometry.Scheme.zeroSection_comp, Category.comp_id, Category.id_comp])
  rw [hz] at hn
  have hinv := congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom
      (sectionPullbackAlong σ (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T (𝟙 T))))
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp σ T.hom).hom_inv_id_app V)
  have h0 : (((AlgebraicGeometry.Scheme.Modules.pullbackComp σ T.hom).inv.app V).val.app
      (Opposite.op ⊤)).hom
      ((((AlgebraicGeometry.Scheme.Modules.pullbackComp σ T.hom).hom.app V).val.app
        (Opposite.op ⊤)).hom (sectionPullbackAlong σ (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T (𝟙 T))))
      = sectionPullbackAlong σ (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T (𝟙 T)) := hinv
  rw [← h0, ← hn]
  exact map_zero _

/-- The homogeneous evaluation of a homogeneous polynomial of positive degree at the zero tuple is zero:
`F(0, …, 0) = 0` (`e ≥ 1`).
Proof: `0 = 0 • 0`, and homogeneity (`evalHomogeneousAtSections_smul_pow`) gives `F(0 • f) = 0^e • F(f)`,
where `0^e = 0` for `e ≥ 1`. -/
theorem evalHomogeneousAtSections_zero_of_pos {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : X.Modules) [A.IsLineBundle]
    {N e : ℕ} (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous e) (he : 0 < e) :
    evalHomogeneousAtSections A F hF (fun _ => (0 : (A.val.obj (Opposite.op ⊤) : Type u))) = 0 := by
  have h := evalHomogeneousAtSections_smul_pow A F hF (0 : Γ(X, ⊤))
    (fun _ => (0 : (A.val.obj (Opposite.op ⊤) : Type u)))
  have h0 : (fun i : Fin (N + 1) => (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from (0 : Γ(X, ⊤))) •
      (fun _ => (0 : (A.val.obj (Opposite.op ⊤) : Type u))) i) =
      fun _ => (0 : (A.val.obj (Opposite.op ⊤) : Type u)) := by
    funext i
    exact zero_smul _ _
  have hpow : ((0 : Γ(X, ⊤)) ^ e) = 0 := zero_pow he.ne'
  rw [h0, hpow] at h
  exact h.trans (zero_smul _ _)

/-- The homogeneous equation section `F(τ)` pulls back to zero along the zero section (`e ≥ 1`).
Proof: by definition `homogeneousEquationSection A N F hF = evalHomogeneousAtSections (π^*A) F hF τ`
with `τ_i = π^*(pr_i)(τ)`. `evalHomogeneousAtSections_pullback` (`σ_0` is a `k`-morphism:
`σ_0 ≫ π ≫ s = s`) identifies `σ_0^*F(τ)` with `F(σ_0^*τ_i)` through the canonical isomorphism
`pullbackTensorPowIso`; `sectionPullbackAlong_naturality` and
`zeroSection_pullback_tautologicalSection_eq_zero` give `σ_0^*τ_i = σ_0^*π^*(pr_i)(σ_0^*τ) = 0`;
`evalHomogeneousAtSections_zero_of_pos` gives `F(0) = 0`; an isomorphism reflects zero
(`iso_hom_app_top_eq_zero_iff`). -/
theorem sectionPullbackAlong_zeroSection_homogeneousEquationSection {k : Type u} [Field k]
    {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {e : ℕ} (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous e) (he : 0 < e) :
    sectionPullbackAlong (AlgebraicGeometry.Scheme.zeroSection (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)))
      (homogeneousEquationSection A N F hF) = 0 := by
  let _ : (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).left.Over
      (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom ≫
      (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have _ : (AlgebraicGeometry.Scheme.zeroSection (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).IsOver
      (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨by
      change AlgebraicGeometry.Scheme.zeroSection (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) ≫
        ((AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom ≫
          (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) = C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
      rw [← Category.assoc, AlgebraicGeometry.Scheme.zeroSection_comp, Category.id_comp]⟩
  -- the coordinates of the tautological section
  let τ : Fin (N + 1) → (((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom).obj A).val.obj
        (Opposite.op ⊤) : Type u) := fun i =>
    ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom).map
          (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
        (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)))
        (CategoryTheory.CategoryStruct.id _))
  have hdef : homogeneousEquationSection A N F hF =
      evalHomogeneousAtSections ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom).obj A)
        F hF τ := rfl
  have hτ : ∀ i, sectionPullbackAlong
      (AlgebraicGeometry.Scheme.zeroSection (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))) (τ i) = 0 := by
    intro i
    have hnat := sectionPullbackAlong_naturality
      (AlgebraicGeometry.Scheme.zeroSection (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)))
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom).map
          (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i))
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
        (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)))
        (CategoryTheory.CategoryStruct.id _))
    have h1 := congrArg (fun x => (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.zeroSection (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)))).map
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom).map
            (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i))).val.app (Opposite.op ⊤)).hom x)
      (AlgebraicGeometry.Scheme.zeroSection_pullback_tautologicalSection_eq_zero
        (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)))
    exact hnat.trans (h1.trans (map_zero _))
  have key := evalHomogeneousAtSections_pullback
    (AlgebraicGeometry.Scheme.zeroSection (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)))
    ((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom).obj A)
    F hF τ
  have hz : (fun i => sectionPullbackAlong
      (AlgebraicGeometry.Scheme.zeroSection (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))) (τ i)) =
      fun _ => 0 := funext hτ
  rw [hz, evalHomogeneousAtSections_zero_of_pos _ F hF he] at key
  rw [hdef]
  exact (AlgebraicGeometry.Scheme.Modules.iso_hom_app_top_eq_zero_iff _ _).mp key

theorem zeroSection_mem_twistedAffineCone {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (hdeg : ∀ j, 0 < deg j)
    (F : ι → MvPolynomial (Fin (N + 1)) k) (hF : ∀ j, (F j).IsHomogeneous (deg j)) :
    ∃ σ : C ⟶ (twistedAffineCone A N deg F hF).left,
      σ ≫ (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
        (homogeneousEquationSection A N (F j) (hF j))).subschemeι =
      AlgebraicGeometry.Scheme.zeroSection (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) := by
  have hker : (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
        (homogeneousEquationSection A N (F j) (hF j))).subschemeι.ker ≤
      (AlgebraicGeometry.Scheme.zeroSection (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).ker := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]
    refine iSup_le fun j => ?_
    rw [AlgebraicGeometry.Scheme.idealSheafOfSection_le_ker_iff]
    exact sectionPullbackAlong_zeroSection_homogeneousEquationSection A N (F j) (hF j) (hdeg j)
  refine ⟨(AlgebraicGeometry.IsClosedImmersion.lift
    (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
      (homogeneousEquationSection A N (F j) (hF j))).subschemeι
    (AlgebraicGeometry.Scheme.zeroSection (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))) hker :
      C ⟶ (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
        (homogeneousEquationSection A N (F j) (hF j))).subscheme), ?_⟩
  exact AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ hker

end
