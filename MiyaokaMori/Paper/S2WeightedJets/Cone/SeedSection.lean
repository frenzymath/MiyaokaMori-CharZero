import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousAtSections
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousLocalFormula
import MiyaokaMori.AlgebraicGeometry.Modules.HomogeneousEquationAsSection
import MiyaokaMori.AlgebraicGeometry.Modules.HomogeneousEquationSectionAtTotalSpaceSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalProperty
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSectionEquationsVanish
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineCone
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.Stacks02or

/-! # The seed section

The seed section `s = (f_0, …, f_N) : C → 𝒵`: the `C`-section given by the homogeneous coordinate
sections of `f` (Definition 2.1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The tuple `f`, as the global section `Σ_i ι_i(f_i)` of `A^{⊕(N+1)}`, gives `σ : C → Tot(A^{⊕(N+1)})`
   through `totalSpaceSectionEquiv`; `Z = V(⨆ I_j)` is a closed subscheme and `σ` factors through `Z`
   (the kernel condition follows from `hvanish` via Stacks 02OR and `kerAdjunction`); the universal
   property of the closed immersion, `IsClosedImmersion.lift`, lifts it to `s : C → Z`, with
   `s ≫ Z.hom = σ ≫ π = 𝟙`. -/

/-- The section `σ_f : C → Tot(A^{⊕(N+1)})` given by the tuple `f` (together with `σ_f ≫ π = 𝟙`). -/

noncomputable def seedSection.totSection {C : AlgebraicGeometry.Scheme.{u}} (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u)) :
    { σ : C ⟶ (AlgebraicGeometry.Scheme.totalSpace
        (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).left //
      σ ≫ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom =
        CategoryTheory.CategoryStruct.id C } :=
  AlgebraicGeometry.Scheme.totalSpaceSectionEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
    (∑ i : Fin (N + 1),
      ((CategoryTheory.Limits.biproduct.ι (fun _ : Fin (N + 1) => A) i).val.app (Opposite.op ⊤)).hom (f i))

/-- `σ_f` factors through the cone `Z = V(⨆ I_j)`: the ideal sheaf of the cone is contained in `ker σ_f`.
Proof: `iSup_le`, and for each `j` the characterisation of `idealSheafOfSection` (Stacks 02OR: the
vanishing ideal of a section `t` is `≤ ker g` iff `g^* t = 0`, via `kerAdjunction`), while
`σ_f^*(equation section of F_j) = evalHomogeneousAtSections A (F j) (hF j) f`, which is zero by
`hvanish j`. -/
theorem seedSection.ideal_le_ker {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u))
    {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j))
    (hvanish : ∀ j, evalHomogeneousAtSections A (F j) (hF j) f = 0) :
    (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
        (homogeneousEquationSection (k := k) A N (F j) (hF j))) ≤
      AlgebraicGeometry.Scheme.Hom.ker (seedSection.totSection A N f).1 := by
  refine iSup_le (fun j => ?_)
  exact (homogeneousEquationSection_le_ker_totalSpaceSection_iff
    (k := k) A N (F j) (hF j) f).2 (hvanish j)

/-- The seed section `s = (f_0, …, f_N) : C → 𝒵` of the twisted affine cone, together with `s ≫ 𝒵.hom = 𝟙`. -/
noncomputable def seedSection {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u))
    {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j))
    (hvanish : ∀ j, evalHomogeneousAtSections A (F j) (hF j) f = 0) :
    { s : C ⟶ (twistedAffineCone A N deg F hF).left //
      s ≫ (twistedAffineCone A N deg F hF).hom = CategoryTheory.CategoryStruct.id C } :=
  let I : (AlgebraicGeometry.Scheme.totalSpace
      (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).left.IdealSheafData :=
    ⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _ (homogeneousEquationSection A N (F j) (hF j))
  let σ := seedSection.totSection A N f
  ⟨(AlgebraicGeometry.IsClosedImmersion.lift I.subschemeι σ.1 (by
      simp only [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]
      exact seedSection.ideal_le_ker A N f deg F hF hvanish) : C ⟶ I.subscheme), by
    simp only [twistedAffineCone, CategoryTheory.Over.mk_hom]
    rw [AlgebraicGeometry.IsClosedImmersion.lift_fac_assoc]
    exact σ.2⟩

end
