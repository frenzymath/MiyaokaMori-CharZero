import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GeneratedInDegreeOneSections
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjProperOfCharts
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjToSpecProperOfGenerated
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01pbAffineOpen

/-! # Projective morphisms are proper

A projective morphism is proper (Stacks Project, Tag 01WC: a locally projective morphism is proper;
Hartshorne II.4.9). This is how the weighted jet spaces of §2 of the paper are seen to be proper.

Route. `f = i ≫ π` with `i` a closed immersion and `π : Proj_X S → X` the relative
Proj of a graded quasi-coherent algebra `S` generated in degree one with `S_1` of finite type.
Closed immersions are finite, hence proper (Mathlib), so it suffices that `π` is proper.
Properness is Zariski-local on the target and the chart square identifies `π⁻¹(U) → U` with
`projToOpen U : Proj S(U) → U` for affine `U` (Stacks 01NQ),
which is `Proj.toSpecZero S(U) ≫ Spec (Γ(U) → S(U)_0) ≫ (U ≅ Spec Γ(U))`.
On the affine `U`: `Γ(S_1, U)` is a finite `Γ(U)`-module (Stacks 01PB) and every
element of `S(U)` of positive degree is a polynomial in `S(U)_1` with coefficients in the image of
`Γ(U)`; so `Proj S(U)` is a closed subscheme of `P^N_{Γ(U)}`
and `Proj S(U) → Spec Γ(U)` is proper (this realises
Stacks 01WC's "closed in `P^n_S`, and `P^n_S` is proper" step; it does **not** need `Γ(U) → S(U)_0`
to be surjective, which the Lean definition `GeneratedInDegreeOne` (only `ℓ > 0`) does not give).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The chart `Proj S(U) → U` of the relative Proj is proper, for `S` generated in degree one with
`S_1` of finite type and `U` an affine open of the base. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.projToOpen_isProper {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (hS : S.GeneratedInDegreeOne) [(S.part 1).IsFiniteType]
    (U : X.AffineZariskiSite) :
    AlgebraicGeometry.IsProper (S.toGradedAffineAlgebra.projToOpen U) := by
  classical
  have : (S.part 1).IsQuasicoherent := S.quasicoherent 1
  -- `Γ(S_1, U)` is a finite `Γ(X, U)`-module: pick generators `t`
  have hfin : Module.Finite Γ(X, U.toOpens) Γ(S.part 1, U.toOpens) :=
    AlgebraicGeometry.Scheme.Modules.finite_sections_of_isFiniteType (S.part 1) U.2
  obtain ⟨t, ht⟩ := hfin.fg_top
  let s : Finset (S.sectionsRing U.toOpens) := t.image (S.ofPiece U.toOpens 1)
  have hs : ∀ x ∈ s, x ∈ S.sectionsGrading U.toOpens 1 := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨a, rfl⟩
  -- every element of positive degree is a polynomial in `s` with coefficients in `Γ(X, U)`
  have hgen : ∀ n, 0 < n → ∀ x ∈ S.sectionsGrading U.toOpens n,
      x ∈ Subring.closure (Set.range (S.sectionsUnitHom U.toOpens) ∪
        (↑s : Set (S.sectionsRing U.toOpens))) := by
    intro n hn x hx
    refine Subring.closure_le.mpr ?_ (hS.sectionsGrading_mem_closure U.2 hn hx)
    rintro y (⟨r, rfl⟩ | ⟨a, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨r, rfl⟩)
    · have ha : a ∈ Submodule.span Γ(X, U.toOpens) (↑t : Set Γ(S.part 1, U.toOpens)) := by
        rw [ht]; trivial
      change S.ofPiece U.toOpens 1 a ∈ _
      refine Submodule.span_induction
        (p := fun (a : Γ(S.part 1, U.toOpens)) _ => S.ofPiece U.toOpens 1 a ∈ Subring.closure
          (Set.range (S.sectionsUnitHom U.toOpens) ∪ (↑s : Set (S.sectionsRing U.toOpens))))
        ?_ ?_ ?_ ?_ ha
      · intro b hb
        exact Subring.subset_closure (Or.inr (Finset.mem_image.mpr ⟨b, hb, rfl⟩))
      · have h0 : S.ofPiece U.toOpens 1 (0 : Γ(S.part 1, U.toOpens)) = 0 :=
          map_zero (DirectSum.of (S.sectionsPiece U.toOpens) 1)
        rw [h0]
        exact zero_mem _
      · intro b c _ _ hb hc
        have hadd : S.ofPiece U.toOpens 1 (b + c) = S.ofPiece U.toOpens 1 b + S.ofPiece U.toOpens 1 c :=
          map_add (DirectSum.of (S.sectionsPiece U.toOpens) 1) b c
        exact hadd ▸ add_mem hb hc
      · intro r b _ hb
        exact (S.sectionsUnitHom_mul_ofPiece U.toOpens r b) ▸
          mul_mem (Subring.subset_closure (Or.inl ⟨r, rfl⟩)) hb
  -- the chart is `Proj S(U) → Spec S(U)_0 → Spec Γ(X, U) ≅ U`
  have key : AlgebraicGeometry.IsProper (AlgebraicGeometry.Proj.toSpecZero
      (S.toGradedAffineAlgebra.grading U) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (S.toGradedAffineAlgebra.unitZero U))) :=
    AlgebraicGeometry.Proj.isProper_toSpecZero_comp_of_generated
      (S.toGradedAffineAlgebra.grading U) (S.toGradedAffineAlgebra.unitZero U) s hs
      (fun n hn x hx => hgen n hn x hx)
  have hiso : AlgebraicGeometry.IsProper U.2.isoSpec.inv := by
    have : AlgebraicGeometry.IsClosedImmersion U.2.isoSpec.inv := inferInstance
    infer_instance
  show AlgebraicGeometry.IsProper (AlgebraicGeometry.Proj.toSpecZero _ ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (S.toGradedAffineAlgebra.unitZero U)) ≫
      U.2.isoSpec.inv)
  rw [← Category.assoc]
  infer_instance

theorem AlgebraicGeometry.IsProjectiveMorphism.isProper {Y X : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ X) [AlgebraicGeometry.IsProjectiveMorphism f] : AlgebraicGeometry.IsProper f := by
  obtain ⟨S, i, hgen, hfin, hi, hfi⟩ :=
    AlgebraicGeometry.IsProjectiveMorphism.exists_closed_immersion (f := f)
  have := hfin
  have := hi
  have : AlgebraicGeometry.IsProper (AlgebraicGeometry.Scheme.relativeProj S).hom :=
    S.toGradedAffineAlgebra.relativeProj_hom_isProper_of_projToOpen
      (fun U => S.projToOpen_isProper hgen U)
  rw [← hfi]
  infer_instance

end
