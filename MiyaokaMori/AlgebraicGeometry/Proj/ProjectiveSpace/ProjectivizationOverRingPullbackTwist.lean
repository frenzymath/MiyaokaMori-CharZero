import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectivizationOverRing
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesGlueIsoOfFrames

/-! # Pullback of `O(1)` along the projectivization morphism over a ring

`φ^*O(1) ≅ M` for the projectivization morphism `φ = projectivizationMorphismOver f M P hP : V → P^N_R`
over a commutative ring `R`, with `φ^*T_j ↦ P_j` (Hartshorne II.7.1 over `R`; Stacks 01VU).

Chart by chart: on `V_ℓ`, `φ` factors through `g_ℓ : V_ℓ → D_+(T_ℓ)` (`projectivizationChartMapOver_comp_ι`);
`T_ℓ` is a frame of `O(1)|_{D_+(T_ℓ)}` (`ProjectiveSpaceOverChart.targetFrameIso`), so `φ^*T_ℓ` is a frame
of `φ^*O(1)|_{V_ℓ}` (the generic `pullbackFrameIso`), with coordinates
`φ^*T_j ↦ g_ℓ^♯(T_j/T_ℓ) = r_{ℓ,j}` (`projectivizationChartMapOver_appTop_ratioSection`); `P_ℓ` is a frame
of `M|_{V_ℓ}` (`projectivizationChart_isFrame`), and `θ_ℓ := (P_ℓ)⁻¹ ∘ (φ^*T_ℓ)` sends `φ^*T_j` to
`r_{ℓ,j} • P_ℓ = P_j`. The `θ_ℓ` glue along `{V_ℓ}` (`exists_iso_of_local_frames_ulift`,
`Paper/S3PositiveLine/ModulesGlueIsoOfFrames.lean`).

This is the ring version of `projectivizationMorphism_pullback_twist` (field `k`,
`Paper/S3PositiveLine/Realization/ProjectivizationOfNowhereZeroTuple.lean`); all the frame lemmas used
are base-free. For performance, `O(1)` is spelled `ProjTwisting.sheaf 𝒜 ((1 : ℕ) : ℤ)` inside and
converted to `projectiveSpaceOverTwist R N 1` only in the final `exact`.

References: Hartshorne II.7.1; Stacks 01VU.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open MiyaokaMori.WeightedJets AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {V : AlgebraicGeometry.Scheme.{u}}
  (f : V ⟶ AlgebraicGeometry.Spec (CommRingCat.of R))
  (M : V.Modules) [M.IsLineBundle] {N : ℕ}
  (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
  (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v)

/-- `φ^*O(1)|_{V_ℓ} ≅ O_{V_ℓ}`, by pulling back the target frame `T_ℓ` along `g_ℓ`. -/
noncomputable def projectivizationPullbackFrameIsoOver (ℓ : Fin (N + 1)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback (projectivizationMorphismOver f M P hP)).obj
        (ProjTwisting.sheaf (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          ((1 : ℕ) : ℤ))).restrict (projectivizationChart P ℓ).ι ≅
      SheafOfModules.unit (R := (projectivizationChart P ℓ).toScheme.ringCatSheaf) :=
  pullbackFrameIso (projectivizationMorphismOver f M P hP)
    (projectivizationChart P ℓ)
    (AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X ℓ))
    (projectivizationChartMapOver f P ℓ) (projectivizationChartMapOver_comp_ι f M P hP ℓ)
    (ProjTwisting.sheaf (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) ((1 : ℕ) : ℤ))
    (ProjectiveSpaceOverChart.targetFrameIso (R := R) N ℓ)

/-- The pulled-back frame on `φ^*T_j|_{V_ℓ}`: `g_ℓ^♯(target frame (T_j))`. -/
theorem projectivizationPullbackFrameIsoOver_section (ℓ j : Fin (N + 1)) :
    (projectivizationPullbackFrameIsoOver f M P hP ℓ).hom.app ⊤
        (restrictedGlobalSection
          ((AlgebraicGeometry.Scheme.Modules.pullback (projectivizationMorphismOver f M P hP)).obj
            (ProjTwisting.sheaf (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) ((1 : ℕ) : ℤ)))
          (projectivizationChart P ℓ)
          (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (projectivizationMorphismOver f M P hP)
            (ProjTwisting.homogeneousSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) 1
              (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j) ⊤))) =
      (projectivizationChartMapOver f P ℓ).appTop
        ((ProjectiveSpaceOverChart.targetFrameIso (R := R) N ℓ).hom.app ⊤
          (restrictedGlobalSection
            (ProjTwisting.sheaf (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) ((1 : ℕ) : ℤ))
            (AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
              (MvPolynomial.X ℓ))
            (ProjTwisting.homogeneousSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) 1
              (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j) ⊤))) :=
  pullbackFrameIso_section_of_eq
    (projectivizationMorphismOver f M P hP) (projectivizationChart P ℓ)
    (AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X ℓ))
    (projectivizationChartMapOver f P ℓ) (projectivizationChartMapOver_comp_ι f M P hP ℓ)
    (ProjTwisting.sheaf (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) ((1 : ℕ) : ℤ))
    rfl (ProjectiveSpaceOverChart.targetFrameIso (R := R) N ℓ)
    (projectivizationPullbackFrameIsoOver f M P hP ℓ) rfl
    (ProjTwisting.homogeneousSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) 1
      (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j) ⊤) _ rfl

/-- **Coordinate formula of the pulled-back frame**: `φ^*T_j|_{V_ℓ} ↦ r_{ℓ,j}`. -/
theorem projectivizationPullbackFrameIsoOver_coordinate (ℓ j : Fin (N + 1)) :
    (projectivizationPullbackFrameIsoOver f M P hP ℓ).hom.app ⊤
        (restrictedGlobalSection
          ((AlgebraicGeometry.Scheme.Modules.pullback (projectivizationMorphismOver f M P hP)).obj
            (ProjTwisting.sheaf (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) ((1 : ℕ) : ℤ)))
          (projectivizationChart P ℓ)
          (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (projectivizationMorphismOver f M P hP)
            (ProjTwisting.homogeneousSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) 1
              (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j) ⊤))) =
      (projectivizationChart P ℓ).topIso.inv.hom (projectivizationRatio P ℓ j) := by
  rw [projectivizationPullbackFrameIsoOver_section,
    ProjectiveSpaceOverChart.targetFrameIso_coordinate]
  exact projectivizationChartMapOver_appTop_ratioSection f P ℓ j

/-- `θ_ℓ : φ^*O(1)|_{V_ℓ} ≅ M|_{V_ℓ}`: the pulled-back frame followed by the inverse of the frame `P_ℓ`. -/
noncomputable def projectivizationTwistIsoOnOver (ℓ : Fin (N + 1)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback (projectivizationMorphismOver f M P hP)).obj
        (ProjTwisting.sheaf (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          ((1 : ℕ) : ℤ))).restrict (projectivizationChart P ℓ).ι ≅
      M.restrict (projectivizationChart P ℓ).ι :=
  projectivizationPullbackFrameIsoOver f M P hP ℓ ≪≫
    (projectivizationChart_isFrame P ℓ).restrictIso.symm

/-- **`θ_ℓ(φ^*T_j) = P_j`** (`r_{ℓ,j} • P_ℓ = P_j`). -/
theorem projectivizationTwistIsoOnOver_coordinate (ℓ j : Fin (N + 1)) :
    (projectivizationTwistIsoOnOver f M P hP ℓ).hom.app ⊤
        (restrictedGlobalSection
          ((AlgebraicGeometry.Scheme.Modules.pullback (projectivizationMorphismOver f M P hP)).obj
            (ProjTwisting.sheaf (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) ((1 : ℕ) : ℤ)))
          (projectivizationChart P ℓ)
          (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (projectivizationMorphismOver f M P hP)
            (ProjTwisting.homogeneousSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) 1
              (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j) ⊤))) =
      restrictedGlobalSection M (projectivizationChart P ℓ) (P j) :=
  AlgebraicGeometry.Scheme.Modules.twistIsoOn_coordinate
    (projectivizationPullbackFrameIsoOver f M P hP ℓ) (projectivizationChart_isFrame P ℓ) _ _ _
    (projectivizationPullbackFrameIsoOver_coordinate f M P hP ℓ j)
    (by have h := projectivizationRatio_smul P ℓ j
        rwa [AlgebraicGeometry.Scheme.Modules.res_self] at h)

/-- **`φ^*T_ℓ` is a frame of `φ^*O(1)` on `V_ℓ`** (the pulled-back frame sends it to `r_{ℓ,ℓ} = 1`). -/
theorem isFrame_projectivizationOver_pullback_coordinate (ℓ : Fin (N + 1)) :
    AlgebraicGeometry.Scheme.Modules.IsFrame
      ((AlgebraicGeometry.Scheme.Modules.pullback (projectivizationMorphismOver f M P hP)).obj
        (ProjTwisting.sheaf (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) ((1 : ℕ) : ℤ)))
      (projectivizationChart P ℓ)
      (((AlgebraicGeometry.Scheme.Modules.pullback (projectivizationMorphismOver f M P hP)).obj
        (ProjTwisting.sheaf (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) ((1 : ℕ) : ℤ))).res le_top
        (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (projectivizationMorphismOver f M P hP)
          (ProjTwisting.homogeneousSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) 1
            (MvPolynomial.X ℓ) (MvPolynomial.isHomogeneous_X R ℓ) ⊤))) :=
  AlgebraicGeometry.Scheme.Modules.IsFrame.of_restrictIso_eq_one'
    (projectivizationPullbackFrameIsoOver f M P hP ℓ) _
    (by have h := projectivizationPullbackFrameIsoOver_coordinate f M P hP ℓ ℓ
        rwa [projectivizationRatio_self, map_one] at h)

/-- **`φ^*O(1) ≅ M`, `φ^*T_ℓ ↦ P_ℓ`** (glued along `{V_ℓ}` from the frames). -/
theorem projectivizationMorphismOver_pullback_twist :
    ∃ θ : (AlgebraicGeometry.Scheme.Modules.pullback
        (projectivizationMorphismOver f M P hP)).obj (projectiveSpaceOverTwist R N 1) ≅ M,
      ∀ ℓ, θ.hom.app ⊤
          (sectionPullbackAlong (projectivizationMorphismOver f M P hP)
            (projectiveSpaceOverCoordinate R N ℓ)) = P ℓ := by
  have hcover : (⨆ i : ULift.{u} (Fin (N + 1)), projectivizationChart P i.down) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨i, hi⟩ := hP v
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨ULift.up i, hi⟩
  obtain ⟨e, he⟩ := AlgebraicGeometry.Scheme.Modules.exists_iso_of_local_frames_ulift
    (projectivizationChart P) hcover
    (fun i => projectivizationTwistIsoOnOver f M P hP i.down)
    (fun j => AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (projectivizationMorphismOver f M P hP)
      (ProjTwisting.homogeneousSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) 1
        (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j) ⊤))
    P
    (fun i => isFrame_projectivizationOver_pullback_coordinate f M P hP i)
    (fun i j => projectivizationTwistIsoOnOver_coordinate f M P hP i.down j)
  exact ⟨e, he⟩

end
