import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialConstants
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialFrameLocalSections
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialRingEquivCoordinateAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialRingEquivCoordinateSectionsRing
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialRingEquivCoordinateDualFrame
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialRingEquivCoordinateFunctional
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.TautologicalSection
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceSectionsRingEquivMvPolynomialSymSectionsInjective

/-! # The frame coordinate on `Tot(L)` over an affine open with a frame

Over an affine open `V` of the curve on which `L` has a frame `ε`, the functions on `p⁻¹V ⊂ Tot(L)` form
the polynomial ring `Γ(V, O)[x]` on the frame coordinate `x = ξ/p^*ε`: there are `x ∈ Γ(Tot(L), p⁻¹V)` and
a trivialization `τ₀` of `p^*L` on `p⁻¹V` with `Polynomial.aeval x : Γ(V, O)[t] → Γ(p⁻¹V, O)` bijective and
`τ₀(ξ|_{p⁻¹V}) = x`.

Source: the paper, §3 (a frame of `L` on an affine open `V` identifies `Tot(L)|_V` with
`Spec O(V)[t]`, `ξ = t·ε`) and the proof of the polynomial realization theorem. This is the
"`ξ = t·ε`" content behind `totLine_sections_over_frame`, which only asserts
`Nonempty (… ≃ₐ[Γ(V, O)] Polynomial Γ(V, O))`.

`A(V)` is the symmetric algebra of `Γ(V, L^∨)` by
`symGradedAlgebra_sectionsRing_isSymmetricAlgebra_of_retraction`; the algebraic glue lives in the
sibling modules `…CoordinateAlgebra`, `…CoordinateSectionsRing`, `…CoordinateDualFrame`,
`…CoordinateFunctional`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Over an affine open with a frame, `Γ(p⁻¹V, O_Tot) = Γ(V, O)[ξ/ε]`.**

Setting: `L` a line bundle on the smooth projective curve `C` over `k`, `p : Tot(L) → C` (`Tot(L) = Spec_C S`,
`S := Sym(L^∨)`, `totalSpace = relativeSpec S.total`), `V ⊆ C` an affine open, `ε ∈ Γ(V, L)` a frame of `L`
on `V` (`Modules.IsFrame`: `r ↦ r·ε` is bijective `Γ(W, O) → Γ(W, L)` for every open `W ⊆ V`),
`ι : p⁻¹V ↪ Tot(L)`, `R := Γ(C, V)`, `A := Γ(Tot(L), p⁻¹V)` (an `R`-algebra through `p.app V`),
`ξ = tautologicalSection L ∈ Γ(Tot(L), p^*L)`.
Claim: there are `x ∈ A` and a trivialization `τ₀ : ι^*(p^*L) ≅ O_{p⁻¹V}` such that
`Polynomial.aeval x : R[t] → A` is bijective and `τ₀(ι^*ξ) = x|_{p⁻¹V}` (the right-hand side is `x` read as a
global function of the open subscheme `p⁻¹V`, `ι.appLE (p⁻¹V) ⊤ _`; the left-hand side is read through
`unitSectionAsFunction`, definitionally the identity).

Proof:
1. **The dual frame.** `t := ε^∨ ∈ Γ(V, L^∨)` (`IsFrame.dualSec`, `…CoordinateDualFrame`): the coordinate
   functional `x ↦ coord_ε(x)` pushed into `Modules.dual L`. It is a frame of `L^∨` on `V`
   (`IsFrame.dualSec_isFrame`) and `⟨t, ε⟩ = 1` under the evaluation `dualEv L : L^∨ ⊗ L → O`
   (`IsFrame.dualEv_dualSec_frame`).
2. **`A(V) := Γ(V, S)` is the polynomial ring on `ι₁(t)`.** `A(V)` is the symmetric algebra of the `R`-module
   `Γ(V, L^∨)` (`symGradedAlgebra_sectionsRing_isSymmetricAlgebra_of_retraction`), which is free on `t`
   (`IsFrame.basisUnit`), so `aeval (ι₁ t) : R[X] → A(V)` is bijective
   (`Polynomial.aeval_bijective_of_isSymmetricAlgebra`, `…CoordinateAlgebra`). The chart `p⁻¹V = Spec A(V)`
   gives the `R`-algebra isomorphism `A(V) ≅ A` (`relativeSpec.sectionsAlgEquiv`, `…CoordinateSectionsRing`),
   which is the structure map `σ : S → p_*O_Tot` on sections (`sectionsAlgEquiv_apply_eq_structureHom_app`);
   so `x := σ(ι₁ t) ∈ A` has `aeval x` bijective (`Polynomial.aeval_bijective_of_algEquiv`).
3. **`ξ|_{p⁻¹V} = x · p^*ε`.** `p^*ε := η(ε) ∈ Γ(p⁻¹V, p^*L)` is a frame (`isFrame_unitSec_pullback`), so
   `ξ|_{p⁻¹V} = c · p^*ε` with `c` its coordinate. The functional `ψ_ξ : p^*(L^∨) → O_Tot` of `ξ`
   (`functionalOfSection`) is the transpose of the degree-one part of `σ` (`functionalOfSection_totalSpaceHomEquiv_id`,
   `…CoordinateFunctional`), so `ψ_ξ(η(t)) = σ(ι₁ t) = x` (`homEquiv_symm_app_unit`); on the other hand
   `ψ_ξ(η(t)) = ⟨η(t), c · η(ε)⟩ = c · p^♯⟨t, ε⟩ = c` (`functionalOfSection_app_unit_of_res_eq_smul`). Hence `c = x`.
4. **The trivialization.** `τ₀` is the trivialization by the global frame `ι^*(p^*ε)` of `ι^*(p^*L)`
   (`isFrame_pullbackTopSection`, `IsFrame.topTrivialization`), which reads off the coordinate
   (`IsFrame.topTrivialization_inv_app_smul`); `ι^*ξ = ι^*(ξ|_{p⁻¹V}) = ι^♯(c) · ι^*(p^*ε)`
   (`pullbackTopSection_res_top`, `pullbackTopSection_smul`), so `τ₀(ι^*ξ) = ι^♯(c) = ι^♯(x)`. ∎

Edge cases: `V = ∅` (then `R = A = 0` and `aeval x : 0[t] → 0` is bijective; the argument goes through
unchanged); `ε` may be any frame (the coordinate depends on it; the parent reconciles different choices by a
unit). Nothing here uses `IsAlgClosed k` or closed points. -/
theorem totalSpace_exists_coordinate_of_isFrame {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) (V : C.toScheme.Opens) (hV : AlgebraicGeometry.IsAffineOpen V)
    (ε : Γ(L.toModules, V)) (hε : AlgebraicGeometry.Scheme.Modules.IsFrame L.toModules V ε) :
    letI : Algebra Γ(C.toScheme, V)
        Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) :=
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.app V).hom.toAlgebra
    ∃ (x : Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V))
      (τ₀ : (AlgebraicGeometry.Scheme.Modules.pullback
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V).ι).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback
              (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj L.toModules) ≅
          SheafOfModules.unit
            ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V).toScheme.ringCatSheaf),
      Function.Bijective (Polynomial.aeval x : Polynomial Γ(C.toScheme, V) →ₐ[Γ(C.toScheme, V)]
        Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)) ∧
      AlgebraicGeometry.Scheme.Modules.unitSectionAsFunction (τ₀.hom.app ⊤ (sectionPullbackAlong
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V).ι (tautologicalSection L))) =
        (((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V).ι.appLE
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) ⊤
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V).ι_preimage_self.ge).hom x := by
  let _ : Algebra Γ(C.toScheme, V)
      Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) :=
    ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.app V).hom.toAlgebra
  -- notation: `Lb`, `D = L^∨`, `S = Sym(L^∨)`, `Tot`, `p`, `W = p⁻¹V`, `ι`
  let Lb := L.toModules
  let D := AlgebraicGeometry.Scheme.Modules.dual Lb
  let S := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra D
  let Tot := AlgebraicGeometry.Scheme.totalSpace Lb
  let p := Tot.hom
  let W := p ⁻¹ᵁ V
  let ι := W.ι
  -- step 1: the dual frame `t = ε^∨`
  let t : Γ(D, V) := hε.dualSec
  have ht : AlgebraicGeometry.Scheme.Modules.IsFrame D V t := hε.dualSec_isFrame
  have hte := hε.dualEv_dualSec_frame
  -- the coordinate `x = σ(ι₁ t) ∈ Γ(Tot, p⁻¹V)`
  let φ₁ : D ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward p).obj
      (SheafOfModules.unit Tot.left.ringCatSheaf) :=
    AlgebraicGeometry.Scheme.Modules.symGen D ≫ CategoryTheory.Limits.Sigma.ι S.part 1 ≫
      AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap S.total Tot (CategoryTheory.CategoryStruct.id _)
  let x : Γ(Tot.left, W) := φ₁.app V t
  -- step 2: `aeval x` is bijective
  have hx : Function.Bijective (Polynomial.aeval x : Polynomial Γ(C.toScheme, V) →ₐ[Γ(C.toScheme, V)]
      Γ(Tot.left, W)) := by
    let _ := (S.total.sectionsUnit V).toAlgebra
    let _ : Algebra Γ(C.toScheme, V)
        Γ((AlgebraicGeometry.Scheme.relativeSpec S.total).left,
          (AlgebraicGeometry.Scheme.relativeSpec S.total).hom ⁻¹ᵁ V) :=
      ((AlgebraicGeometry.Scheme.relativeSpec S.total).hom.app V).hom.toAlgebra
    have : D.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.dual_isQuasicoherent_of_locallyFree Lb
    have hS := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_sectionsRing_isSymmetricAlgebra_of_retraction
      D ⟨V, hV⟩
    have h1 := Polynomial.aeval_bijective_of_isSymmetricAlgebra hS ht.basisUnit
    rw [AlgebraicGeometry.Scheme.Modules.IsFrame.basisUnit_apply] at h1
    have h2 := Polynomial.aeval_bijective_of_algEquiv
      (AlgebraicGeometry.Scheme.relativeSpec.sectionsAlgEquiv S.total ⟨V, hV⟩) h1
    have h3 : AlgebraicGeometry.Scheme.relativeSpec.sectionsAlgEquiv S.total ⟨V, hV⟩
        (AlgebraicGeometry.Scheme.Modules.symGenTotalLinearMap D V t) = x := by
      rw [AlgebraicGeometry.Scheme.relativeSpec.sectionsAlgEquiv_apply_eq_structureHom_app]
      rfl
    rw [h3] at h2
    exact h2
  -- step 3: `ξ|_{p⁻¹V} = c • p^*ε` and `c = x`
  let ξ := tautologicalSection L
  let ε' : Γ((AlgebraicGeometry.Scheme.Modules.pullback p).obj Lb, W) :=
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction p).unit.app Lb).app V ε
  have hε' : AlgebraicGeometry.Scheme.Modules.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback p).obj Lb) W ε' :=
    MiyaokaMori.DualPullback.isFrame_unitSec_pullback p Lb hε
  let c : Γ(Tot.left, W) := hε'.coord le_rfl
    (((AlgebraicGeometry.Scheme.Modules.pullback p).obj Lb).res le_top ξ)
  have hc : ((AlgebraicGeometry.Scheme.Modules.pullback p).obj Lb).res le_top ξ = c • ε' := by
    have h := hε'.coord_smul_frame le_rfl (((AlgebraicGeometry.Scheme.Modules.pullback p).obj Lb).res le_top ξ)
    rw [AlgebraicGeometry.Scheme.Modules.res_self] at h
    exact h.symm
  have hcx : c = x := by
    have h1 := AlgebraicGeometry.Scheme.totalSpace.functionalOfSection_app_unit_of_res_eq_smul Lb Tot ξ V t ε
      hte c hc
    have h2 := AlgebraicGeometry.Scheme.totalSpace.functionalOfSection_totalSpaceHomEquiv_id Lb
    change AlgebraicGeometry.Scheme.totalSpace.functionalOfSection Lb Tot ξ = _ at h2
    rw [h2] at h1
    exact h1.symm.trans (AlgebraicGeometry.Scheme.Modules.homEquiv_symm_app_unit p φ₁ V t)
  -- step 4: the trivialization by the global frame `ι^*(p^*ε)` of `ι^*(p^*L)`
  have hW : (⊤ : W.toScheme.Opens) ≤ ι ⁻¹ᵁ W := W.ι_preimage_self.ge
  have hε'' := AlgebraicGeometry.Scheme.Modules.isFrame_pullbackTopSection ι
    ((AlgebraicGeometry.Scheme.Modules.pullback p).obj Lb) hW hε'
  refine ⟨x, hε''.topTrivialization.symm, hx, ?_⟩
  have hs : sectionPullbackAlong ι ξ =
      (ι.appLE W ⊤ hW) c • AlgebraicGeometry.Scheme.Modules.pullbackTopSection ι
        ((AlgebraicGeometry.Scheme.Modules.pullback p).obj Lb) hW ε' := by
    rw [← AlgebraicGeometry.Scheme.Modules.pullbackTopSection_res_top ι
      ((AlgebraicGeometry.Scheme.Modules.pullback p).obj Lb) hW ξ, hc,
      AlgebraicGeometry.Scheme.Modules.pullbackTopSection_smul]
  have h4 := hε''.topTrivialization_inv_app_smul ((ι.appLE W ⊤ hW) c)
  exact (congrArg (fun z => AlgebraicGeometry.Scheme.Modules.unitSectionAsFunction
    (AlgebraicGeometry.Scheme.Modules.Hom.app hε''.topTrivialization.inv ⊤ z)) hs).trans
    (h4.trans (congrArg (fun y => (ι.appLE W ⊤ hW).hom y) hcx))

end
