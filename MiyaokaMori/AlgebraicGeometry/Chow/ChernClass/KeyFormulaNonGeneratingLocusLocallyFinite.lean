import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.KeyFormulaGeneratingFamily
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupXLemmas
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Morphisms.FiniteCodimOnePointsOutsideOpen

/-! # Local finiteness of the Stacks index set of the key formula; corrected assembly of 0AYC

The key formula (Stacks 0AYC) is indexed by `J := {w | coheight w = 1 ∧ ¬ (s generates L at w ∧ t generates N at w)}`
(see `CycleIdentitySplit_GeneratingFamily.lean`). To feed it into `ratEquivZero` (Stacks 02RW, locally finite
families) one needs `J` to be a locally finite family of points: this is `locallyFinitePoints_nonGeneratingLocus`
below (proved: frame coordinates + `X.basicOpen` + `finite_coheight_one_not_mem` on an affine open). With it, the Chow-level key formula `keyFormula_ratEquivZero`
(`Stacks0ayc.lean`) is re-assembled here as `keyFormula_ratEquivZero_generating` **with the same statement**,
from the core `exists_keyFormula_principalFamily_generating_of_normalizationFinite`, whose index set is
the non-generating locus rather than the support.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

open Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

omit [IsLocallyNoetherian X] in
/-- A nonzero rational section generates on a nonempty open set (Stacks 01CY, germ version): if
`s = germ_η(s̃)` with `s̃` a section over `W₀ ∋ η`, and `e` is a frame of `L` on `W ≤ W₀` around `η`, write
`s̃|_W = f • e`; then on `X.basicOpen f` (which contains `η` because `f_η ≠ 0` in the field `K(X)`) the germ of
`s̃` is a unit multiple of the frame germ, hence a generator of the stalk, with generic image `s`. -/
theorem exists_opens_rationalSectionGeneratesAt (L : X.Modules) [L.IsLineBundle]
    (s : L.stalk (genericPoint X)) (hs : s ≠ 0) :
    ∃ U : X.Opens, genericPoint X ∈ U ∧ ∀ y ∈ U, L.RationalSectionGeneratesAt s y := by
  obtain ⟨W₀, hη₀, s₀, rfl⟩ := L.presheaf.exists_germ_eq s
  obtain ⟨W, hWW₀, hηW, e, hf⟩ := exists_frame_le L hη₀
  set f : Γ(X, W) := hf.coord le_rfl (L.res hWW₀ s₀) with hfdef
  have hse : L.res hWW₀ s₀ = f • e := by
    have h := hf.coord_smul_frame le_rfl (L.res hWW₀ s₀)
    rw [res_self] at h
    exact h.symm
  have key : ∀ (y : X) (hy : y ∈ W),
      L.presheaf.germ W₀ y (hWW₀ hy) s₀ = X.presheaf.germ W y hy f • L.presheaf.germ W y hy e := by
    intro y hy
    have h0 : L.presheaf.germ W y hy (L.res hWW₀ s₀) = L.presheaf.germ W₀ y (hWW₀ hy) s₀ :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [← h0, hse, germ_smul']
  refine ⟨X.basicOpen f, ?_, ?_⟩
  · rw [X.mem_basicOpen f _ hηW, isUnit_iff_ne_zero]
    intro h0
    apply hs
    rw [key _ hηW, h0, zero_smul]
    rfl
  · intro y hy
    have hyW : y ∈ W := X.basicOpen_le f hy
    have hu : IsUnit (X.presheaf.germ W y hyW f) := (X.mem_basicOpen f y hyW).mp hy
    refine ⟨L.presheaf.germ W₀ y (hWW₀ hyW) s₀, ?_, ?_⟩
    · rw [key y hyW, Submodule.span_singleton_smul_eq hu]
      exact hf.span_germ_eq_top hyW
    · exact AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber_germ X L y W₀ (hWW₀ hyW) s₀

/-- **The non-generating codimension-1 locus is locally finite (Stacks 0AYC, setup: "a locally finite set of
irreducible closed subsets of codimension 1 such that `s` and `t` are generators outside them").**

Statement: `X` integral, locally Noetherian; `L, N` line bundles; `s ∈ L_η`, `t ∈ N_η` nonzero. The family of
points `J := {w | coheight w = 1 ∧ ¬ (RationalSectionGeneratesAt L s w ∧ RationalSectionGeneratesAt N t w)}`
is locally finite: every `x ∈ X` has an open neighbourhood containing only finitely many `w ∈ J`.

Proof: `s` and `t` generate on nonempty opens `U_s, U_t ∋ η` (`exists_opens_rationalSectionGeneratesAt`). Given `x`,
take an affine open `V ∋ x`; `V` is an integral Noetherian scheme, `U := V ∩ U_s ∩ U_t` is a nonempty open of
`V` (it contains `η`), and the coheight-1 points of `V` outside `U` are finite
(`Scheme.finite_coheight_one_not_mem`, i.e. `AlgebraicGeometry.Divisors.finite_codimensionOneOutside`: they are generic points of
the finitely many irreducible components of `V ∖ U`). Coheight is invariant under the open immersion `V → X`
(Mathlib `coheight_eq_of_isOpenImmersion`), and every `w ∈ J ∩ V` lies outside `U` (points of `U` are
generating), so `J ∩ V` is contained in the image of that finite set. -/
theorem locallyFinitePoints_nonGeneratingLocus (L N : X.Modules) [L.IsLineBundle] [N.IsLineBundle]
    (s : L.stalk (genericPoint X)) (t : N.stalk (genericPoint X)) (hs : s ≠ 0) (ht : t ≠ 0) :
    LocallyFinitePoints (fun w : ↥{w : X | Order.coheight w = 1 ∧
      ¬ (L.RationalSectionGeneratesAt s w ∧ N.RationalSectionGeneratesAt t w)} => (w : X)) := by
  obtain ⟨Us, hηs, hUs⟩ := exists_opens_rationalSectionGeneratesAt L s hs
  obtain ⟨Ut, hηt, hUt⟩ := exists_opens_rationalSectionGeneratesAt N t ht
  intro x
  obtain ⟨_, ⟨V₀, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let V : X.Opens := V₀
  have hxV' : x ∈ V := hxV
  refine ⟨V, V.isOpen, hxV', ?_⟩
  haveI : Nonempty V := ⟨⟨x, hxV'⟩⟩
  haveI : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
  haveI : IsNoetherian V.toScheme := {}
  have hηV : genericPoint X ∈ V := (genericPoint_specializes x).mem_open V.isOpen hxV'
  let U : V.toScheme.Opens := V.ι ⁻¹ᵁ (Us ⊓ Ut)
  haveI : Nonempty U := ⟨⟨⟨genericPoint X, hηV⟩, ⟨hηs, hηt⟩⟩⟩
  have hfin := Scheme.finite_coheight_one_not_mem U
  refine ((hfin.image (fun z : V.toScheme => (V.ι z : X))).preimage Subtype.val_injective.injOn).subset ?_
  rintro ⟨w, hw⟩ hwV
  have hw' : Order.coheight w = 1 ∧
      ¬ (L.RationalSectionGeneratesAt s w ∧ N.RationalSectionGeneratesAt t w) := hw
  have hwV' : w ∈ V := hwV
  refine ⟨⟨w, hwV'⟩, ⟨?_, ?_⟩, rfl⟩
  · rw [← hw'.1]
    exact (coheight_eq_of_isOpenImmersion (x := (⟨w, hwV'⟩ : V)) V.ι).symm
  · intro hU
    exact hw'.2 ⟨hUs w hU.1, hUt w hU.2⟩

/-- **Key formula (Stacks 0AYC), Chow-group level — corrected assembly.** Same statement as
`keyFormula_ratEquivZero` (`Stacks0ayc.lean`); the proof uses the Stacks index set `J` (non-generating
codimension-1 locus) via `exists_keyFormula_principalFamily_generating_of_normalizationFinite`, the finite
normalization of stalks `keyFormula_module_finite_integralClosure_stalk` (Stacks 0335), and the local
finiteness of `J` (`locallyFinitePoints_nonGeneratingLocus`), assembled by the definition of `ratEquivZero`
(02RW, locally finite families) exactly as in `keyFormula_ratEquivZero`. -/
theorem keyFormula_ratEquivZero_generating
    (K : Type u) [Field K] (π : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType π]
    (L N : X.Modules) [L.IsLineBundle] [N.IsLineBundle] (n : ℕ) (hX : X.dimension = n + 2)
    (s : L.stalk (genericPoint X)) (t : N.stalk (genericPoint X)) (hs : s ≠ 0) (ht : t ≠ 0) :
    firstChernCapCycle ⟨K, inferInstance, π, inferInstance⟩ N (n + 1) (L.rationalSectionDivisor s)
      = firstChernCapCycle ⟨K, inferInstance, π, inferInstance⟩ L (n + 1) (N.rationalSectionDivisor t) := by
  obtain ⟨c, hgen, hsum⟩ := exists_keyFormula_principalFamily_generating_of_normalizationFinite K π L N n hX
    s t hs ht (fun x => keyFormula_module_finite_integralClosure_stalk K π x)
  have hXf : X.IsLocallyOfFiniteTypeOverField := ⟨K, inferInstance, π, inferInstance⟩
  show ChowGroup.mk ⟨firstChernCapCycleAux N (n + 1) (L.rationalSectionDivisor s),
        firstChernCapCycleAux_mem hXf N (n + 1) _⟩
    = ChowGroup.mk ⟨firstChernCapCycleAux L (n + 1) (N.rationalSectionDivisor t),
        firstChernCapCycleAux_mem hXf L (n + 1) _⟩
  rw [ChowGroup.mk_eq_mk_iff]
  refine ⟨firstChernCapCycleAux_mem hXf N (n + 1) _, firstChernCapCycleAux_mem hXf L (n + 1) _, ?_⟩
  exact ⟨↥{w : X | Order.coheight w = 1 ∧
      ¬ (L.RationalSectionGeneratesAt s w ∧ N.RationalSectionGeneratesAt t w)}, fun w => (w : X), c,
    fun _ => Set.mem_univ _, hgen, locallyFinitePoints_nonGeneratingLocus L N s t hs ht, hsum⟩

end AlgebraicGeometry

end
