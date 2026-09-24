import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodSectionEqZeroOfPreimageEqZero_LineBundleRestrictInjective
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodSectionEqZeroOfPreimageEqZero_StructureSheafRestrictInjective

/-! # A section of a line bundle on the jet neighbourhood vanishing generically vanishes

A section of a line bundle on the jet neighbourhood `C̃_(κ)(L) = Spec_C̃(⊕_{q≤κ} L^{-q})` that vanishes over a
nonempty open subset of the curve vanishes identically ("vanishes generically, hence everywhere" on the
thickening of an integral curve).

Source: proof of Lemma 4.1 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Sections of a line bundle on the thickening are determined on a dense open.** Let `p : C̃_(κ)(L) → C̃`
be the jet neighbourhood of the smooth projective (hence integral) curve `C̃`, `N` a line bundle on `C̃_(κ)(L)`,
`U ⊆ C̃` a nonempty open and `t ∈ Γ(N)`. If `t` pulled back to the open subscheme `p⁻¹U` is `0`, then `t = 0`.

**Proof (formalized).**
1. The pullback of `t` along the open immersion `ι : p⁻¹U → C̃_(κ)(L)` is the presheaf restriction of `t` to
   `ι(⊤) = p⁻¹U`, up to the comparison isomorphisms (`AlgebraicGeometry.Scheme.Modules.ModuleSections.restrictIso_inv_pullback`); so
   the hypothesis says `t|_{p⁻¹U} = 0`.
2. `p⁻¹U ≠ ∅`: `U ≠ ∅` and the zero section `σ` satisfies `p ∘ σ = id`.
3. `C̃_(κ)(L)` is irreducible (`σ` is a continuous surjection from the irreducible `C̃`;
   `jetNeighborhood.irreducibleSpace`) and its structure sheaf is torsion-free: for opens `W₁ ≤ W₂` with
   `W₁ ≠ ∅`, `Γ(W₂, O) → Γ(W₁, O)` is injective (`jetNeighborhood.eq_zero_of_map_eq_zero`: every open is
   `p⁻¹V`, `Γ(p⁻¹V, O) ≅ Γ(V, 𝒜)` via `relativeSpec.structureIso`, naturally in `V`, and
   `𝒜 = ⊕_{q≤κ} L^{-q}` is a biproduct of line bundles on the integral curve, whose sections are determined
   on any nonempty open).
4. A line bundle on a preirreducible scheme with torsion-free structure sheaf is itself torsion-free
   (`IsLineBundle.eq_zero_of_map_eq_zero`: trivialise locally, transport the section to a function, apply 3,
   and conclude by the sheaf axiom). Applied to `W₁ = p⁻¹U ≤ W₂ = ⊤` this gives `t = 0`.
Edge cases: `U = ⊤` (trivial); `κ = 0` (then `p` is an isomorphism and the statement is the integral-curve
case). -/
theorem jetNeighborhood.section_eq_zero_of_sectionPullbackAlong_preimage_eq_zero {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ)
    (N : (jetNeighborhood L κ).left.Modules) [N.IsLineBundle]
    (U : Ct.toScheme.Opens) (hU : (U : Set Ct.toScheme).Nonempty)
    (t : (N.val.obj (Opposite.op ⊤) : Type u))
    (h : sectionPullbackAlong ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι t = 0) : t = 0 := by
  -- Step 1: the restriction of `t` to `ι(⊤) = p⁻¹U` vanishes
  have h1 := AlgebraicGeometry.Scheme.Modules.ModuleSections.restrictIso_inv_pullback ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι (M := N) t
  have h2 : N.presheaf.map (homOfLE (show ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι ''ᵁ
      (⊤ : ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme.Opens) ≤ ⊤ from le_top)).op t = 0 := by
    rw [← h1]
    have h0 : AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι t = 0 := h
    rw [h0, map_zero]
    exact map_zero _
  -- Step 2: `ι(⊤) = p⁻¹U` is nonempty
  have hne : ((((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι ''ᵁ
      (⊤ : ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme.Opens) : (jetNeighborhood L κ).left.Opens) :
        Set (jetNeighborhood L κ).left).Nonempty := by
    rw [AlgebraicGeometry.Scheme.Opens.ι_image_top]
    obtain ⟨x, hx⟩ := hU
    refine ⟨(jetNeighborhood.zeroSection L κ).base x, ?_⟩
    change (jetNeighborhood.proj L κ).base ((jetNeighborhood.zeroSection L κ).base x) ∈ U
    rw [jetNeighborhood.proj_base_zeroSection_base]
    exact hx
  -- Steps 3–4
  have : IrreducibleSpace (jetNeighborhood L κ).left := jetNeighborhood.irreducibleSpace L κ
  exact AlgebraicGeometry.Scheme.Modules.IsLineBundle.eq_zero_of_map_eq_zero
    (fun _ _ h' hne' g hg => jetNeighborhood.eq_zero_of_map_eq_zero L κ h' hne' g hg) N le_top hne t h2

end
