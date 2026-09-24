import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.BiproductSections
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecStructureIso
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhood
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodZeroSectionSurjective
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodSectionEqZeroOfPreimageEqZero_LineBundleRestrictInjective

/-! # The structure sheaf of the jet neighbourhood is torsion-free

**The structure sheaf of the jet neighbourhood `C̃_(κ)(L) = Spec_C̃(⊕_{q≤κ} L^{-q})` is torsion-free**: for
opens `W₁ ≤ W₂` of `C̃_(κ)(L)` with `W₁ ≠ ∅`, the restriction `Γ(W₂, O) → Γ(W₁, O)` is injective. Also:
`C̃_(κ)(L)` is irreducible (its underlying space is homeomorphic to `C̃` via the zero section).

Source: proof of Lemma 4.1 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Sections of the truncated jet algebra vanishing on a nonempty open vanish.** `𝒜 = ⊕_{q≤κ} piece_q` with
each `piece_q` a line bundle on the integral curve `C̃`; a section over `V₂` is determined by its components
`π_q` (`biproduct_sections_bijective`), each of which restricts to `0` on `V₁` (naturality of `π_q`) and hence
is `0` (`IsLineBundle.eq_zero_of_map_eq_zero_of_isIntegral`). -/
theorem truncatedJetAlgebra.carrier_eq_zero_of_map_eq_zero {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ)
    {V₁ V₂ : Ct.toScheme.Opens} (hV : V₁ ≤ V₂) (hV₁ : (V₁ : Set Ct.toScheme).Nonempty)
    (a : Γ((truncatedJetAlgebra L κ).carrier, V₂))
    (ha : (truncatedJetAlgebra L κ).carrier.presheaf.map (homOfLE hV).op a = 0) : a = 0 := by
  let P : Fin (κ + 1) → Ct.toScheme.Modules := fun q => truncatedJetAlgebra.piece L q
  change Γ(⨁ P, V₂) at a
  have ha' : (⨁ P).presheaf.map (homOfLE hV).op a = 0 := ha
  apply (AlgebraicGeometry.Scheme.Modules.biproduct_sections_bijective P V₂).1
  funext q
  show (biproduct.π P q).app V₂ a = (biproduct.π P q).app V₂ 0
  rw [map_zero]
  refine AlgebraicGeometry.Scheme.Modules.IsLineBundle.eq_zero_of_map_eq_zero_of_isIntegral (P q) hV hV₁ _ ?_
  have hn := PresheafOfModules.naturality_apply (biproduct.π P q).val (homOfLE hV).op a
  change (biproduct.π P q).app V₁ ((⨁ P).presheaf.map (homOfLE hV).op a) =
    (P q).presheaf.map (homOfLE hV).op ((biproduct.π P q).app V₂ a) at hn
  rw [← hn, ha', map_zero]

namespace jetNeighborhood

variable {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ)

/-- `p ∘ σ = id` on points. -/
theorem proj_base_zeroSection_base (x : Ct.toScheme) :
    (jetNeighborhood.proj L κ).base ((jetNeighborhood.zeroSection L κ).base x) = x :=
  congrArg (fun f => f.base x) (jetNeighborhood.zeroSection_proj L κ)

/-- `σ ∘ p = id` on points (`σ` is surjective and `p ∘ σ = id`). -/
theorem zeroSection_base_proj_base (y : (jetNeighborhood L κ).left) :
    (jetNeighborhood.zeroSection L κ).base ((jetNeighborhood.proj L κ).base y) = y := by
  obtain ⟨x, rfl⟩ := jetNeighborhood.zeroSection_base_surjective L κ y
  rw [proj_base_zeroSection_base]

/-- Every open of the jet neighbourhood is the preimage of an open of the curve: `W = p⁻¹(σ⁻¹ W)`. -/
theorem proj_preimage_zeroSection_preimage (W : (jetNeighborhood L κ).left.Opens) :
    jetNeighborhood.proj L κ ⁻¹ᵁ (jetNeighborhood.zeroSection L κ ⁻¹ᵁ W) = W := by
  ext y
  change (jetNeighborhood.zeroSection L κ).base ((jetNeighborhood.proj L κ).base y) ∈ W ↔ y ∈ W
  rw [zeroSection_base_proj_base]

/-- The jet neighbourhood is irreducible: the zero section is a continuous surjection from the irreducible
space `C̃`. (A theorem, not an instance; use `haveI`.) -/
theorem irreducibleSpace : IrreducibleSpace (jetNeighborhood L κ).left :=
  haveI : AlgebraicGeometry.IsIntegral Ct.toScheme := SmoothProjectiveCurve.isIntegral Ct
  Function.Surjective.irreducibleSpace (jetNeighborhood.zeroSection L κ).continuous
    (jetNeighborhood.zeroSection_base_surjective L κ)

/-- **Torsion-freeness of `O_{C̃_(κ)(L)}`.** For opens `W₁ ≤ W₂` with `W₁ ≠ ∅`, a function on `W₂` vanishing
on `W₁` is zero.

**Proof.** Write `W_i = p⁻¹V_i` (`proj_preimage_zeroSection_preimage`, `V_i := σ⁻¹W_i`); `V₁ ≤ V₂` and
`V₁ ≠ ∅` since `p` is surjective. `structureIso : 𝒜 ≅ p_*O` identifies `Γ(p⁻¹V, O)` with `Γ(V, 𝒜)`
compatibly with restriction (naturality), so `a := structureIso⁻¹(g) ∈ Γ(V₂, 𝒜)` restricts to `0` on `V₁`,
hence `a = 0` (`truncatedJetAlgebra.carrier_eq_zero_of_map_eq_zero`) and `g = structureIso(a) = 0`. -/
theorem eq_zero_of_map_eq_zero {W₁ W₂ : (jetNeighborhood L κ).left.Opens} (h : W₁ ≤ W₂)
    (hW₁ : (W₁ : Set (jetNeighborhood L κ).left).Nonempty)
    (g : Γ((jetNeighborhood L κ).left, W₂))
    (hg : (jetNeighborhood L κ).left.presheaf.map (homOfLE h).op g = 0) : g = 0 := by
  obtain ⟨V₂, rfl⟩ : ∃ V, W₂ = jetNeighborhood.proj L κ ⁻¹ᵁ V :=
    ⟨_, (proj_preimage_zeroSection_preimage L κ W₂).symm⟩
  obtain ⟨V₁, rfl⟩ : ∃ V, W₁ = jetNeighborhood.proj L κ ⁻¹ᵁ V :=
    ⟨_, (proj_preimage_zeroSection_preimage L κ W₁).symm⟩
  have hV : V₁ ≤ V₂ := by
    intro x hx
    have hx' : (jetNeighborhood.zeroSection L κ).base x ∈ jetNeighborhood.proj L κ ⁻¹ᵁ V₁ := by
      change (jetNeighborhood.proj L κ).base ((jetNeighborhood.zeroSection L κ).base x) ∈ V₁
      rw [proj_base_zeroSection_base]; exact hx
    have := h hx'
    change (jetNeighborhood.proj L κ).base ((jetNeighborhood.zeroSection L κ).base x) ∈ V₂ at this
    rwa [proj_base_zeroSection_base] at this
  have hV₁ : (V₁ : Set Ct.toScheme).Nonempty := by
    obtain ⟨y, hy⟩ := hW₁
    exact ⟨(jetNeighborhood.proj L κ).base y, hy⟩
  let A := truncatedJetAlgebra L κ
  let e := AlgebraicGeometry.Scheme.relativeSpec.structureIso A
  -- `g` as a section of `p_*O` over `V₂`
  let g' : Γ((AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
      (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf), V₂) := g
  let a : Γ(A.carrier, V₂) := e.inv.app V₂ g'
  have ha : A.carrier.presheaf.map (homOfLE hV).op a = 0 := by
    have hn := PresheafOfModules.naturality_apply e.inv.val (homOfLE hV).op g'
    change e.inv.app V₁ (((AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
      (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf)).presheaf.map (homOfLE hV).op g') =
      A.carrier.presheaf.map (homOfLE hV).op a at hn
    rw [← hn]
    have hg' : ((AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
      (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf)).presheaf.map (homOfLE hV).op g' = 0 := hg
    rw [hg']
    exact map_zero _
  have ha0 : a = 0 := truncatedJetAlgebra.carrier_eq_zero_of_map_eq_zero L κ hV hV₁ a ha
  have hc : e.hom.app V₂ (e.inv.app V₂ g') = g' :=
    congrArg (fun ψ => (AlgebraicGeometry.Scheme.Modules.Hom.app ψ V₂) g') e.inv_hom_id
  change g' = 0
  rw [← hc]
  change e.hom.app V₂ a = 0
  rw [ha0, map_zero]

end jetNeighborhood

end
