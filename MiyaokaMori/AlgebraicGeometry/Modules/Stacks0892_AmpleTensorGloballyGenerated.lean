import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.NonvanishingLocusTensorSection
import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowIsos
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowSectionLocus
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01q1

/-! # Ample tensor globally generated is ample

Stacks 0890 (`morphisms-lemma-ample-tensor-globally-generated`, in the form used here): if `K` is ample
and the global sections of `G` have no common zero (the globally generated line bundle case), then
`K ⊗ G` is ample. Pointwise version `exists_section_nonvanishingLocus_tensor_eq_inf`: `σ ∈ Γ(K^{⊗n})`
and `τ ∈ Γ(G)` give `ρ ∈ Γ((K ⊗ G)^{⊗n})` with `X_ρ = X_σ ⊓ X_τ`.

Reference: Stacks 0890; used in the third paragraph of the proof of Stacks 0892 (removing "sufficiently
divisible").

Proof:
1. `ρ := σ ⊗ τ^{⊗n}` transported to `(K ⊗ G)^{⊗n}` along the isomorphism
   `K^{⊗n} ⊗ G^{⊗n} ≅ (K ⊗ G)^{⊗n}` (`tensorPowTensorIso`); nonvanishing loci are invariant under
   isomorphisms (`nonvanishingLocus_iso`).
2. `X_{σ ⊗ τ^{⊗n}} = X_σ ⊓ X_{τ^{⊗n}}` (`nonvanishingLocus_sectionTensor`) and `X_{τ^{⊗n}} = X_τ`
   (`n ≥ 1`, `nonvanishingLocus_tensorPowSection`).
3. Ampleness: for `x`, take the `n, σ` given by ampleness of `K` (`x ∈ X_σ` affine) and `τ` not
   vanishing at `x`; then `x ∈ X_ρ = X_σ ⊓ X_τ`, and the intersection of an affine open with `X_τ` is
   affine (Stacks 01PV, `IsAffineOpen.inf_nonvanishingLocus`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **Pointwise 0890**: `σ ∈ Γ(K^{⊗n})`, `τ ∈ Γ(G)`, `n ≥ 1` ⇒ there is `ρ ∈ Γ((K ⊗ G)^{⊗n})` with
`X_ρ = X_σ ⊓ X_τ`. -/
theorem exists_section_nonvanishingLocus_tensor_eq_inf (K G : X.Modules) [K.IsLineBundle] [G.IsLineBundle]
    {n : ℕ} (hn : 0 < n) (σ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow K n, ⊤)) (τ : Γ(G, ⊤)) :
    ∃ ρ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensor K G) n, ⊤),
      (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensor K G) n).nonvanishingLocus ρ =
        (AlgebraicGeometry.Scheme.Modules.tensorPow K n).nonvanishingLocus σ ⊓ G.nonvanishingLocus τ := by
  refine ⟨(AlgebraicGeometry.Scheme.Modules.tensorPowTensorIso K G n).symm.hom.app ⊤
    (sectionTensor σ (AlgebraicGeometry.Scheme.Modules.tensorPowSection τ n)), ?_⟩
  have h1 := nonvanishingLocus_iso (AlgebraicGeometry.Scheme.Modules.tensorPowTensorIso K G n).symm
    (sectionTensor σ (AlgebraicGeometry.Scheme.Modules.tensorPowSection τ n))
  have h2 := nonvanishingLocus_sectionTensor (AlgebraicGeometry.Scheme.Modules.tensorPow K n)
    (AlgebraicGeometry.Scheme.Modules.tensorPow G n) σ (AlgebraicGeometry.Scheme.Modules.tensorPowSection τ n)
  have h3 := nonvanishingLocus_tensorPowSection G τ hn
  exact h1.trans (h2.trans (congrArg (fun W => (AlgebraicGeometry.Scheme.Modules.tensorPow K n).nonvanishingLocus σ ⊓ W) h3))

end AlgebraicGeometry.Scheme.Modules

/-- **Stacks 0890**: if `K` is ample and `G` has a non-vanishing global section at every point, then
`K ⊗ G` is ample. -/
theorem AlgebraicGeometry.IsAmple.tensor_of_forall_not_isZeroAt {X : AlgebraicGeometry.Scheme.{u}}
    (K G : X.Modules) [K.IsLineBundle] [G.IsLineBundle] (hK : AlgebraicGeometry.IsAmple K)
    (hG : ∀ x : X, ∃ τ : (G.val.obj (Opposite.op ⊤) : Type u), ¬ IsZeroAt τ x) :
    AlgebraicGeometry.IsAmple (AlgebraicGeometry.Scheme.Modules.tensor K G) := by
  obtain ⟨hcpt, hcov⟩ := hK
  refine ⟨hcpt, fun x => ?_⟩
  obtain ⟨n, hn, σ, hxσ, haff⟩ := hcov x
  obtain ⟨τ, hτ⟩ := hG x
  let τ' : Γ(G, ⊤) := τ
  obtain ⟨ρ, hρ⟩ := AlgebraicGeometry.Scheme.Modules.exists_section_nonvanishingLocus_tensor_eq_inf K G hn σ τ'
  refine ⟨n, hn, ρ, ?_, ?_⟩
  · rw [hρ]
    refine ⟨hxσ, ?_⟩
    show x ∈ G.nonvanishingLocus τ'
    exact hτ
  · rw [hρ]
    exact haff.inf_nonvanishingLocus G τ'

end
