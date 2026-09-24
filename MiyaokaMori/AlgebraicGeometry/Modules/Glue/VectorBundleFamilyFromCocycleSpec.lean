import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeOfRestrictFreeCover
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOver
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.FreeTransitionCompatible
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.GluedIsGlueCompatible
import MiyaokaMori.AlgebraicGeometry.Modules.MatrixCocycle
import MiyaokaMori.AlgebraicGeometry.Modules.RestrictToLambda
import MiyaokaMori.AlgebraicGeometry.Modules.RestrictToLambdaBundleFamilyTransition
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.TrivializationCocycleFrameIso
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.VectorBundleFamilyFromCocycle

/-! # The vector bundle family glued from a matrix cocycle: local freeness and fibres

The sheaf on `C × A¹` glued from a matrix cocycle `G` is locally free of rank `r`, and its
restriction to `λ = t` is the sheaf glued from `G(t)`: if `G(t)` is a trivialization cocycle of a
module `V`, then the restriction is isomorphic to `V`. (Both ends of the deformation family.)

Proof outline:
1. `GlueData.exists_glued_iso`: the glued sheaf `𝒱` comes with block isomorphisms
   `e_α : 𝒱|_{W_α} ≅ O^r` compatible with the gluing data; the `W_α = toBase⁻¹ U_α` cover
   `C × A¹`, so `𝒱` is locally free (`isLocallyFree_of_restrict_free`).
2. `restrictToLambda_bundleFamilyOfCocycle_transition`: pulling back along `sectionAt t` gives
   `(restrictToLambda 𝒱 t)|_{U_α} ≅ O^r` with transitions `G(t)_{α'α}`.
3. `IsTrivializationCocycle.exists_frame_iso`: the frames of `V` give `V|_{U_α} ≅ O^r` with
   transitions `g_{α'α}`; since `G(t) = g` the two systems of transitions agree, and
   `exists_iso_of_isTransitionCompatible` gives `restrictToLambda 𝒱 t ≅ V`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The family `bundleFamilyOfCocycle U hU G hG` is locally free, and its restriction to `λ = t`
is isomorphic to any module `V` of which `G(t)` is a trivialization cocycle. -/
theorem bundleFamilyOfCocycle_spec {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {ι : Type u} {r : ℕ} (U : ι → C.toScheme.Opens) (hU : ⨆ α, U α = ⊤)
    (G : ∀ α α' : ι, Matrix (Fin r) (Fin r)
      Γ(AlgebraicGeometry.Scheme.affineLineOver C.toScheme,
        AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α ⊓
          AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α'))
    (hG : IsMatrixCocycle (fun α => AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α) G) :
    (bundleFamilyOfCocycle U hU G hG).IsLocallyFree ∧
      ∀ (t : k) (V : C.toScheme.Modules) (g : ∀ α α' : ι, Matrix (Fin r) (Fin r) Γ(C.toScheme, U α ⊓ U α')),
        IsTrivializationCocycle V U g →
        (∀ α α', (G α α').map (AlgebraicGeometry.Scheme.affineLineOver.evalAt C.toScheme t (U α ⊓ U α')) = g α α') →
        Nonempty (SheafOfModules.restrictToLambda (bundleFamilyOfCocycle U hU G hG) t ≅ V) := by
  -- Step 1: the glued sheaf comes with block isomorphisms compatible with the gluing data
  obtain ⟨e, he⟩ := (bundleFamilyOfCocycle.data U G hG).exists_glued_iso
    (fun α => AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α)
  refine ⟨?_, ?_⟩
  · -- local freeness: the `W_α` cover `C × A¹` and each block is `≅ O^r`
    apply AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_restrict_free
    intro x
    have hW : (⨆ α, AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α) = ⊤ := by
      rw [← AlgebraicGeometry.Scheme.Hom.preimage_iSup, hU]
      exact AlgebraicGeometry.Scheme.Hom.preimage_top _
    have hx : x ∈ ⨆ α, AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α := by
      rw [hW]; trivial
    obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨_, (AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α).ι, inferInstance,
      ULift.{u} (Fin r), ⟨⟨x, hα⟩, rfl⟩, ⟨e α⟩⟩
  · intro t V g hg hGt
    -- Step 2: the restriction to `λ = t`, block isomorphisms `ε`, transitions `G(t)`
    obtain ⟨ε, hε⟩ := restrictToLambda_bundleFamilyOfCocycle_transition U hU G hG t e
      (fun α α' => (he α α').isTransitionCompatible)
    -- Step 3: the frames of `V` give block isomorphisms `ψ`, transitions `g`
    obtain ⟨ψ, hψ⟩ := hg.exists_frame_iso
    have hθ : (fun α α' => AlgebraicGeometry.Scheme.Modules.freeTransition (U α) (U α')
        ((G α' α).map (AlgebraicGeometry.Scheme.affineLineOver.evalAt C.toScheme t (U α' ⊓ U α)))) =
        fun α α' => AlgebraicGeometry.Scheme.Modules.freeTransition (U α) (U α') (g α' α) := by
      funext α α'
      rw [hGt α' α]
    rw [hθ] at hε
    exact AlgebraicGeometry.Scheme.Modules.exists_iso_of_isTransitionCompatible U hU _ _ _ _ ε ψ hε hψ

end
