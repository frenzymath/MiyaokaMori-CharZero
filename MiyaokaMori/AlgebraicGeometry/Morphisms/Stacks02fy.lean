import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.LocalDimensionOpenEmbedding
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.LocalDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks00p4

/-! # Local dimension of fibers is invariant under base change

Stacks Project, Tag 02FY (1): in a fiber square with `f` locally of finite type, `x′ ↦ x` and
`s′ ↦ s`, one has `dim_x(X_s) = dim_{x′}(X′_{s′})`: the local dimension of the fiber is invariant
under base change (needed for Stacks 0B2M).

Route: Stacks 02FY (1), reduced to Algebra 00P4 via Mathlib's
`isPullback_fiberToSpecResidueField_of_isPullback`, `IsAffineOpen.fromSpec` and `pullbackSpecIso`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- Untruncated local dimension is invariant under open immersions of schemes
(special case of `Topology.IsOpenEmbedding.iInf_topologicalKrullDim_opens_eq`). -/
theorem Scheme.Hom.iInf_topologicalKrullDim_opens_eq_of_isOpenImmersion {W Z : Scheme.{u}}
    (j : W ⟶ Z) [IsOpenImmersion j] (q : W) :
    (⨅ U ∈ {U : W.Opens | q ∈ U}, topologicalKrullDim U) =
      ⨅ U ∈ {U : Z.Opens | j.base q ∈ U}, topologicalKrullDim U :=
  j.isOpenEmbedding.iInf_topologicalKrullDim_opens_eq q

/-- Two embeddings `e₁ : Z₁ → X`, `e₂ : Z₂ → X` with the same range give homeomorphic spaces;
untruncated local dimensions at corresponding points agree. -/
theorem iInf_topologicalKrullDim_opens_eq_of_isEmbedding_of_range_eq
    {Z₁ Z₂ X : Type*} [TopologicalSpace Z₁] [TopologicalSpace Z₂] [TopologicalSpace X]
    {e₁ : Z₁ → X} {e₂ : Z₂ → X} (h₁ : Topology.IsEmbedding e₁) (h₂ : Topology.IsEmbedding e₂)
    (hr : Set.range e₁ = Set.range e₂) {z₁ : Z₁} {z₂ : Z₂} (hz : e₁ z₁ = e₂ z₂) :
    (⨅ U ∈ {U : Opens Z₁ | z₁ ∈ U}, topologicalKrullDim U) =
      ⨅ U ∈ {U : Opens Z₂ | z₂ ∈ U}, topologicalKrullDim U := by
  let φ : Z₁ ≃ₜ Z₂ := h₁.toHomeomorph.trans ((Homeomorph.setCongr hr).trans h₂.toHomeomorph.symm)
  have hφ : φ z₁ = z₂ := by
    have : (Homeomorph.setCongr hr) (h₁.toHomeomorph z₁) = ⟨e₂ z₂, Set.mem_range_self z₂⟩ := by
      ext
      exact hz
    show h₂.toHomeomorph.symm ((Homeomorph.setCongr hr) (h₁.toHomeomorph z₁)) = z₂
    rw [this]
    exact h₂.toHomeomorph_symm_apply z₂
  rw [← hφ]
  exact φ.isOpenEmbedding.iInf_topologicalKrullDim_opens_eq z₁

/-- Core of Stacks 02FY: `F` locally of finite type over the field `k`, `F'` its base change
along `Spec K → Spec k` (`K` a field). Local dimensions at corresponding points agree. -/
theorem iInf_topologicalKrullDim_opens_eq_of_isPullback_over_field
    {k K : Type u} [Field k] [Field K] {F F' : Scheme.{u}}
    (π : F ⟶ Spec (.of k)) [LocallyOfFiniteType π] (ψ : Spec (.of K) ⟶ Spec (.of k))
    (φ : F' ⟶ F) (π' : F' ⟶ Spec (.of K)) (h : IsPullback φ π' π ψ) (p' : F') :
    (⨅ U ∈ {U : F'.Opens | p' ∈ U}, topologicalKrullDim U) =
      ⨅ U ∈ {U : F.Opens | φ.base p' ∈ U}, topologicalKrullDim U := by
  obtain ⟨ρ, rfl⟩ := Spec.map_surjective ψ
  -- an affine open neighbourhood `U ∋ φ p'` of `F`
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    F.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (φ.base p')) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨ρA, hρA⟩ := Spec.map_surjective (hU.fromSpec ≫ π)
  -- `Γ(F, U)` is a finite type `k`-algebra
  have hlft : LocallyOfFiniteType (Spec.map ρA) := by rw [hρA]; infer_instance
  have hft : RingHom.FiniteType ρA.hom :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hlft
  -- the affine piece `P = Spec Γ(F, U) ×_{Spec k} Spec K` of `F'`
  let j : pullback (Spec.map ρA) (Spec.map ρ) ⟶ F' :=
    h.lift (pullback.fst _ _ ≫ hU.fromSpec) (pullback.snd _ _)
      (by rw [Category.assoc, ← hρA, pullback.condition])
  have hjφ : j ≫ φ = pullback.fst _ _ ≫ hU.fromSpec := h.lift_fst _ _ _
  have hjπ' : j ≫ π' = pullback.snd _ _ := h.lift_snd _ _ _
  have hsq : IsPullback j (pullback.fst (Spec.map ρA) (Spec.map ρ)) φ hU.fromSpec := by
    refine IsPullback.of_right ?_ hjφ h.flip
    rw [hjπ', ← hρA]
    exact (IsPullback.of_hasPullback _ _).flip
  have : IsOpenImmersion j :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq.flip inferInstance
  -- `p'` lies in the image of `j`
  obtain ⟨a, ha⟩ : ∃ a : Spec Γ(F, U), hU.fromSpec.base a = φ.base p' := by
    have : φ.base p' ∈ Set.range hU.fromSpec.base := by rw [hU.range_fromSpec]; exact hpU
    exact this
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ) (g := hU.fromSpec)
    p' a ha.symm
  have hjq : j.base (hsq.isoPullback.inv.base z) = p' := by
    rw [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_fst]; exact hz1
  -- algebra structures and the identification `P ≅ Spec (K ⊗_k Γ(F, U))`
  let _ : Algebra k K := ρ.hom.toAlgebra
  let _ : Algebra k Γ(F, U) := ρA.hom.toAlgebra
  have _ : Algebra.FiniteType k Γ(F, U) := hft
  let e : pullback (Spec.map ρA) (Spec.map ρ) ≅ Spec (.of (TensorProduct k K Γ(F, U))) :=
    pullbackSymmetry _ _ ≪≫ pullbackSpecIso k K Γ(F, U)
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight : Γ(F, U) →ₐ[k] TensorProduct k K Γ(F, U)))) =
      pullback.fst (Spec.map ρA) (Spec.map ρ) := by
    simp only [e, Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_snd]
    exact pullbackSymmetry_hom_comp_snd _ _
  have h00P4 := stacks_00P4 (k := k) Γ(F, U) K (e.hom.base (hsq.isoPullback.inv.base z))
  calc (⨅ U ∈ {U : F'.Opens | p' ∈ U}, topologicalKrullDim U)
      = ⨅ V ∈ {V : (pullback (Spec.map ρA) (Spec.map ρ)).Opens | hsq.isoPullback.inv.base z ∈ V},
          topologicalKrullDim V := by
        rw [← hjq]
        exact (j.iInf_topologicalKrullDim_opens_eq_of_isOpenImmersion _).symm
    _ = ⨅ V ∈ {V : (Spec (.of (TensorProduct k K Γ(F, U)))).Opens |
          e.hom.base (hsq.isoPullback.inv.base z) ∈ V}, topologicalKrullDim V :=
        e.hom.iInf_topologicalKrullDim_opens_eq_of_isOpenImmersion _
    _ = ⨅ V ∈ {V : (Spec Γ(F, U)).Opens |
          (pullback.fst (Spec.map ρA) (Spec.map ρ)).base (hsq.isoPullback.inv.base z) ∈ V},
          topologicalKrullDim V := by
        have hpt3 : (pullback.fst (Spec.map ρA) (Spec.map ρ)).base (hsq.isoPullback.inv.base z) =
            (Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
              (Algebra.TensorProduct.includeRight :
                Γ(F, U) →ₐ[k] TensorProduct k K Γ(F, U))))).base
              (e.hom.base (hsq.isoPullback.inv.base z)) := by
          rw [← Scheme.Hom.comp_apply e.hom, he]
        rw [hpt3]
        exact h00P4
    _ = ⨅ U ∈ {U : F.Opens | φ.base p' ∈ U}, topologicalKrullDim U := by
        rw [← hjq, ← Scheme.Hom.comp_apply j φ, hjφ, Scheme.Hom.comp_apply]
        exact hU.fromSpec.iInf_topologicalKrullDim_opens_eq_of_isOpenImmersion _

theorem localDimension_fiber_baseChange {X S S' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType f]
    (x' : ↥(CategoryTheory.Limits.pullback f g)) :
    localDimension ((CategoryTheory.Limits.pullback.snd f g).fiber ((CategoryTheory.Limits.pullback.snd f g).base x'))
        ((CategoryTheory.Limits.pullback.snd f g).asFiber x') =
      localDimension (f.fiber (f.base ((CategoryTheory.Limits.pullback.fst f g).base x')))
        (f.asFiber ((CategoryTheory.Limits.pullback.fst f g).base x')) := by
  -- Step 1: the fibre of `snd` at `s'` is the base change of the fibre of `f` at `g s'`
  -- along `Spec κ(s') → Spec κ(g s')` (Mathlib, `isPullback_fiberToSpecResidueField_of_isPullback`)
  obtain ⟨φ, hφ, hsq⟩ : ∃ φ : (pullback.snd f g).fiber ((pullback.snd f g).base x') ⟶
      f.fiber (g.base ((pullback.snd f g).base x')),
      φ ≫ f.fiberι _ = (pullback.snd f g).fiberι _ ≫ pullback.fst f g ∧
      IsPullback φ ((pullback.snd f g).fiberToSpecResidueField _)
        (f.fiberToSpecResidueField _)
        (Spec.map (g.residueFieldMap ((pullback.snd f g).base x'))) :=
    ⟨_, pullback.lift_fst _ _ _,
      isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f g) _⟩
  have hlft : LocallyOfFiniteType (f.fiberToSpecResidueField (g.base ((pullback.snd f g).base x'))) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (IsPullback.of_hasPullback f (S.fromSpecResidueField _)) inferInstance
  -- Steps 2–4: the core statement over the residue fields
  have hcore := @iInf_topologicalKrullDim_opens_eq_of_isPullback_over_field _ _ _ _ _ _ _ hlft
    _ _ _ hsq ((pullback.snd f g).asFiber x')
  -- the point `φ (asFiber x')` of `f.fiber (g s')` and the point `f.asFiber (fst x')` of
  -- `f.fiber (f (fst x'))` both map to `fst x'` in `X`; both fibres embed into `X` with the same range
  have hpt : (f.fiberι _).base (φ.base ((pullback.snd f g).asFiber x')) =
      (f.fiberι _).base (f.asFiber ((pullback.fst f g).base x')) := by
    rw [Scheme.Hom.fiberι_asFiber, ← Scheme.Hom.comp_apply, hφ, Scheme.Hom.comp_apply,
      Scheme.Hom.fiberι_asFiber]
  have hrange : Set.range (f.fiberι (g.base ((pullback.snd f g).base x'))).base =
      Set.range (f.fiberι (f.base ((pullback.fst f g).base x'))).base := by
    rw [Scheme.Hom.range_fiberι, Scheme.Hom.range_fiberι]
    congr 2
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have h2 := iInf_topologicalKrullDim_opens_eq_of_isEmbedding_of_range_eq
    (f.fiberι _).isEmbedding (f.fiberι _).isEmbedding hrange hpt
  exact congrArg (fun z : WithBot ℕ∞ => (WithBot.unbotD 0 z).toNat) (hcore.trans h2)

end AlgebraicGeometry

end
