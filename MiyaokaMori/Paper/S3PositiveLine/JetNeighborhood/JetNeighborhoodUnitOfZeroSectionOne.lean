import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodZeroSectionSurjective

/-! # A function on the jet neighbourhood that is `1` along the zero section is a unit

A function on `p_κ⁻¹U ⊆ C̃_(κ)(L)` whose restriction
along the jet zero section is `1` is a unit, because the ideal of the zero section is nilpotent
(`𝓘^{κ+1} = 0` in the truncated jet algebra `⊕_{q ≤ κ} L^{-q}`).

Source: §3 of the paper (the truncated jet algebra and its augmentation); used in the scalar-ratio argument
(`ScalarRatioOfSeedMinorsZero`).
No local model is needed: the affine-local statement
`jetNeighborhood.pow_succ_eq_zero_of_zeroSection_appLE_eq_zero` (JetNeighborhoodZeroSectionSurjective.lean,
via `truncatedJetAlgebra.pow_succ_eq_zero_of_π₀_eq_zero`) gives `(u−1)^{κ+1} = 0` on each `p_κ⁻¹V`,
`V ⊆ U` affine; these are glued by the sheaf axiom and `IsNilpotent.isUnit_add_one` finishes.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **A function on the jet neighbourhood that is `1` along the zero section is a unit.**

Let `p_κ : C̃_(κ)(L) → C̃` be the jet neighbourhood, `σ_κ : C̃ → C̃_(κ)(L)` its zero section
(`jetNeighborhood.zeroSection`), `U ⊆ C̃` open, `W := p_κ⁻¹U`, and `u ∈ Γ(W, O)` with
`(σ_κ|_U)^*u = 1`. Then `u` is a unit.

Proof (source: §3 of the paper, description of `C̃_(κ)(L) = Spec_{C̃} ⊕_{q≤κ} L^{-q}`
and its zero section as the augmentation `⊕_{q≤κ} L^{-q} → L^0 = O_{C̃}`):
1. Transport `u` from `Γ(W.toScheme, ⊤)` to `u' ∈ Γ(C̃_(κ)(L), W)` by `W.topIso`; by Mathlib's
   `Scheme.Hom.resLE_app_top`, the hypothesis becomes `σ_κ^*u' = 1` in `Γ(C̃, U)` (`appLE W U`).
2. For every affine open `V ⊆ U` of `C̃`, `Γ(p_κ⁻¹V, O) = 𝒜(V) = ⊕_{q≤κ} L^{-q}(V)` and `σ_κ^*` is
   the weight-`0` projection (`relativeSpec.structureHom_app_bijective`,
   `relativeSpec.ofAlgebraMap_appLE_structureHom`); the positive-weight ideal is nilpotent
   (`truncatedJetAlgebra.pow_succ_eq_zero_of_π₀_eq_zero`). Both facts are packaged in
   `jetNeighborhood.pow_succ_eq_zero_of_zeroSection_appLE_eq_zero`: if `σ_κ^* w = 0` for
   `w ∈ Γ(p_κ⁻¹V, O)` then `w^{κ+1} = 0`.
3. Apply 2 to `w := u'|_{p_κ⁻¹V} − 1`: `σ_κ^* w = (σ_κ^*u')|_V − 1 = 0` by naturality of `appLE`
   (`Scheme.Hom.map_appLE`, `Scheme.Hom.appLE_map`). Hence `(u' − 1)^{κ+1}` restricts to `0` on
   every `p_κ⁻¹V`; these cover `W` (affine opens form a basis, `Scheme.isBasis_affineOpens`), so
   `(u' − 1)^{κ+1} = 0` in `Γ(C̃_(κ)(L), W)` by the sheaf axiom (`TopCat.Sheaf.eq_of_locally_eq'`).
4. `u' = (u' − 1) + 1` with `u' − 1` nilpotent, so `u'` is a unit (`IsNilpotent.isUnit_add_one`),
   and so is `u = W.topIso.inv u'`. -/
theorem jetNeighborhood.isUnit_of_zeroSection_appTop_eq_one {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ) (U : Ct.toScheme.Opens)
    (u : Γ(((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme, ⊤))
    (hu : ((jetNeighborhood.zeroSection L κ).resLE ((jetNeighborhood.proj L κ) ⁻¹ᵁ U) U
        (by
          change U ≤ (jetNeighborhood.zeroSection L κ ≫ jetNeighborhood.proj L κ) ⁻¹ᵁ U
          rw [jetNeighborhood.zeroSection_proj]
          exact le_rfl)).appTop u = 1) :
    IsUnit u := by
  have hWU : U ≤ jetNeighborhood.zeroSection L κ ⁻¹ᵁ (jetNeighborhood.proj L κ ⁻¹ᵁ U) :=
    jetNeighborhood.le_zeroSection_preimage_proj_preimage L κ U
  -- Step 1: transport `u` to `Γ(X', p⁻¹U)`
  obtain ⟨u', hu'def⟩ : ∃ u' : Γ((jetNeighborhood L κ).left, jetNeighborhood.proj L κ ⁻¹ᵁ U),
      u' = (jetNeighborhood.proj L κ ⁻¹ᵁ U).topIso.hom.hom u := ⟨_, rfl⟩
  have hu' : ((jetNeighborhood.zeroSection L κ).appLE (jetNeighborhood.proj L κ ⁻¹ᵁ U) U hWU).hom u'
      = 1 := by
    have h1 : (((jetNeighborhood.zeroSection L κ).resLE (jetNeighborhood.proj L κ ⁻¹ᵁ U) U hWU).app ⊤ :
        Γ((jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme, ⊤) ⟶ Γ(U.toScheme, ⊤)) =
        (jetNeighborhood.proj L κ ⁻¹ᵁ U).topIso.hom ≫
          (jetNeighborhood.zeroSection L κ).appLE (jetNeighborhood.proj L κ ⁻¹ᵁ U) U hWU ≫
          U.topIso.inv :=
      AlgebraicGeometry.Scheme.Hom.resLE_app_top _ _
    have h2 := congrArg (fun φ : Γ((jetNeighborhood.proj L κ ⁻¹ᵁ U).toScheme, ⊤) ⟶ Γ(U.toScheme, ⊤) =>
      φ.hom u) h1
    have h3 : ((jetNeighborhood.proj L κ ⁻¹ᵁ U).topIso.hom ≫
          (jetNeighborhood.zeroSection L κ).appLE (jetNeighborhood.proj L κ ⁻¹ᵁ U) U hWU ≫
          U.topIso.inv).hom u = 1 := h2.symm.trans hu
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply,
      ← hu'def] at h3
    have h4 := congrArg U.topIso.hom.hom h3
    rw [map_one, ← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.inv_hom_id,
      CommRingCat.hom_id, RingHom.id_apply] at h4
    exact h4
  -- Step 3: `(u' - 1)^(κ+1) = 0` locally on `p⁻¹V`, `V ⊆ U` affine, hence globally on `p⁻¹U`
  have hnil : (u' - 1) ^ (κ + 1) = 0 := by
    refine (jetNeighborhood L κ).left.sheaf.eq_of_locally_eq'
      (fun V : {V : Ct.toScheme.affineOpens // V.1 ≤ U} => jetNeighborhood.proj L κ ⁻¹ᵁ V.1.1)
      (jetNeighborhood.proj L κ ⁻¹ᵁ U)
      (fun V => homOfLE (fun x hx => V.2 hx)) ?_ _ _ ?_
    · intro x hx
      obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
        Ct.toScheme.isBasis_affineOpens (show (jetNeighborhood.proj L κ).base x ∈ U from hx)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hxV⟩
    · intro V
      have hVU : V.1.1 ≤ U := V.2
      have hVW : jetNeighborhood.proj L κ ⁻¹ᵁ V.1.1 ≤ jetNeighborhood.proj L κ ⁻¹ᵁ U :=
        fun x hx => hVU hx
      have e₂ : V.1.1 ≤ jetNeighborhood.zeroSection L κ ⁻¹ᵁ (jetNeighborhood.proj L κ ⁻¹ᵁ V.1.1) :=
        jetNeighborhood.le_zeroSection_preimage_proj_preimage L κ V.1.1
      change ((jetNeighborhood L κ).left.presheaf.map (homOfLE hVW).op).hom ((u' - 1) ^ (κ + 1)) =
        ((jetNeighborhood L κ).left.presheaf.map (homOfLE hVW).op).hom 0
      rw [map_pow, map_sub, map_one, map_zero]
      apply jetNeighborhood.pow_succ_eq_zero_of_zeroSection_appLE_eq_zero L κ V.1
      rw [map_sub, map_one]
      -- `σ^*(u'|_{p⁻¹V}) = (σ^*u')|_V = 1`
      have h1 := congrArg (fun φ : Γ((jetNeighborhood L κ).left, jetNeighborhood.proj L κ ⁻¹ᵁ U) ⟶
          Γ(Ct.toScheme, V.1.1) => φ.hom u')
        (AlgebraicGeometry.Scheme.Hom.map_appLE (jetNeighborhood.zeroSection L κ) e₂ (homOfLE hVW).op)
      have h2 := congrArg (fun φ : Γ((jetNeighborhood L κ).left, jetNeighborhood.proj L κ ⁻¹ᵁ U) ⟶
          Γ(Ct.toScheme, V.1.1) => φ.hom u')
        (AlgebraicGeometry.Scheme.Hom.appLE_map (jetNeighborhood.zeroSection L κ) hWU (homOfLE hVU).op)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1 h2
      rw [hu', map_one] at h2
      rw [h1, ← h2]
      exact sub_self _
  -- Step 4: `u' = (u' - 1) + 1` is a unit, hence so is `u`
  have hunit' : IsUnit u' := by
    have h := IsNilpotent.isUnit_add_one ⟨κ + 1, hnil⟩
    rwa [sub_add_cancel] at h
  have hu_eq : (jetNeighborhood.proj L κ ⁻¹ᵁ U).topIso.inv.hom u' = u := by
    rw [hu'def, ← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id,
      RingHom.id_apply]
  rw [← hu_eq]
  exact hunit'.map (jetNeighborhood.proj L κ ⁻¹ᵁ U).topIso.inv.hom

end
