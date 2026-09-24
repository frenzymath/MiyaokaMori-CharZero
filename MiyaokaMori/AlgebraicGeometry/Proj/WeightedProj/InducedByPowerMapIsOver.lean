import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPowerChartFinite

/-! # The power map is a morphism over `Spec k`

The power map `φ : P^N = P(1,…,1) → P(w)` (`InducedByPowerMap`) is compatible with the structure
morphisms of both sides to `Spec k`, i.e. `φ` is a `k`-morphism.

Reference: Stacks Project, Tag 01MY (a graded ring homomorphism induces a morphism between the
`Proj`s, compatible with `Proj → Spec A_0`). The projection formula for the top self-intersection
of the weighted projective space needs `φ` to be a `k`-morphism (`Scheme.Hom.IsOver`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The power map is a `k`-morphism: `g ≫ (P(w) ↘ Spec k) = P(1,…,1) ↘ Spec k`.

Proof sketch. `InducedByPowerMap g` says `g = (topIso).inv ≫ isoOfEq ≫ Proj.mapOfGradedHom ψ`, where
`ψ = weightedPowerGradedHom k w : k[x]` (weights `w`) `→ k[x]` (weights `1`), `x_i ↦ x_i^{w_i}`, is a
`k`-algebra homomorphism; in particular its degree-zero part `ψ_0 : A_0 = k → B_0 = k` is the
identity. Both structure morphisms are `Proj.toSpecZero ≫ Spec.map (algebraMap k _)`. To show
`mapOfGradedHom ψ ≫ toSpecZero 𝒜 = (U(ψ)).ι ≫ toSpecZero ℬ ≫ Spec.map ψ_0`, both sides are
morphisms out of `U(ψ)`, so they are determined by the open cover `D_+(ψ f)`
(`Proj.mapOfGradedHom.cover`, `Scheme.OpenCover.hom_ext`). On each piece
`Proj.mapOfGradedHom_basicOpen` turns the left side into
`Spec (Away.map ψ f) ≫ awayι 𝒜 f ≫ toSpecZero 𝒜 = Spec (Away.map ψ f) ≫ Spec (fromZero 𝒜 f)`
(`Proj.awayι_toSpecZero`), while the right side is
`awayι ℬ (ψ f) ≫ toSpecZero ℬ ≫ Spec ψ_0 = Spec (fromZero ℬ (ψ f)) ≫ Spec ψ_0`; the two ring
homomorphisms `A_0 → B_{(ψ f)}` are both `a ↦ a/1` (compatibility of
`HomogeneousLocalization.Away.map` with `fromZero`, checked on `val`), hence equal. Composing with
`Spec.map (algebraMap k A_0)` and using `ψ_0 ∘ algebraMap k A_0 = algebraMap k B_0` gives the claim. -/
theorem InducedByPowerMap.comp_over (k : Type u) [Field k] {σ : Type u} [Fintype σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (g : weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos) ⟶
      weightedProjectiveSpace k w hw) (hg : InducedByPowerMap g) :
    g ≫ (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos) ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  let _ := MvPolynomial.weightedGradedAlgebra (R := k) w
  let _ := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  obtain ⟨h, rfl⟩ := hg
  set ψ := weightedPowerGradedHom k w
  -- `h` carries the `GradedRing` instances of `weightedProjectiveSpace` (through `ℕ+`); restate it
  -- with the local instances so that the terms below are syntactically uniform
  have h' : AlgebraicGeometry.Proj.mapDomain ψ = ⊤ := h
  -- the key compatibility, as morphisms out of `U(ψ)`
  have key : AlgebraicGeometry.Proj.mapOfGradedHom ψ ≫
      (AlgebraicGeometry.Proj.toSpecZero (MvPolynomial.weightedHomogeneousSubmodule k w) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0)))) =
      (AlgebraicGeometry.Proj.mapDomain ψ).ι ≫
      (AlgebraicGeometry.Proj.toSpecZero
          (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1) 0)))) := by
    apply (AlgebraicGeometry.Proj.mapOfGradedHom.cover ψ).hom_ext
    rintro ⟨⟨f, m⟩, hm, hf⟩
    have hle : AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) (ψ f) ≤
        AlgebraicGeometry.Proj.mapDomain ψ :=
      le_iSup_of_le f (le_iSup_of_le m (le_iSup_of_le hm (le_iSup_of_le hf le_rfl)))
    -- the chart of the cover factors through `homOfLE`
    have hrange : Set.range ((AlgebraicGeometry.Proj.mapDomain ψ).ι ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) (ψ f)).ι.base ⊆
        Set.range ((AlgebraicGeometry.Proj
          (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))).homOfLE hle).base := by
      rw [AlgebraicGeometry.Scheme.Opens.range_ι, ← AlgebraicGeometry.Scheme.Hom.coe_opensRange,
        AlgebraicGeometry.Scheme.opensRange_homOfLE]
    have hl := AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hrange
    change ((AlgebraicGeometry.Proj.mapDomain ψ).ι ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) (ψ f)).ι ≫ _ =
      ((AlgebraicGeometry.Proj.mapDomain ψ).ι ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) (ψ f)).ι ≫ _
    rw [← hl, Category.assoc, Category.assoc]
    congr 1
    rw [← cancel_epi (AlgebraicGeometry.Proj.basicOpenIsoSpec
      (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) (ψ f) (ψ.2 hf) hm).inv]
    rw [reassoc_of% (AlgebraicGeometry.Proj.mapOfGradedHom_basicOpen ψ f m hm hf),
      AlgebraicGeometry.Scheme.homOfLE_ι_assoc,
      AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι_assoc,
      AlgebraicGeometry.Proj.awayι_toSpecZero_assoc, AlgebraicGeometry.Proj.awayι_toSpecZero_assoc,
      ← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_comp,
      ← AlgebraicGeometry.Spec.map_comp]
    congr 1
    ext c
    -- the ring-hom identity `k → (B_(ψ f))_0`
    have hψalg : ψ (algebraMap k (MvPolynomial σ k) c) = algebraMap k (MvPolynomial σ k) c :=
      (MvPolynomial.aeval (R := k)
        (fun j : σ => (MvPolynomial.X j : MvPolynomial σ k) ^ w j)).commutes c
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    change (HomogeneousLocalization.mk _).val = (HomogeneousLocalization.mk _).val
    simp only [HomogeneousLocalization.val_mk]
    congr 1
    exact Subtype.ext (by simp)
  -- assemble: the structure morphisms are `Proj.toSpecZero ≫ Spec.map (algebraMap k _)` by `rfl`
  have final : ((AlgebraicGeometry.Proj
        (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))).topIso.inv ≫
      ((AlgebraicGeometry.Proj
        (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))).isoOfEq h'.symm).hom ≫
      AlgebraicGeometry.Proj.mapOfGradedHom ψ) ≫
      (AlgebraicGeometry.Proj.toSpecZero (MvPolynomial.weightedHomogeneousSubmodule k w) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0)))) =
    AlgebraicGeometry.Proj.toSpecZero
        (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1) 0))) := by
    rw [Category.assoc, Category.assoc, key, AlgebraicGeometry.Scheme.isoOfEq_hom_ι_assoc,
      AlgebraicGeometry.Scheme.toIso_inv_ι_assoc]
  exact final

end
