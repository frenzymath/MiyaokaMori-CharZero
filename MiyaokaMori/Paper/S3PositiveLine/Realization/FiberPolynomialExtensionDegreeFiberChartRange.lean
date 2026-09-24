import MiyaokaMori.Paper.S3PositiveLine.Realization.FiberPolynomialExtensionDegreeFiberChartMap

/-! # The image of the fiber of the total space in the ruled fiber

The image of the fiber inclusion `Tot(L)_y ⟶ W_y` is the complement of a single point of the ruled
fiber `W_y` (the point over `σ_L(y)`, `σ_L : C̃ → W` the `L`-section that is removed to get `Tot(L)`).

Source: §2 of the paper (`Tot(L) = W ∖ σ_L`) and the proof of Theorem 4.2.
Point-set argument (Hartshorne II, Ex. 3.10: the fiber embedding `W_y → W` is a
homeomorphism onto `π_W^{-1}(y)`; Mathlib `Scheme.Hom.range_fiberι`, `Scheme.Hom.isEmbedding`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The underlying map of an isomorphism of schemes is bijective (`Scheme.homeoOfIso`). -/
theorem AlgebraicGeometry.Scheme.bijective_iso_hom {X Y : AlgebraicGeometry.Scheme.{u}} (e : X ≅ Y) :
    Function.Bijective e.hom := by
  have h := (AlgebraicGeometry.Scheme.homeoOfIso e).bijective
  rwa [show ⇑(AlgebraicGeometry.Scheme.homeoOfIso e) = ⇑e.hom from
    funext (AlgebraicGeometry.Scheme.homeoOfIso_apply e)] at h

/-- **Point-set lemma.** Let `p : T → C`, `π : W → C`, `ι : T → W` with `ι ≫ π = p`, `σ : C → W` a
section of `π` whose image is the complement of the image of `ι`, and `m : p.fiber y → π.fiber y` a
morphism of fibers over `ι` (`m ≫ π.fiberι y = p.fiberι y ≫ ι`). Then the image of `m` is the
complement of a single point `x₀` of `π.fiber y`, namely the unique point with `π.fiberι y x₀ = σ y`.

Proof. `π.fiberι y` is injective (an embedding, Mathlib `Scheme.Hom.isEmbedding`) with image
`π⁻¹(y)` (`Scheme.Hom.range_fiberι`); `σ y ∈ π⁻¹(y)` gives `x₀`. If `x = m z` then
`π.fiberι y x = ι (p.fiberι y z) ∉ im σ`, so `x ≠ x₀`. Conversely if `x ≠ x₀` then `π.fiberι y x ∉ im σ`
(a point `σ c` in `π⁻¹(y)` has `c = y`, so it is `π.fiberι y x₀`), hence `π.fiberι y x = ι t` with
`p t = π (ι t) = y`, `t = p.fiberι y z`, and `π.fiberι y (m z) = ι t = π.fiberι y x` gives `m z = x`. -/
theorem AlgebraicGeometry.Scheme.Hom.exists_range_fiberMap_eq_compl_singleton
    {T W C : AlgebraicGeometry.Scheme.{u}} (p : T ⟶ C) (π : W ⟶ C) (ι : T ⟶ W) (σ : C ⟶ W)
    (hιπ : ι ≫ π = p) (hσ : σ ≫ π = 𝟙 C)
    (hrange : Set.range ι = (Set.range σ)ᶜ) (y : C)
    (m : p.fiber y ⟶ π.fiber y) (hm : m ≫ π.fiberι y = p.fiberι y ≫ ι) :
    ∃ x₀ : π.fiber y, Set.range m = {x₀}ᶜ := by
  have hinj : Function.Injective (π.fiberι y) := (π.fiberι y).isEmbedding.injective
  have hπσ : ∀ c, π (σ c) = c := fun c => by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, hσ]; rfl
  have hπι : ∀ t, π (ι t) = p t := fun t => by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, hιπ]
  have hmι : ∀ z, (π.fiberι y) (m z) = ι ((p.fiberι y) z) := fun z => by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, hm, AlgebraicGeometry.Scheme.Hom.comp_apply]
  have hrπ : Set.range (π.fiberι y) = π ⁻¹' {y} := π.range_fiberι y
  have hrp : Set.range (p.fiberι y) = p ⁻¹' {y} := p.range_fiberι y
  have hfib : ∀ x : π.fiber y, π ((π.fiberι y) x) = y := fun x => by
    have h : (π.fiberι y) x ∈ Set.range (π.fiberι y) := ⟨x, rfl⟩
    rw [hrπ] at h
    exact h
  have hσy : σ y ∈ Set.range (π.fiberι y) := by
    rw [hrπ]; exact hπσ y
  obtain ⟨x₀, hx₀⟩ := hσy
  refine ⟨x₀, Set.ext fun x => ?_⟩
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨z, rfl⟩ hx
    have h1 : (π.fiberι y) (m z) ∈ Set.range ι := ⟨_, (hmι z).symm⟩
    rw [hrange] at h1
    apply h1
    rw [hx, hx₀]
    exact ⟨y, rfl⟩
  · intro hx
    have hnot : (π.fiberι y) x ∉ Set.range σ := by
      rintro ⟨c, hc⟩
      have hc' : c = y := by
        have h1 := hπσ c
        rw [hc, hfib] at h1
        exact h1.symm
      apply hx
      apply hinj
      rw [hx₀, ← hc, hc']
    rw [← Set.mem_compl_iff, ← hrange] at hnot
    obtain ⟨t, ht⟩ := hnot
    have hty : t ∈ Set.range (p.fiberι y) := by
      rw [hrp, Set.mem_preimage, Set.mem_singleton_iff, ← hπι, ht]
      exact hfib x
    obtain ⟨z, hz⟩ := hty
    refine ⟨z, hinj ?_⟩
    rw [hmι, hz, ht]

/-- Composing with an isomorphism: if the image of `f` is the complement of the point `x₀`, the
image of `f ≫ e.hom` is the complement of `e.hom x₀`. -/
theorem AlgebraicGeometry.Scheme.range_comp_iso_hom_eq_compl_singleton
    {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (e : Y ≅ Z) (x₀ : Y)
    (h : Set.range f = {x₀}ᶜ) : Set.range (f ≫ e.hom) = {e.hom x₀}ᶜ := by
  have hc : ⇑(f ≫ e.hom) = ⇑e.hom ∘ ⇑f :=
    funext fun x => AlgebraicGeometry.Scheme.Hom.comp_apply _ _ x
  rw [hc, Set.range_comp, h, Set.image_compl_eq (AlgebraicGeometry.Scheme.bijective_iso_hom e),
    Set.image_singleton]

/-- The image of `Tot(L) ⊆ W` is the complement of the image of the `L`-section `σ_L`
(`totalSpaceIncl = totalSpace.toProjBundle`, whose image is computed in `TotLineAffineOverBase`:
`totalSpace.range_toProjBundle_eq`). -/
theorem ruledSurface.range_totalSpaceIncl {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) :
    Set.range (ruledSurface.totalSpaceIncl L) =
      (Set.range (AlgebraicGeometry.Scheme.lSection L.toModules))ᶜ :=
  AlgebraicGeometry.Scheme.totalSpace.range_toProjBundle_eq L.toModules

/-- **Lemma.** The image of the fiber inclusion `Tot(L)_y ⟶ W_y` (`totalSpaceFiberToRuledFiber`) is
the complement of a single point of `W_y` (the point over `σ_L(y)`).
Proof: `exists_range_fiberMap_eq_compl_singleton` with `ι = totalSpaceIncl L`, `σ = lSection`
(`lSection_comp`: `σ_L ≫ π_W = 𝟙`; `range_totalSpaceIncl`; `totalSpaceFiberToRuledFiber_comp_fiberι`). -/
theorem exists_range_totalSpaceFiberToRuledFiber_eq_compl_singleton {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety) (y : C.toScheme) :
    ∃ x₀ : (ruledSurface.π L).fiber y,
      Set.range (totalSpaceFiberToRuledFiber L y) = {x₀}ᶜ :=
  AlgebraicGeometry.Scheme.Hom.exists_range_fiberMap_eq_compl_singleton
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom (ruledSurface.π L)
    (ruledSurface.totalSpaceIncl L) (AlgebraicGeometry.Scheme.lSection L.toModules)
    (ruledSurface.totalSpaceIncl_comp_π L) (AlgebraicGeometry.Scheme.lSection_comp L.toModules)
    (ruledSurface.range_totalSpaceIncl L) y (totalSpaceFiberToRuledFiber L y)
    (totalSpaceFiberToRuledFiber_comp_fiberι L y)

end
