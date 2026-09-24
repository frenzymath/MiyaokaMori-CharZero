import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalProperty

/-! # `projBundle.lift` restricted to a local piece

`projBundle.lift` restricted to a local piece is `projBundle.liftLocal`.

Reference: Stacks 01O4 (the morphism `T → P(V)` is glued from local pieces); Mathlib
`AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms`. Used to read `toProjBundle` / `lSection` on a chart.

Two forms:
* `exists_lift_restrict`: for every `t : T` there is a piece
  `(U, e, W, V', …)` with `t ∈ V'` and `V'.ι ≫ lift = liftLocal …` — the piece is the one chosen inside the
  definition of `lift` (`Cover.ι_glueMorphisms`).
* `lift_restrict`: the same equality for *any*
  admissible piece `(U, e, W, V', hV', hle)`, so that two different lifts can be compared on a common chart.
  Proof: the equality of two morphisms out of `V'` is checked on the open cover of `V'` by the pullbacks
  `V' ×_T V_s` of the cover `{V_s}` used inside `lift` (`Cover.hom_ext` on `𝒰.pullback₁ V'.ι`); on such a
  piece `pullback.fst ≫ V'.ι ≫ lift = pullback.snd ≫ V_s.ι ≫ lift = pullback.snd ≫ liftLocal(V_s)`
  (`pullback.condition`, `ι_glueMorphisms`), which is `pullback.fst ≫ liftLocal(V')` by `liftLocal_compat`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

/-- **`lift` agrees with the piece chosen in its definition.** For every `t : T` there are an open `U ∋ t`
trivializing `M`, an affine open `W ∋ f t`, and an affine open `V' ∋ t` with `V' ≤ U ⊓ f⁻¹W`, such that
`V'.ι ≫ projBundle.lift V f M ψ = projBundle.liftLocal V f M ψ U e W V' hV' hle`.
Proof: `lift` is `Cover.glueMorphisms` over the cover `{V_t}`; `Cover.ι_glueMorphisms`. -/
theorem AlgebraicGeometry.Scheme.projBundle.exists_lift_restrict {X T : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    [CategoryTheory.Epi ψ] (t : T) :
    ∃ (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
      (W : X.affineOpens) (V' : T.Opens) (hV' : AlgebraicGeometry.IsAffineOpen V')
      (hle : V' ≤ U ⊓ f ⁻¹ᵁ W.1),
      t ∈ V' ∧
        V'.ι ≫ AlgebraicGeometry.Scheme.projBundle.lift V f M ψ =
          AlgebraicGeometry.Scheme.projBundle.liftLocal V f M ψ U e W V' hV' hle := by
  let hU := fun t : T => SheafOfModules.IsLineBundle.locally_trivial (M := M) t
  let U : T → T.Opens := fun t => (hU t).choose
  let e : ∀ t, M.restrict (U t).ι ≅ SheafOfModules.unit (U t).toScheme.ringCatSheaf :=
    fun t => (hU t).choose_spec.snd.some
  let hW := fun t : T =>
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := f.base t) (U := ⊤) trivial
  let W : T → X.affineOpens := fun t => ⟨(hW t).choose, (hW t).choose_spec.1⟩
  let hA := fun t : T =>
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := t) (U := U t ⊓ f ⁻¹ᵁ (W t).1)
      ⟨(hU t).choose_spec.fst, (hW t).choose_spec.2.1⟩
  let Vt : T → T.Opens := fun t => (hA t).choose
  have hVt : ∀ t, AlgebraicGeometry.IsAffineOpen (Vt t) := fun t => (hA t).choose_spec.1
  have hle : ∀ t, Vt t ≤ U t ⊓ f ⁻¹ᵁ (W t).1 := fun t => (hA t).choose_spec.2.2
  have hcov : TopologicalSpace.IsOpenCover Vt := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro t _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨t, (hA t).choose_spec.2.1⟩
  refine ⟨U t, e t, W t, Vt t, hVt t, hle t, (hA t).choose_spec.2.1, ?_⟩
  exact (T.openCoverOfIsOpenCover Vt hcov).ι_glueMorphisms
    (fun t => AlgebraicGeometry.Scheme.projBundle.liftLocal V f M ψ (U t) (e t) (W t) (Vt t) (hVt t) (hle t))
    (fun s t => AlgebraicGeometry.Scheme.projBundle.liftLocal_compat V f M ψ
      (U s) (e s) (W s) (Vt s) (hVt s) (hle s) (U t) (e t) (W t) (Vt t) (hVt t) (hle t)) t

/-- **`lift` restricted to any admissible piece is `liftLocal`** (Stacks 01O4: the glued morphism is
independent of the choices). For any open `U`, trivialization `e : M|_U ≅ O_U`, affine open `W ⊆ X`, and
affine open `V' ≤ U ⊓ f⁻¹W`:
`V'.ι ≫ projBundle.lift V f M ψ = projBundle.liftLocal V f M ψ U e W V' hV' hle`.

Proof: check on the open cover of `V'` by the pullbacks `V' ×_T V_s` of the cover `{V_s}` inside `lift`
(`Cover.hom_ext`). On such a piece, `pullback.fst ≫ V'.ι ≫ lift = pullback.snd ≫ V_s.ι ≫ lift`
(`pullback.condition`) `= pullback.snd ≫ liftLocal(V_s)` (`ι_glueMorphisms`), and
`liftLocal_compat V' V_s` says this equals `pullback.fst ≫ liftLocal(V')`. -/
theorem AlgebraicGeometry.Scheme.projBundle.lift_restrict {X T : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    [CategoryTheory.Epi ψ]
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    (V' : T.Opens) (hV' : AlgebraicGeometry.IsAffineOpen V') (hle : V' ≤ U ⊓ f ⁻¹ᵁ W.1) :
    V'.ι ≫ AlgebraicGeometry.Scheme.projBundle.lift V f M ψ =
      AlgebraicGeometry.Scheme.projBundle.liftLocal V f M ψ U e W V' hV' hle := by
  let hU := fun t : T => SheafOfModules.IsLineBundle.locally_trivial (M := M) t
  let U' : T → T.Opens := fun t => (hU t).choose
  let e' : ∀ t, M.restrict (U' t).ι ≅ SheafOfModules.unit (U' t).toScheme.ringCatSheaf :=
    fun t => (hU t).choose_spec.snd.some
  let hW := fun t : T =>
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := f.base t) (U := ⊤) trivial
  let W' : T → X.affineOpens := fun t => ⟨(hW t).choose, (hW t).choose_spec.1⟩
  let hA := fun t : T =>
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := t) (U := U' t ⊓ f ⁻¹ᵁ (W' t).1)
      ⟨(hU t).choose_spec.fst, (hW t).choose_spec.2.1⟩
  let Vt : T → T.Opens := fun t => (hA t).choose
  have hVt : ∀ t, AlgebraicGeometry.IsAffineOpen (Vt t) := fun t => (hA t).choose_spec.1
  have hle' : ∀ t, Vt t ≤ U' t ⊓ f ⁻¹ᵁ (W' t).1 := fun t => (hA t).choose_spec.2.2
  have hcov : TopologicalSpace.IsOpenCover Vt := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro t _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨t, (hA t).choose_spec.2.1⟩
  have hpiece : ∀ s : T, (Vt s).ι ≫ AlgebraicGeometry.Scheme.projBundle.lift V f M ψ =
      AlgebraicGeometry.Scheme.projBundle.liftLocal V f M ψ (U' s) (e' s) (W' s) (Vt s) (hVt s) (hle' s) :=
    fun s => (T.openCoverOfIsOpenCover Vt hcov).ι_glueMorphisms
      (fun t => AlgebraicGeometry.Scheme.projBundle.liftLocal V f M ψ (U' t) (e' t) (W' t) (Vt t) (hVt t) (hle' t))
      (fun s t => AlgebraicGeometry.Scheme.projBundle.liftLocal_compat V f M ψ
        (U' s) (e' s) (W' s) (Vt s) (hVt s) (hle' s) (U' t) (e' t) (W' t) (Vt t) (hVt t) (hle' t)) s
  refine AlgebraicGeometry.Scheme.Cover.hom_ext ((T.openCoverOfIsOpenCover Vt hcov).pullback₁ V'.ι) _ _ (fun s => ?_)
  change CategoryTheory.Limits.pullback.fst V'.ι (Vt s).ι ≫ _ = CategoryTheory.Limits.pullback.fst V'.ι (Vt s).ι ≫ _
  rw [← Category.assoc, CategoryTheory.Limits.pullback.condition, Category.assoc, hpiece s]
  exact (AlgebraicGeometry.Scheme.projBundle.liftLocal_compat V f M ψ U e W V' hV' hle
    (U' s) (e' s) (W' s) (Vt s) (hVt s) (hle' s)).symm

/-- The underlying map of the inverse of an isomorphism of schemes is injective. -/
theorem AlgebraicGeometry.Scheme.iso_inv_base_injective {A B : AlgebraicGeometry.Scheme.{u}} (i : A ≅ B) :
    Function.Injective i.inv.base := by
  intro a b h
  have h' := congrArg i.hom.base h
  change (i.inv ≫ i.hom).base a = (i.inv ≫ i.hom).base b at h'
  rw [i.inv_hom_id] at h'
  exact h'

/-- Point-level form of Mathlib's `Proj.fromOfGlobalSections_preimage_basicOpen`: the image of `x` lies in
`D₊(r)` iff `x` lies in the basic open of `f r`. -/
theorem AlgebraicGeometry.Proj.fromOfGlobalSections_base_mem_basicOpen_iff {σ : Type*} {A : Type u}
    [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {Y : AlgebraicGeometry.Scheme.{u}} (f : A →+* Γ(Y, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n)
    (y : Y) :
    (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf).base y ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 r ↔
      y ∈ Y.basicOpen (f r) := by
  rw [← AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf hn hr]
  exact Iff.rfl

/-- **Two local pieces over a common chart cannot meet where a degree-1 coordinate is a unit for one and zero
for the other.** Let `W ⊆ X` be affine, `r ∈ A(W)_1` homogeneous of degree 1, and consider two admissible pieces
`liftLocal V f₁ M₁ ψ₁ U₁ e₁ W V₁ …` and `liftLocal V f₂ M₂ ψ₂ U₂ e₂ W V₂ …` (possibly over different schemes
`T₁`, `T₂`). If the local ring homomorphism of the first sends `r` to a unit and that of the second sends `r` to
`0`, then the two pieces have disjoint images: `liftLocal₁ y₁ ≠ liftLocal₂ y₂`.

Source: Stacks 01O4 / 01M9 (a morphism `fromOfGlobalSections φ` lands in `D₊(r)` exactly on the basic open
`{φ(r) ≠ 0}`; Mathlib `Proj.fromOfGlobalSections_preimage_basicOpen`).
Proof: both pieces are `fromOfGlobalSections φᵢ ≫ (affineIso S W).inv ≫ (π⁻¹W).ι`; `ι` and `affineIso.inv`
are injective on points, so equal images give equal points `aᵢ` of `Proj A(W)`. The first lies in `D₊(r)`
(`φ₁ r` is a unit, so `basicOpen (φ₁ r) = ⊤`), the second does not (`φ₂ r = 0`, `basicOpen 0 = ⊥`). -/
theorem AlgebraicGeometry.Scheme.projBundle.liftLocal_base_ne {X T₁ T₂ : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (f₁ : T₁ ⟶ X) (M₁ : T₁.Modules) [M₁.IsLineBundle]
    (ψ₁ : (AlgebraicGeometry.Scheme.Modules.pullback f₁).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M₁)
    [CategoryTheory.Epi ψ₁]
    (f₂ : T₂ ⟶ X) (M₂ : T₂.Modules) [M₂.IsLineBundle]
    (ψ₂ : (AlgebraicGeometry.Scheme.Modules.pullback f₂).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M₂)
    [CategoryTheory.Epi ψ₂]
    (W : X.affineOpens)
    (U₁ : T₁.Opens) (e₁ : M₁.restrict U₁.ι ≅ SheafOfModules.unit U₁.toScheme.ringCatSheaf)
    (V₁ : T₁.Opens) (hV₁ : AlgebraicGeometry.IsAffineOpen V₁) (hle₁ : V₁ ≤ U₁ ⊓ f₁ ⁻¹ᵁ W.1)
    (U₂ : T₂.Opens) (e₂ : M₂.restrict U₂.ι ≅ SheafOfModules.unit U₂.toScheme.ringCatSheaf)
    (V₂ : T₂.Opens) (hV₂ : AlgebraicGeometry.IsAffineOpen V₂) (hle₂ : V₂ ≤ U₂ ⊓ f₂ ⁻¹ᵁ W.1)
    (y₁ : V₁) (y₂ : V₂)
    (r : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual V)).sectionsRing W.1)
    (hr : r ∈ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual V)).sectionsGrading W.1 1)
    (hu : IsUnit (AlgebraicGeometry.Scheme.projBundle.localRingHom V f₁ M₁ ψ₁ U₁ e₁ W.1 r))
    (hz : AlgebraicGeometry.Scheme.projBundle.localRingHom V f₂ M₂ ψ₂ U₂ e₂ W.1 r = 0) :
    (AlgebraicGeometry.Scheme.projBundle.liftLocal V f₁ M₁ ψ₁ U₁ e₁ W V₁ hV₁ hle₁).base y₁ ≠
      (AlgebraicGeometry.Scheme.projBundle.liftLocal V f₂ M₂ ψ₂ U₂ e₂ W V₂ hV₂ hle₂).base y₂ := by
  intro h
  have h' : ((AlgebraicGeometry.Scheme.relativeProj (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V))).hom ⁻¹ᵁ W.1).ι.base
      ((AlgebraicGeometry.Scheme.relativeProj.affineIso _ W).inv.base
        ((AlgebraicGeometry.Proj.fromOfGlobalSections _
          ((T₁.homOfLE hle₁).appTop.hom.comp
            (AlgebraicGeometry.Scheme.projBundle.localRingHom V f₁ M₁ ψ₁ U₁ e₁ W.1))
          (AlgebraicGeometry.Scheme.projBundle.localRingHom_map_irrelevant V f₁ M₁ ψ₁ U₁ e₁ W V₁ hV₁ hle₁)).base
            y₁)) =
      ((AlgebraicGeometry.Scheme.relativeProj (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V))).hom ⁻¹ᵁ W.1).ι.base
      ((AlgebraicGeometry.Scheme.relativeProj.affineIso _ W).inv.base
        ((AlgebraicGeometry.Proj.fromOfGlobalSections _
          ((T₂.homOfLE hle₂).appTop.hom.comp
            (AlgebraicGeometry.Scheme.projBundle.localRingHom V f₂ M₂ ψ₂ U₂ e₂ W.1))
          (AlgebraicGeometry.Scheme.projBundle.localRingHom_map_irrelevant V f₂ M₂ ψ₂ U₂ e₂ W V₂ hV₂ hle₂)).base
            y₂)) := h
  have h'' := AlgebraicGeometry.Scheme.iso_inv_base_injective _ (Subtype.val_injective h')
  have hu' : (V₁.toScheme).basicOpen (((T₁.homOfLE hle₁).appTop.hom.comp
      (AlgebraicGeometry.Scheme.projBundle.localRingHom V f₁ M₁ ψ₁ U₁ e₁ W.1)) r) = ⊤ :=
    AlgebraicGeometry.Scheme.basicOpen_of_isUnit _ (IsUnit.map (T₁.homOfLE hle₁).appTop.hom hu)
  have hz' : ((T₂.homOfLE hle₂).appTop.hom.comp
      (AlgebraicGeometry.Scheme.projBundle.localRingHom V f₂ M₂ ψ₂ U₂ e₂ W.1)) r = 0 := by
    show (T₂.homOfLE hle₂).appTop.hom
      (AlgebraicGeometry.Scheme.projBundle.localRingHom V f₂ M₂ ψ₂ U₂ e₂ W.1 r) = 0
    rw [hz, map_zero]
  have m₁ := (AlgebraicGeometry.Proj.fromOfGlobalSections_base_mem_basicOpen_iff _
    ((T₁.homOfLE hle₁).appTop.hom.comp
      (AlgebraicGeometry.Scheme.projBundle.localRingHom V f₁ M₁ ψ₁ U₁ e₁ W.1))
    (AlgebraicGeometry.Scheme.projBundle.localRingHom_map_irrelevant V f₁ M₁ ψ₁ U₁ e₁ W V₁ hV₁ hle₁)
    Nat.one_pos hr y₁).2 (by rw [hu']; trivial)
  have m₂ := (AlgebraicGeometry.Proj.fromOfGlobalSections_base_mem_basicOpen_iff _
    ((T₂.homOfLE hle₂).appTop.hom.comp
      (AlgebraicGeometry.Scheme.projBundle.localRingHom V f₂ M₂ ψ₂ U₂ e₂ W.1))
    (AlgebraicGeometry.Scheme.projBundle.localRingHom_map_irrelevant V f₂ M₂ ψ₂ U₂ e₂ W V₂ hV₂ hle₂)
    Nat.one_pos hr y₂).1 (h'' ▸ m₁)
  rw [hz', AlgebraicGeometry.Scheme.basicOpen_zero] at m₂
  exact m₂

end
