import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineAffineOverBaseFromOfGlobalSectionsComp
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineAffineOverBaseLiftRestrict

/-! # `g ≫ projBundle.lift = projBundle.lift'` from local pieces

Used for `zeroSection_comp_toProjBundle`: two morphisms to a projective bundle that are both `projBundle.lift`s —
one precomposed with `g : S ⟶ T` — are equal as soon as, around every point of `S`, the local ring homomorphisms
`A(W) → Γ(V, O)` of the two pieces (`projBundle.localRingHom`) agree after moving through `g`. This is the
"functoriality of `lift` in the source" (Stacks 01O4: `Mor_X(T, P(V))` is a functor of `T`; the glued morphism is
determined by its pieces `fromOfGlobalSections φ`), reduced to a statement about ring homomorphisms; the
geometric plumbing (`projBundle.lift_restrict`, `Proj.comp_fromOfGlobalSections`, `Cover.hom_ext`) is done here once.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

/-- `fromOfGlobalSections` only depends on the ring homomorphism (the proof argument is transported). -/
theorem AlgebraicGeometry.Proj.fromOfGlobalSections_congr {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : AlgebraicGeometry.Scheme.{u}}
    {φ φ' : A →+* Γ(X, ⊤)} (h : φ = φ') (hφ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map φ = ⊤) :
    AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 φ hφ =
      AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 φ' (h ▸ hφ) := by
  subst h
  rfl

/-- **`g ≫ lift = lift'` can be checked on local pieces.** Let `g : S ⟶ T`, let `(f, M, ψ)` be lift data on `T`
and `(f', M', ψ')` lift data on `S` (for the same `V` on `X`). Suppose that every `s : S` has admissible pieces
`(W, U₁, e₁, V₁)` for the `T`-datum and `(W, U₂, e₂, V₂)` for the `S`-datum over the **same** affine chart
`W ⊆ X`, with `s ∈ V₂ ≤ g⁻¹V₁`, such that the two local ring homomorphisms `A(W) → Γ(V₂, O_S)` agree:
`(g|_{V₂})^♯ ∘ res ∘ localRingHom V f M ψ U₁ e₁ W = res ∘ localRingHom V f' M' ψ' U₂ e₂ W`.
Then `g ≫ projBundle.lift V f M ψ = projBundle.lift V f' M' ψ'`.

Reference: Stacks 01O4 (the morphism to `Proj` is glued from `fromOfGlobalSections` of the local ring
homomorphisms, and `fromOfGlobalSections` is natural in the source scheme: `Proj.comp_fromOfGlobalSections`).

## Proof
Choose the pieces for every `s` (`choose`); the `V₂ s` form an open cover of `S`, so it suffices
(`Scheme.Cover.hom_ext`) to compare after `(V₂ s).ι`.
1. `(V₂ s).ι ≫ lift' = liftLocal' (V₂ s)` and `(V₁ s).ι ≫ lift = liftLocal (V₁ s)` (`projBundle.lift_restrict`);
   `(V₂ s).ι ≫ g = g.resLE (V₁ s) (V₂ s) _ ≫ (V₁ s).ι` (`Scheme.Hom.resLE_comp_ι`).
2. Unfolding `liftLocal`, both sides are `fromOfGlobalSections A(W) φᵢ ≫ (relativeProj.affineIso S W).inv ≫ ι`,
   the left one precomposed with `g.resLE`; `Proj.comp_fromOfGlobalSections` moves `g.resLE` into the ring
   homomorphism, and the hypothesis says the two ring homomorphisms agree (`fromOfGlobalSections_congr`). ∎ -/
theorem AlgebraicGeometry.Scheme.projBundle.comp_lift_of_pieces {X T S : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    [CategoryTheory.Epi ψ]
    (f' : S ⟶ X) (M' : S.Modules) [M'.IsLineBundle]
    (ψ' : (AlgebraicGeometry.Scheme.Modules.pullback f').obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M')
    [CategoryTheory.Epi ψ'] (g : S ⟶ T)
    (H : ∀ s : S, ∃ (W : X.affineOpens) (U₁ : T.Opens)
      (e₁ : M.restrict U₁.ι ≅ SheafOfModules.unit U₁.toScheme.ringCatSheaf) (V₁ : T.Opens)
      (hV₁ : AlgebraicGeometry.IsAffineOpen V₁) (hle₁ : V₁ ≤ U₁ ⊓ f ⁻¹ᵁ W.1) (U₂ : S.Opens)
      (e₂ : M'.restrict U₂.ι ≅ SheafOfModules.unit U₂.toScheme.ringCatSheaf) (V₂ : S.Opens)
      (hV₂ : AlgebraicGeometry.IsAffineOpen V₂) (hle₂ : V₂ ≤ U₂ ⊓ f' ⁻¹ᵁ W.1) (hg : V₂ ≤ g ⁻¹ᵁ V₁),
      s ∈ V₂ ∧
        (g.resLE V₁ V₂ hg).appTop.hom.comp ((T.homOfLE hle₁).appTop.hom.comp
          (AlgebraicGeometry.Scheme.projBundle.localRingHom V f M ψ U₁ e₁ W.1)) =
        (S.homOfLE hle₂).appTop.hom.comp
          (AlgebraicGeometry.Scheme.projBundle.localRingHom V f' M' ψ' U₂ e₂ W.1)) :
    g ≫ AlgebraicGeometry.Scheme.projBundle.lift V f M ψ = AlgebraicGeometry.Scheme.projBundle.lift V f' M' ψ' := by
  choose W U₁ e₁ V₁ hV₁ hle₁ U₂ e₂ V₂ hV₂ hle₂ hg hmem heq using H
  have hcov : TopologicalSpace.IsOpenCover V₂ := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro s _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨s, hmem s⟩
  refine (S.openCoverOfIsOpenCover V₂ hcov).hom_ext _ _ fun s => ?_
  change (V₂ s).ι ≫ g ≫ AlgebraicGeometry.Scheme.projBundle.lift V f M ψ =
    (V₂ s).ι ≫ AlgebraicGeometry.Scheme.projBundle.lift V f' M' ψ'
  rw [AlgebraicGeometry.Scheme.projBundle.lift_restrict V f' M' ψ' (U₂ s) (e₂ s) (W s) (V₂ s) (hV₂ s) (hle₂ s),
    ← Category.assoc, ← AlgebraicGeometry.Scheme.Hom.resLE_comp_ι g (hg s), Category.assoc,
    AlgebraicGeometry.Scheme.projBundle.lift_restrict V f M ψ (U₁ s) (e₁ s) (W s) (V₁ s) (hV₁ s) (hle₁ s)]
  show g.resLE (V₁ s) (V₂ s) (hg s) ≫
      (AlgebraicGeometry.Proj.fromOfGlobalSections _
        ((T.homOfLE (hle₁ s)).appTop.hom.comp
          (AlgebraicGeometry.Scheme.projBundle.localRingHom V f M ψ (U₁ s) (e₁ s) (W s).1))
        (AlgebraicGeometry.Scheme.projBundle.localRingHom_map_irrelevant V f M ψ (U₁ s) (e₁ s) (W s) (V₁ s)
          (hV₁ s) (hle₁ s)) ≫
        (AlgebraicGeometry.Scheme.relativeProj.affineIso _ (W s)).inv ≫ _) =
    AlgebraicGeometry.Proj.fromOfGlobalSections _
        ((S.homOfLE (hle₂ s)).appTop.hom.comp
          (AlgebraicGeometry.Scheme.projBundle.localRingHom V f' M' ψ' (U₂ s) (e₂ s) (W s).1))
        (AlgebraicGeometry.Scheme.projBundle.localRingHom_map_irrelevant V f' M' ψ' (U₂ s) (e₂ s) (W s) (V₂ s)
          (hV₂ s) (hle₂ s)) ≫
      (AlgebraicGeometry.Scheme.relativeProj.affineIso _ (W s)).inv ≫ _
  rw [← Category.assoc, AlgebraicGeometry.Proj.comp_fromOfGlobalSections,
    AlgebraicGeometry.Proj.fromOfGlobalSections_congr _ (heq s)]

end
