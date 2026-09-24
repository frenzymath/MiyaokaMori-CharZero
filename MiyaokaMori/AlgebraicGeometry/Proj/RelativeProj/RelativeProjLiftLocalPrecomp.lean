import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLift
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback

/-! # Naturality of the local pieces of the lift under precomposition

Local piece of the naturality of `relativeProj.lift` under precomposition (Stacks 01O4 / 01N8: morphisms into
relative Proj are compatible with base change), from which `lift_precomp`
(`RelativeProjLiftPrecomp.lean`) is assembled. Three things live here:

* `comp_glueMorphisms_eq`: `k ≫ 𝒰.glueMorphisms F _ = h` as soon as it holds on every pullback piece
  `pullback k (𝒰.f i)` (`Cover.hom_ext` on `𝒰.pullback₁ k` + `pullback.condition` + `ι_glueMorphisms`).
* `lift_ι_eq_liftLocal`: **the restriction of `lift` to any admissible affine piece is that piece's `liftLocal`**,
  `V.ι ≫ lift S f M D = liftLocal S f M D U e W V hV hle` (from `liftLocal_compat`).
* `liftLocalHomAux_precomp` / `liftLocalPieceAux_precomp` / `liftLocalRingHomAux_precomp`: the general-form local data of
  precomposed `LiftData` along `ι'` is that of the original data along `ι' ≫ g`.
* `liftLocal_precomp_of_Ψ_eq`: the local statement itself (see its docstring).

Source: Stacks 01O4, 01N8. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- **Composing into a glued morphism**: `k ≫ 𝒰.glueMorphisms F hF = h` if for every `i` the two sides agree
after `pullback.fst k (𝒰.f i)` (the right-hand side being `pullback.snd ≫ F i`). Proof: `Cover.hom_ext` on the
pulled-back cover `𝒰.pullback₁ k`, then `pullback.condition` and `Cover.ι_glueMorphisms`. -/
theorem comp_glueMorphisms_eq {X Y Z : Scheme.{u}} (𝒰 : X.OpenCover) (F : ∀ i, 𝒰.X i ⟶ Z)
    (hF : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ F i = pullback.snd _ _ ≫ F j)
    (k : Y ⟶ X) (h : Y ⟶ Z)
    (H : ∀ i, pullback.fst k (𝒰.f i) ≫ h = pullback.snd k (𝒰.f i) ≫ F i) :
    k ≫ 𝒰.glueMorphisms F hF = h := by
  refine Cover.hom_ext (𝒰.pullback₁ k) _ _ fun (i : 𝒰.I₀) => ?_
  change pullback.fst k (𝒰.f i) ≫ k ≫ 𝒰.glueMorphisms F hF = pullback.fst k (𝒰.f i) ≫ h
  rw [pullback.condition_assoc, Cover.ι_glueMorphisms, H]

namespace relativeProj

variable {X T T' : Scheme.{u}}

/-- **`lift` restricted to an admissible affine piece is `liftLocal`**: for any trivialization `e` of `M` on `U`,
affine `W ⊆ X`, affine `V ⊆ U ⊓ f⁻¹W`, `V.ι ≫ lift S f M D = liftLocal S f M D U e W V hV hle`.
Proof: `lift` is glued from the pieces `liftLocal … (U t) (e t) (W t) (Vt t)` over the cover `{Vt t}`;
by `comp_glueMorphisms_eq` it suffices to check on `V ×_T Vt t`, where the two pieces agree by `liftLocal_compat`
(with `V₁ = V`, `V₂ = Vt t`). This is the uniqueness half of Stacks 01O4 in the form actually needed downstream. -/
theorem lift_ι_eq_liftLocal (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (D : LiftData S f M) (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (W : X.affineOpens) (V : T.Opens) (hV : IsAffineOpen V) (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1) :
    V.ι ≫ lift S f M D = liftLocal S f M D U e W V hV hle := by
  dsimp only [lift]
  refine comp_glueMorphisms_eq _ _ _ _ _ fun t => ?_
  exact liftLocal_compat S f M D U e W V hV hle _ _ _ _ _ _

/-- `V ≤ U ⊓ f⁻¹W` and `V' ≤ g⁻¹V` give `V' ≤ g⁻¹U ⊓ (g ≫ f)⁻¹W`. -/
theorem precomp_le (g : T' ⟶ T) {f : T ⟶ X} {U : T.Opens} {W : X.Opens} {V : T.Opens}
    (hle : V ≤ U ⊓ f ⁻¹ᵁ W) {V' : T'.Opens} (h : V' ≤ g ⁻¹ᵁ V) :
    V' ≤ g ⁻¹ᵁ U ⊓ (g ≫ f) ⁻¹ᵁ W :=
  fun _ hx => hle (h hx)

/-! ## Precomposed data reduce to the original data

For `D' : LiftData S (g ≫ f) (g^*M)` whose `Ψ`-components are the precomposed ones, the general-form local
morphism/ring homomorphism of `D'` along `ι' : Y → T'` is that of `D` along `ι' ≫ g`, with the trivialization
transported through `pullbackComp ι' g`. The associativity `ι' ≫ (g ≫ f) = (ι' ≫ g) ≫ f` is definitional
(as in `Modules.pullbackComp_inv_app_assoc`), so no `pullbackCongr` is needed. -/

section Precomp

set_option backward.isDefEq.respectTransparency.types false

variable {Y : Scheme.{u}}

/-- **`liftLocalHomAux` of precomposed data**: `Φ^{D'}_{ι', e''} = Φ^{D}_{ι' ≫ g, C⁻¹_{ι',g} ≫ e''}`.
Unfold both sides; `pullbackComp_inv_app_assoc'` merges `C⁻¹_{ι', g≫f} ≫ ι'^*C⁻¹_{g,f}` into
`C⁻¹_{ι'≫g, f} ≫ C⁻¹_{ι',g}`, naturality of `C⁻¹_{ι',g}` moves it past `Ψ_m`, `pullbackMonoidalPow_comp` merges the two
comparison maps, `monoidalPowMap_comp` merges the two tensor powers. Same script as `liftLocalHomAux_comp`. -/
theorem liftLocalHomAux_precomp (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : LiftData S f M) (g : T' ⟶ T) (D' : LiftData S (g ≫ f) ((Modules.pullback g).obj M))
    (hΨ : ∀ m : ℕ, D'.Ψ m = (Modules.pullbackComp g f).inv.app (S.part m) ≫
      (Modules.pullback g).map (D.Ψ m) ≫ Modules.pullbackMonoidalPow g M m)
    (ι' : Y ⟶ T')
    (e'' : (Modules.pullback ι').obj ((Modules.pullback g).obj M) ≅ SheafOfModules.unit Y.ringCatSheaf)
    (m : ℕ) :
    liftLocalHomAux D' ι' e'' m =
      liftLocalHomAux D (ι' ≫ g) (((Modules.pullbackComp ι' g).app M).symm ≪≫ e'') m := by
  unfold liftLocalHomAux
  rw [hΨ m]
  simp only [Functor.map_comp, Category.assoc]
  rw [Modules.pullbackComp_inv_app_assoc' ι' g f (S.part m)]
  erw [← reassoc_of% ((Modules.pullbackComp ι' g).inv.naturality (D.Ψ m))]
  erw [Modules.pullbackMonoidalPow_comp_assoc ι' g M m]
  rw [Iso.trans_hom, Iso.symm_hom, Modules.monoidalPowMap_comp]
  simp only [Category.assoc]
  rfl

/-- Section level of `liftLocalHomAux_precomp`. -/
theorem liftLocalPieceAux_precomp (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : LiftData S f M) (g : T' ⟶ T) (D' : LiftData S (g ≫ f) ((Modules.pullback g).obj M))
    (hΨ : ∀ m : ℕ, D'.Ψ m = (Modules.pullbackComp g f).inv.app (S.part m) ≫
      (Modules.pullback g).map (D.Ψ m) ≫ Modules.pullbackMonoidalPow g M m)
    (ι' : Y ⟶ T')
    (e'' : (Modules.pullback ι').obj ((Modules.pullback g).obj M) ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) (hW : (⊤ : Y.Opens) ≤ (ι' ≫ (g ≫ f)) ⁻¹ᵁ W) (m : ℕ) :
    liftLocalPieceAux D' ι' e'' W hW m =
      liftLocalPieceAux D (ι' ≫ g) (((Modules.pullbackComp ι' g).app M).symm ≪≫ e'') W hW m := by
  unfold liftLocalPieceAux
  rw [liftLocalHomAux_precomp S f M D g D' hΨ ι' e'' m]
  rfl

/-- Ring-homomorphism level of `liftLocalHomAux_precomp`:
`Aux(D', ι', e'', W) = Aux(D, ι' ≫ g, C⁻¹_{ι',g} ≫ e'', W)`. -/
theorem liftLocalRingHomAux_precomp (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : LiftData S f M) (g : T' ⟶ T) (D' : LiftData S (g ≫ f) ((Modules.pullback g).obj M))
    (hΨ : ∀ m : ℕ, D'.Ψ m = (Modules.pullbackComp g f).inv.app (S.part m) ≫
      (Modules.pullback g).map (D.Ψ m) ≫ Modules.pullbackMonoidalPow g M m)
    (ι' : Y ⟶ T')
    (e'' : (Modules.pullback ι').obj ((Modules.pullback g).obj M) ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) (hW : (⊤ : Y.Opens) ≤ (ι' ≫ (g ≫ f)) ⁻¹ᵁ W) :
    liftLocalRingHomAux D' ι' e'' W hW =
      liftLocalRingHomAux D (ι' ≫ g) (((Modules.pullbackComp ι' g).app M).symm ≪≫ e'') W hW := by
  refine DirectSum.ringHom_ext fun m a => ?_
  change liftLocalRingHomAux D' ι' e'' W hW (DirectSum.of (S.sectionsPiece W) m a) =
    liftLocalRingHomAux D (ι' ≫ g) (((Modules.pullbackComp ι' g).app M).symm ≪≫ e'') W hW
      (DirectSum.of (S.sectionsPiece W) m a)
  rw [liftLocalRingHomAux_of, liftLocalRingHomAux_of, liftLocalPieceAux_precomp S f M D g D' hΨ ι' e'' W hW m]

end Precomp

/-- `fromOfGlobalSections` only depends on the ring homomorphism (the irrelevant-ideal condition is a `Prop`). -/
private theorem fromOfGlobalSections_congr_rplp {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : Scheme.{u}}
    {φ ψ : A →+* Γ(Y, ⊤)} (h : φ = ψ) (hφ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map φ = ⊤)
    (hψ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map ψ = ⊤) :
    Proj.fromOfGlobalSections 𝒜 φ hφ = Proj.fromOfGlobalSections 𝒜 ψ hψ := by
  subst h
  rfl

/-- **Local piece of `lift_precomp`** (Stacks 01O4 / 01N8: morphisms into relative Proj commute with base change).

Data: `f : T → X`, a line bundle `M` on `T`, `D : LiftData S f M`, `g : T' → T`, and `D' : LiftData S (g ≫ f) (g^*M)`
whose components are the precomposed ones, `D'.Ψ m = C⁻¹_{g,f} ≫ g^*(D.Ψ m) ≫ pullbackMonoidalPow g M m`
(this is `precompΨ g D.Ψ m` of `RelativeProjLiftPrecomp.lean`, spelled out so that this module need not import it).
An admissible piece `(U, e, W, V)` for `D` and an affine `V' ⊆ g⁻¹V` in `T'`. Claim:
`g|_{V'→V} ≫ liftLocal D U e W V = liftLocal D' (g⁻¹U) (g^*e) W V'`, where `g^*e = pullbackTrivializationIso g e`
is the pulled-back trivialization on `g⁻¹U` (`PullbackUnit.lean`).

## Proof

Write `k := g.resLE V V' h : V' → V` and unfold `liftLocal` on both sides: each side is
`Proj.fromOfGlobalSections (A(W)) φ hφ ≫ (affineIso S W).inv ≫ (π⁻¹W).ι`.

1. **Naturality of `fromOfGlobalSections` in the source**
   (`AlgebraicGeometry.Proj.ProjectiveTupleRestriction.fromOfGlobalSections_naturality`): `k ≫ fromOfGlobalSections φ = fromOfGlobalSections (k^♯ ∘ φ)`.
2. **Left ring homomorphism**: `k^♯ ∘ (V↪U⊓f⁻¹W)^♯ ∘ liftLocalRingHom D U e W = Aux(D, (k ≫ …) ≫ (V↪U) ≫ U.ι, trivComp …, W)`
   (`liftLocalRingHom_eq_aux`, `liftLocalRingHomAux_comp`), and the base morphism is `V'.ι ≫ g`
   (`homOfLE_comp_liftLocalBase_ι`, `Scheme.Hom.resLE_comp_ι`), so by `liftLocalRingHomAux_congr` it is
   `Aux(D, V'.ι ≫ g, E₁, W)` for some trivialization `E₁` of `(V'.ι ≫ g)^*M`.
3. **Right ring homomorphism**: likewise `Aux(D', V'.ι, trivComp …, W)`; by `liftLocalRingHomAux_precomp` (this file)
   this is `Aux(D, V'.ι ≫ g, E₂, W)` for some trivialization `E₂`.
4. **Same base morphism, possibly different trivializations**: `fromOfGlobalSections (Aux(D, ι, E₁, W))` does not depend
   on the trivialization (`fromOfGlobalSections_liftLocalRingHomAux_change_triv`: two trivializations differ by a
   global unit, which cancels in the degree-zero fractions), which finishes the proof. ∎

Edge cases: `V' = ∅` (both sides are the unique morphism from the empty scheme); `m = 0` pieces are
`(ι ≫ f)^♯` on both sides. No `[M.IsLineBundle]` is needed (`liftLocal` does not use it). -/
theorem liftLocal_precomp_of_Ψ_eq (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : LiftData S f M) (g : T' ⟶ T) (D' : LiftData S (g ≫ f) ((Modules.pullback g).obj M))
    (hΨ : ∀ m : ℕ, D'.Ψ m = (Modules.pullbackComp g f).inv.app (S.part m) ≫
      (Modules.pullback g).map (D.Ψ m) ≫ Modules.pullbackMonoidalPow g M m)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (W : X.affineOpens) (V : T.Opens) (hV : IsAffineOpen V) (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1)
    (V' : T'.Opens) (hV' : IsAffineOpen V') (h : V' ≤ g ⁻¹ᵁ V) :
    g.resLE V V' h ≫ liftLocal S f M D U e W V hV hle =
      liftLocal S (g ≫ f) ((Modules.pullback g).obj M) D' (g ⁻¹ᵁ U)
        (Modules.pullbackTrivializationIso g e) W V' hV' (precomp_le g hle h) := by
  have hle' : V' ≤ g ⁻¹ᵁ U ⊓ (g ≫ f) ⁻¹ᵁ W.1 := precomp_le g hle h
  have hW₀ : (⊤ : V'.toScheme.Opens) ≤ ((V'.ι ≫ g) ≫ f) ⁻¹ᵁ W.1 :=
    top_le_ι_comp_preimage (g ≫ f) (hle'.trans inf_le_right)
  -- the two base morphisms `V' → T` are both `V'.ι ≫ g`
  have hι₁ : (g.resLE V V' h ≫ T.homOfLE hle) ≫
      (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W.1 ≤ U) ≫ U.ι) = V'.ι ≫ g := by
    rw [Category.assoc, homOfLE_comp_liftLocalBase_ι f U W.1 hle]
    exact Scheme.Hom.resLE_comp_ι g h
  have hι₂ : (T'.homOfLE hle' ≫
      (T'.homOfLE (inf_le_left : g ⁻¹ᵁ U ⊓ (g ≫ f) ⁻¹ᵁ W.1 ≤ g ⁻¹ᵁ U) ≫ (g ⁻¹ᵁ U).ι)) ≫ g =
      V'.ι ≫ g := by
    rw [homOfLE_comp_liftLocalBase_ι (g ≫ f) (g ⁻¹ᵁ U) W.1 hle']
  -- left ring homomorphism, in the general form along `V'.ι ≫ g`
  obtain ⟨E₁, hL⟩ : ∃ E₁ : (Modules.pullback (V'.ι ≫ g)).obj M ≅ SheafOfModules.unit V'.toScheme.ringCatSheaf,
      (g.resLE V V' h).appTop.hom.comp
        ((T.homOfLE hle).appTop.hom.comp (liftLocalRingHom S f M D U e W.1)) =
      liftLocalRingHomAux D (V'.ι ≫ g) E₁ W.1 hW₀ := by
    have hc : (g.resLE V V' h).appTop.hom.comp (T.homOfLE hle).appTop.hom =
        (g.resLE V V' h ≫ T.homOfLE hle).appTop.hom := by
      rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop]
    exact ⟨_, by
      rw [liftLocalRingHom_eq_aux, ← RingHom.comp_assoc, hc, liftLocalRingHomAux_comp]
      exact (liftLocalRingHomAux_congr D hι₁ _ W.1 _ hW₀).symm⟩
  -- right ring homomorphism, in the general form along `V'.ι ≫ g`
  obtain ⟨E₂, hR⟩ : ∃ E₂ : (Modules.pullback (V'.ι ≫ g)).obj M ≅ SheafOfModules.unit V'.toScheme.ringCatSheaf,
      (T'.homOfLE hle').appTop.hom.comp
        (liftLocalRingHom S (g ≫ f) ((Modules.pullback g).obj M) D' (g ⁻¹ᵁ U)
          (Modules.pullbackTrivializationIso g e) W.1) =
      liftLocalRingHomAux D (V'.ι ≫ g) E₂ W.1 hW₀ :=
    ⟨_, by
      rw [liftLocalRingHom_eq_aux, liftLocalRingHomAux_comp]
      exact (liftLocalRingHomAux_precomp S f M D g D' hΨ _ _ W.1 _).trans
        (liftLocalRingHomAux_congr D hι₂ _ W.1 _ hW₀).symm⟩
  -- assemble
  have : IsAffine V'.toScheme := hV'
  have h₁ := liftLocalRingHomAux_map_irrelevant D (V'.ι ≫ g) E₁ W hW₀
  have h₂ := liftLocalRingHomAux_map_irrelevant D (V'.ι ≫ g) E₂ W hW₀
  unfold liftLocal
  rw [← Category.assoc, AlgebraicGeometry.Proj.ProjectiveTupleRestriction.fromOfGlobalSections_naturality,
    fromOfGlobalSections_congr_rplp _ hL _ h₁, fromOfGlobalSections_congr_rplp _ hR _ h₂,
    fromOfGlobalSections_liftLocalRingHomAux_change_triv S f M D (V'.ι ≫ g) E₂ E₁ W.1 hW₀ h₂ h₁]

end relativeProj

end AlgebraicGeometry.Scheme

end
