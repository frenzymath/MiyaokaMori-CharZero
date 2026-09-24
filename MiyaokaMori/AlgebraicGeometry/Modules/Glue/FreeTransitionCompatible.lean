import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.VectorBundleFamilyFromCocycle
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.Stacks00an

/-! # Uniqueness of gluing without the cocycle condition

Given sheaves `F_i` on the members `U_i` of an open cover and transition morphisms `θ_ij` on the
overlaps (neither a cocycle condition nor invertibility is required), two sheaves of modules
`M`, `M′` with block isomorphisms `e_i : M|_{U_i} ≅ F_i`, `e′_i : M′|_{U_i} ≅ F_i` both
compatible with `θ` (`θ_ij ∘ e_i = e_j`, `IsTransitionCompatible`) are isomorphic.

This is `glue_unique` (Stacks 00AN) without the assumption that `(F, θ)` is gluing data: that
proof only uses the compatibility, never the cocycle condition. It is used to compare the
restriction `restrictToLambda 𝒱 t` of a bundle family (block isomorphisms by pullback,
transitions `G(t)`) with a module `V` (block isomorphisms from frames, transitions `g`): when
`G(t) = g` the two are isomorphic, without repackaging `g` as a `GlueData`.

Also here: `freeTransition`, the transition morphism between free sheaves `O^r` given by a matrix
(the `hom` of `bundleFamilyOfCocycle.dataφ`), and the bridge
`IsGlueCompatible → IsTransitionCompatible`.

References: Stacks 00AN (uniqueness of gluing), 04TN (gluing of morphisms).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The transition morphism `O^r|_{V ⊓ V′} → O^r|_{V ⊓ V′}` between free sheaves given by a matrix
`g` with coefficients in `Γ(Y, V′ ⊓ V)` (from the coordinates on `V` to those on `V′`: the column
vector of coordinates is multiplied on the left by `g`): `matrixHom (swapMatrix g)` conjugated by
`restrictFreeIso`. The `hom` of `bundleFamilyOfCocycle.dataφ U G hG α α'` is
`freeTransition (W α) (W α') (G α' α)` (`bundleFamilyOfCocycle.dataφ_hom`). -/
noncomputable def AlgebraicGeometry.Scheme.Modules.freeTransition {Y : AlgebraicGeometry.Scheme.{u}} {r : ℕ}
    (V V' : Y.Opens) (g : Matrix (Fin r) (Fin r) Γ(Y, V' ⊓ V)) :
    AlgebraicGeometry.Scheme.Modules.restrict
        (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))
        (Y.homOfLE (inf_le_left : V ⊓ V' ≤ V)) ⟶
      AlgebraicGeometry.Scheme.Modules.restrict
        (SheafOfModules.free (R := V'.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))
        (Y.homOfLE (inf_le_right : V ⊓ V' ≤ V')) :=
  (bundleFamilyOfCocycle.restrictFreeIso inf_le_left).hom ≫
    bundleFamilyOfCocycle.matrixHom (V ⊓ V') (bundleFamilyOfCocycle.swapMatrix V V' g) ≫
    (bundleFamilyOfCocycle.restrictFreeIso inf_le_right).inv

/-- The transition isomorphisms of `bundleFamilyOfCocycle` are `freeTransition`s. -/
theorem bundleFamilyOfCocycle.dataφ_hom {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {ι : Type u} {r : ℕ} (U : ι → C.toScheme.Opens)
    (G : ∀ α α' : ι, Matrix (Fin r) (Fin r)
      Γ(AlgebraicGeometry.Scheme.affineLineOver C.toScheme,
        AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α ⊓
          AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α'))
    (hG : IsMatrixCocycle
      (fun α => AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α) G)
    (α α' : ι) :
    (bundleFamilyOfCocycle.dataφ U G hG α α').hom =
      AlgebraicGeometry.Scheme.Modules.freeTransition
        (AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α)
        (AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α') (G α' α) := rfl

/-- A family of block isomorphisms `e_i : M|_{U_i} ≅ F_i` is compatible with the transition
morphisms `θ_ij`: `θ_ij ∘ e_i = e_j` on `U_ij` (aligned via `restrictιIso`). Same shape as
`IsGlueCompatible`, but `(F, θ)` need not be gluing data. -/
def AlgebraicGeometry.Scheme.Modules.IsTransitionCompatible {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : ∀ i, (U i).toScheme.Modules)
    (θ : ∀ i j, (F i).restrict (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) ⟶
      (F j).restrict (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)))
    (M : X.Modules) (e : ∀ i, M.restrict (U i).ι ≅ F i) (i j : ι) : Prop :=
  (AlgebraicGeometry.Scheme.Modules.restrictιIso (inf_le_left : U i ⊓ U j ≤ U i) M).inv ≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor
        (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).map (e i).hom ≫ θ i j
    = (AlgebraicGeometry.Scheme.Modules.restrictιIso (inf_le_right : U i ⊓ U j ≤ U j) M).inv ≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor
        (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j))).map (e j).hom

/-- Compatibility with gluing data implies compatibility with its transition morphisms
`(D.F, (D.φ i j).hom)` (take `hom` on both sides of `IsGlueCompatible`). -/
theorem AlgebraicGeometry.Scheme.Modules.IsGlueCompatible.isTransitionCompatible
    {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (D : AlgebraicGeometry.Scheme.Modules.GlueData U) (M : X.Modules)
    (e : ∀ i, M.restrict (U i).ι ≅ D.F i) (i j : ι)
    (h : AlgebraicGeometry.Scheme.Modules.IsGlueCompatible U D M e i j) :
    AlgebraicGeometry.Scheme.Modules.IsTransitionCompatible U D.F (fun i j => (D.φ i j).hom) M e i j := by
  unfold AlgebraicGeometry.Scheme.Modules.IsGlueCompatible at h
  have h' := congrArg Iso.hom h
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at h'
  exact h'

/-- Between two families of block isomorphisms compatible with the same `(F, θ)`, the morphisms
`e_i ≫ e′_i⁻¹` on the pieces agree on overlaps (`agreeOnOverlap_of_isGlueCompatible` without the
cocycle condition). -/
theorem AlgebraicGeometry.Scheme.Modules.agreeOnOverlap_of_isTransitionCompatible
    {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : ∀ i, (U i).toScheme.Modules)
    (θ : ∀ i j, (F i).restrict (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) ⟶
      (F j).restrict (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)))
    (M M' : X.Modules) (e : ∀ i, M.restrict (U i).ι ≅ F i) (e' : ∀ i, M'.restrict (U i).ι ≅ F i)
    (he : ∀ i j, AlgebraicGeometry.Scheme.Modules.IsTransitionCompatible U F θ M e i j)
    (he' : ∀ i j, AlgebraicGeometry.Scheme.Modules.IsTransitionCompatible U F θ M' e' i j) (i j : ι) :
    AlgebraicGeometry.Scheme.Modules.AgreeOnOverlap U M M' (fun i => (e i).hom ≫ (e' i).inv) i j := by
  have h1 := he i j
  have h2 := he' i j
  unfold AlgebraicGeometry.Scheme.Modules.IsTransitionCompatible at h1 h2
  unfold AlgebraicGeometry.Scheme.Modules.AgreeOnOverlap
  rw [← cancel_mono ((AlgebraicGeometry.Scheme.Modules.restrictιIso (inf_le_right : U i ⊓ U j ≤ U j) M').inv ≫
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor
      (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j))).map (e' j).hom)]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← h2]
  simp only [Iso.hom_inv_id_assoc, Iso.map_inv_hom_id_assoc, Iso.map_inv_hom_id, Category.comp_id]
  exact h1

/-- Uniqueness of gluing without the cocycle condition: two sheaves of modules with families of
block isomorphisms compatible with the same `(F, θ)` are isomorphic. The proof is that of
`glue_unique`: the morphisms `e_i ≫ e′_i⁻¹` agree on overlaps
(`agreeOnOverlap_of_isTransitionCompatible`) and glue (Stacks 04TN, `existsUnique_glue_hom`) to
`g : M ⟶ M′`; symmetrically one gets `h`; `g ≫ h` and `h ≫ g` are the identity on every piece,
hence the identity by `hom_ext_of_cover`. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_iso_of_isTransitionCompatible
    {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (F : ∀ i, (U i).toScheme.Modules)
    (θ : ∀ i j, (F i).restrict (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) ⟶
      (F j).restrict (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)))
    (M M' : X.Modules) (e : ∀ i, M.restrict (U i).ι ≅ F i) (e' : ∀ i, M'.restrict (U i).ι ≅ F i)
    (he : ∀ i j, AlgebraicGeometry.Scheme.Modules.IsTransitionCompatible U F θ M e i j)
    (he' : ∀ i j, AlgebraicGeometry.Scheme.Modules.IsTransitionCompatible U F θ M' e' i j) :
    Nonempty (M ≅ M') := by
  obtain ⟨g, hg, -⟩ := AlgebraicGeometry.Scheme.Modules.existsUnique_glue_hom U hU M M'
    (fun i => (e i).hom ≫ (e' i).inv)
    (AlgebraicGeometry.Scheme.Modules.agreeOnOverlap_of_isTransitionCompatible U F θ M M' e e' he he')
  obtain ⟨h, hh, -⟩ := AlgebraicGeometry.Scheme.Modules.existsUnique_glue_hom U hU M' M
    (fun i => (e' i).hom ≫ (e i).inv)
    (AlgebraicGeometry.Scheme.Modules.agreeOnOverlap_of_isTransitionCompatible U F θ M' M e' e he' he)
  have hgh : g ≫ h = 𝟙 M := AlgebraicGeometry.Scheme.Modules.hom_ext_of_cover U hU _ _ (fun i => by
    rw [Functor.map_comp, hg, hh, CategoryTheory.Functor.map_id]; simp)
  have hhg : h ≫ g = 𝟙 M' := AlgebraicGeometry.Scheme.Modules.hom_ext_of_cover U hU _ _ (fun i => by
    rw [Functor.map_comp, hg, hh, CategoryTheory.Functor.map_id]; simp)
  exact ⟨⟨g, h, hgh, hhg⟩⟩

end
