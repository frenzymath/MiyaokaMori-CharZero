import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle

/-! # Torsion-freeness of line bundles from torsion-freeness of the structure sheaf

**Torsion-freeness passes from the structure sheaf to every line bundle.** Let `Z` be a preirreducible
scheme whose structure sheaf has injective restriction maps to nonempty opens (`Γ(Z, W₂) → Γ(Z, W₁)` is
injective whenever `∅ ≠ W₁ ⊆ W₂`). Then every line bundle `N` on `Z` has the same property. As a corollary,
on an integral scheme the restriction maps of a line bundle to nonempty opens are injective.

Source: standard (Stacks 01PD neighbourhood: locally free sheaves on an integral scheme are torsion-free);
proof of Lemma 4.1 of the paper ("vanishes generically, hence everywhere").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- An isomorphism of `O_Z`-modules is injective on sections over every open. -/
theorem iso_app_injective {Z : AlgebraicGeometry.Scheme.{u}} {A B : Z.Modules} (e : A ≅ B) (U : Z.Opens) :
    Function.Injective (fun s : Γ(A, U) => e.hom.app U s) := by
  intro s t h
  have hc : ∀ x : Γ(A, U), e.inv.app U (e.hom.app U x) = x := fun x =>
    congrArg (fun ψ => (AlgebraicGeometry.Scheme.Modules.Hom.app ψ U) x) e.hom_inv_id
  have h' := congrArg (fun x => e.inv.app U x) h
  simp only [hc] at h'
  exact h'

/-- **Line bundles inherit torsion-freeness from `O_Z`.** `Z` preirreducible; if `Γ(Z, W₂) → Γ(Z, W₁)` is
injective for all nonempty opens `W₁ ≤ W₂`, then for a line bundle `N` a section over `W₂` whose restriction to
a nonempty `W₁ ≤ W₂` vanishes is zero.

**Proof.** By the sheaf axiom (`TopCat.Presheaf.section_ext`) it suffices that every germ of `s` vanishes. Fix
`z ∈ W₂` and a trivialisation `φ : N|_W ≅ O_W` near `z` (`IsLineBundle.locally_trivial`); compose with
`restrictUnitIso` to get `ψ : N|_W ≅ O_Z|_W`. Put `T_i := W.ι⁻¹ W_i` (opens of `W`), so `W.ι(T_i) = W ⊓ W_i`.
The restriction `s₂` of `s` to `W ⊓ W₂` restricts to `0` on `W ⊓ W₁` (it factors through `W₁`), hence by
naturality `g := ψ(s₂) ∈ Γ(Z, W ⊓ W₂)` restricts to `0` on `W ⊓ W₁`, which is nonempty by preirreducibility
(`nonempty_preirreducible_inter`). By hypothesis `g = 0`, so `s₂ = 0` (`ψ` is injective on sections), and the
germ of `s` at `z ∈ W ⊓ W₂` is zero (`germ_ext`). -/
theorem IsLineBundle.eq_zero_of_map_eq_zero {Z : AlgebraicGeometry.Scheme.{u}} [PreirreducibleSpace Z]
    (hO : ∀ (W₁ W₂ : Z.Opens) (h : W₁ ≤ W₂), (W₁ : Set Z).Nonempty →
      ∀ a : Γ(Z, W₂), Z.presheaf.map (homOfLE h).op a = 0 → a = 0)
    (N : Z.Modules) [N.IsLineBundle] {W₁ W₂ : Z.Opens} (h : W₁ ≤ W₂) (hW₁ : (W₁ : Set Z).Nonempty)
    (s : Γ(N, W₂)) (hs : N.presheaf.map (homOfLE h).op s = 0) : s = 0 := by
  refine TopCat.Presheaf.section_ext (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab Z) W₂ s 0 ?_
  intro z hz
  obtain ⟨W, hzW, ⟨φ⟩⟩ := IsLineBundle.locally_trivial (M := N) z
  let ψ : N.restrict W.ι ≅ AlgebraicGeometry.Scheme.Modules.restrict (SheafOfModules.unit Z.ringCatSheaf) W.ι :=
    φ ≪≫ (AlgebraicGeometry.Scheme.Modules.restrictUnitIso W.ι).symm
  let T₂ : W.toScheme.Opens := W.ι ⁻¹ᵁ W₂
  let T₁ : W.toScheme.Opens := W.ι ⁻¹ᵁ W₁
  have hT : T₁ ≤ T₂ := W.ι.preimage_mono h
  have hle₂ : W.ι ''ᵁ T₂ ≤ W₂ := W.ι.image_preimage_le W₂
  have hle₁ : W.ι ''ᵁ T₁ ≤ W₁ := W.ι.image_preimage_le W₁
  let s₂ : Γ(N.restrict W.ι, T₂) := N.presheaf.map (homOfLE hle₂).op s
  -- the restriction of `s₂` to `T₁` vanishes
  have hs₂ : (N.restrict W.ι).presheaf.map (homOfLE hT).op s₂ = 0 := by
    change N.presheaf.map (W.ι.opensFunctor.map (homOfLE hT)).op (N.presheaf.map (homOfLE hle₂).op s) = 0
    have hcomp : (homOfLE hle₂ : W.ι ''ᵁ T₂ ⟶ W₂) ≫ 𝟙 _ = homOfLE hle₂ := Category.comp_id _
    have e1 : W.ι.opensFunctor.map (homOfLE hT) ≫ homOfLE hle₂ =
        (homOfLE hle₁ : W.ι ''ᵁ T₁ ⟶ W₁) ≫ homOfLE h := Subsingleton.elim _ _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, e1, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply, hs, map_zero]
  -- transport through `ψ`
  let g : Γ(Z, W.ι ''ᵁ T₂) := ψ.hom.app T₂ s₂
  have hg : Z.presheaf.map (homOfLE (W.ι.image_mono hT)).op g = 0 := by
    have hn := PresheafOfModules.naturality_apply ψ.hom.val (homOfLE hT).op s₂
    change ψ.hom.app T₁ ((N.restrict W.ι).presheaf.map (homOfLE hT).op s₂) =
      Z.presheaf.map (W.ι.opensFunctor.map (homOfLE hT)).op g at hn
    rw [hs₂, map_zero] at hn
    have e2 : W.ι.opensFunctor.map (homOfLE hT) = homOfLE (W.ι.image_mono hT) := Subsingleton.elim _ _
    rw [e2] at hn
    exact hn.symm
  have hne : ((W.ι ''ᵁ T₁ : Z.Opens) : Set Z).Nonempty := by
    have e3 : W.ι ''ᵁ T₁ = W ⊓ W₁ := by
      rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
        AlgebraicGeometry.Scheme.Opens.opensRange_ι]
    rw [e3, TopologicalSpace.Opens.coe_inf]
    exact nonempty_preirreducible_inter W.isOpen W₁.isOpen ⟨z, hzW⟩ hW₁
  have hg0 : g = 0 := hO _ _ (W.ι.image_mono hT) hne g hg
  have hs₂0 : s₂ = 0 := by
    apply iso_app_injective ψ T₂
    show ψ.hom.app T₂ s₂ = ψ.hom.app T₂ 0
    rw [map_zero]
    exact hg0
  -- the germ of `s` at `z` vanishes
  have hzT : z ∈ W.ι ''ᵁ T₂ := ⟨⟨z, hzW⟩, hz, rfl⟩
  refine TopCat.Presheaf.germ_ext N.presheaf (W.ι ''ᵁ T₂) hzT (homOfLE hle₂) (homOfLE hle₂) ?_
  rw [map_zero]
  exact hs₂0

/-- **On an integral scheme a section of a line bundle vanishing on a nonempty open is zero.** The structure
sheaf of an integral scheme has injective restriction maps to nonempty opens (`germ_injective_of_isIntegral`:
the germ at any point of `W₁` factors through the restriction to `W₁`), and `IsLineBundle.eq_zero_of_map_eq_zero`
transfers this to `N`. -/
theorem IsLineBundle.eq_zero_of_map_eq_zero_of_isIntegral {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] (N : X.Modules) [N.IsLineBundle]
    {W₁ W₂ : X.Opens} (h : W₁ ≤ W₂) (hW₁ : (W₁ : Set X).Nonempty)
    (s : Γ(N, W₂)) (hs : N.presheaf.map (homOfLE h).op s = 0) : s = 0 := by
  refine IsLineBundle.eq_zero_of_map_eq_zero ?_ N h hW₁ s hs
  intro V₁ V₂ hV hne a ha
  obtain ⟨x, hx⟩ := hne
  apply AlgebraicGeometry.germ_injective_of_isIntegral (X := X) x (hV hx)
  rw [map_zero]
  have hres := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hV) x hx a
  rw [ha, map_zero] at hres
  exact hres.symm

end AlgebraicGeometry.Scheme.Modules

end
