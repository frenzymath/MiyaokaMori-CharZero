import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesExactIffLocallyLift

/-! # Local surjectivity on an open gives an epimorphism on the open subscheme

**A morphism of `O_X`-modules that is locally surjective on sections over the opens contained in an
open `U` becomes an epimorphism after pullback to the open subscheme `U`.**

This is the "one open" version of `Scheme.Modules.epi_of_openCover` and its converse direction: there
one passes from `Epi ((pullback (𝒰.f i)).map φ)` to local surjectivity on `X`; here we pass from local
surjectivity on the opens `V ≤ U` of `X` to `Epi ((pullback U.ι).map φ)`.

Proof. `pullback U.ι ≅ restrictFunctor U.ι` (`restrictFunctorIsoPullback`), and epimorphisms
are stable under composition with isomorphisms, so it suffices to show that
`ψ := (restrictFunctor U.ι).map φ : M.restrict U.ι ⟶ N.restrict U.ι` is an epimorphism, i.e. locally
surjective on sections of the scheme `U` (`epi_iff_locally_surjective_sections`). Sections of
`N.restrict U.ι` over an open `O` of `U` are sections of `N` over `U.ι ''ᵁ O ≤ U` (`restrictAppIso`,
definitionally the identity), and `ψ.app O = φ.app (U.ι ''ᵁ O)`. Given `O`, `s` and `y ∈ O`, the
hypothesis at `V := U.ι ''ᵁ O`, `s`, `p := U.ι y` gives `W ≤ V` with `p ∈ W` and `t ∈ Γ(M, W)` with
`φ.app W t = s|_W`; put `O' := U.ι ⁻¹ᵁ W` (so `y ∈ O'`, `O' ≤ O` and `U.ι ''ᵁ O' ≤ W`) and take the
section `t|_{U.ι ''ᵁ O'}` of `M.restrict U.ι` over `O'`; it is mapped by `ψ` to `s|_{O'}` by naturality
of `φ` with respect to restriction.

Reference: Stacks 01AG (epimorphisms of sheaves are checked locally) together with the standard
identification of `O_U`-modules on an open subscheme with the restricted sheaves.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Local surjectivity on the opens inside `U` gives an epimorphism on the open subscheme `U`.**
If for every open `V ≤ U`, every section `s ∈ Γ(N, V)` and every point `p ∈ V` there is an open
`W ≤ V` with `p ∈ W` and a section `y ∈ Γ(M, W)` with `φ(y) = s|_W`, then the pullback of `φ` along
the open immersion `U.ι : U ⟶ X` is an epimorphism of `O_U`-modules. -/
theorem AlgebraicGeometry.Scheme.Modules.epi_pullback_ι_map_of_locally_surjective
    {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)
    (h : ∀ (V : X.Opens), V ≤ U → ∀ (s : Γ(N, V)) (p : X), p ∈ V →
      ∃ (W : X.Opens) (hWV : W ≤ V), p ∈ W ∧
        ∃ y : Γ(M, W), φ.app W y = N.presheaf.map (homOfLE hWV).op s) :
    CategoryTheory.Epi ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).map φ) := by
  let ψ : M.restrict U.ι ⟶ N.restrict U.ι :=
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).map φ
  have hψ : CategoryTheory.Epi ψ := by
    rw [AlgebraicGeometry.Scheme.Modules.epi_iff_locally_surjective_sections]
    intro O s y hy
    let V : X.Opens := U.ι ''ᵁ O
    have hVU : V ≤ U := by
      intro x hx
      obtain ⟨z, -, rfl⟩ := hx
      exact z.2
    let sX : Γ(N, V) := (N.restrictAppIso U.ι O).hom s
    have hyV : U.ι y ∈ V := ⟨y, hy, rfl⟩
    obtain ⟨W, hWV, hyW, t, ht⟩ := h V hVU sX (U.ι y) hyV
    let O' : U.toScheme.Opens := U.ι ⁻¹ᵁ W
    have hO'O : O' ≤ O := by
      intro z hz
      have hz' : U.ι z ∈ V := hWV hz
      obtain ⟨z', hz'O, hzz'⟩ := hz'
      have : z' = z := U.ι.isOpenEmbedding.injective hzz'
      exact this ▸ hz'O
    have hyO' : y ∈ O' := hyW
    have hW' : U.ι ''ᵁ O' ≤ W := U.ι.image_preimage_le W
    let tR : Γ(M.restrict U.ι, O') :=
      (M.restrictAppIso U.ι O').inv (M.presheaf.map (homOfLE hW').op t)
    refine ⟨O', hO'O, hyO', tR, ?_⟩
    have hleft : ψ.app O' tR = φ.app (U.ι ''ᵁ O') (M.presheaf.map (homOfLE hW').op t) := rfl
    rw [hleft]
    have hnat : φ.app (U.ι ''ᵁ O') (M.presheaf.map (homOfLE hW').op t) =
        N.presheaf.map (homOfLE hW').op (φ.app W t) :=
      ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hW').op) t
    rw [hnat, ht]
    have hright : (N.restrict U.ι).presheaf.map (homOfLE hO'O).op s =
        N.presheaf.map (homOfLE (U.ι.image_mono hO'O)).op sX := rfl
    rw [hright]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have he := AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι
  have hn := he.hom.naturality φ
  have hright : CategoryTheory.Epi (ψ ≫ he.hom.app N) := inferInstance
  have hleft : CategoryTheory.Epi (he.hom.app M ≫
      (AlgebraicGeometry.Scheme.Modules.pullback U.ι).map φ) := by
    rw [← hn]
    exact hright
  exact CategoryTheory.epi_of_epi (he.hom.app M)
    ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).map φ)

end
