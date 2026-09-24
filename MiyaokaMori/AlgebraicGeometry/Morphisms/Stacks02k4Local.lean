import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesExactIffLocallyLift
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.Stacks02k4Affine

/-! # The first fundamental sequence of differentials: globalization

Globalization of the affine first fundamental sequence (Stacks 01UX / 02K4). For `f : X ⟶ Y`,
`g : Y ⟶ S` with `α = Omega.baseChangeMap f g : f^*Ω_{Y/S} → Ω_{X/S}`, `β = Omega.compMap f g :
Ω_{X/S} → Ω_{X/Y}`:

* `Omega.exists_small_affine`: every point has arbitrarily small affine neighbourhoods `U ⊆ f⁻¹V`,
  `V ⊆ g⁻¹W` with `V`, `W` affine;
* `Omega.compMap_epi`: `β` is an epimorphism (surjectivity is local on sections,
  `Scheme.Modules.epi_iff_locally_surjective_sections`, and holds on small affines by
  `Omega.compMap_app_surjective_affine`);
* `Omega.baseChangeMap_compMap_exact`: `α → β` is exact in the middle (exactness is local,
  `exact_iff_locally_lift_sections`; small affines: `Omega.compMap_app_exact_affine`);
* `Omega.baseChangeMap_mono`: for `f` smooth, `α` is a monomorphism (`Mono α` is exactness of
  `0 → f^*Ω_{Y/S} → Ω_{X/S}`; small affines: `Omega.baseChangeMap_app_injective_affine`).

Source: Stacks 01UX, 02K4 (the relative tangent sequence of §2.1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace ZeroObject
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- Every point `p` of an open `U₀ ⊆ X` lies in an affine open `U ⊆ U₀` with `U ⊆ f⁻¹V`, `V ⊆ g⁻¹W` for
affine opens `V ⊆ Y`, `W ⊆ S` (affine opens form a basis, `Scheme.isBasis_affineOpens`). -/
theorem Omega.exists_small_affine (p : X) (U₀ : X.Opens) (hp : p ∈ U₀) :
    ∃ (W : S.Opens) (_ : IsAffineOpen W) (V : Y.Opens) (_ : IsAffineOpen V) (U : X.Opens)
      (_ : IsAffineOpen U), p ∈ U ∧ U ≤ U₀ ∧ V ≤ g ⁻¹ᵁ W ∧ U ≤ f ⁻¹ᵁ V := by
  obtain ⟨_, ⟨W, hW : IsAffineOpen W, rfl⟩, hpW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g (f p))) isOpen_univ
  obtain ⟨_, ⟨V, hV : IsAffineOpen V, rfl⟩, hpV, hVW⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show f p ∈ g ⁻¹ᵁ W from hpW) (g ⁻¹ᵁ W).isOpen
  obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hpU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show p ∈ U₀ ⊓ f ⁻¹ᵁ V from ⟨hp, hpV⟩)
      (U₀ ⊓ f ⁻¹ᵁ V).isOpen
  exact ⟨W, hW, V, hV, U, hU, hpU, fun x hx => (hUV hx).1, hVW, fun x hx => (hUV hx).2⟩

/-- `β = Omega.compMap f g : Ω_{X/S} → Ω_{X/Y}` is an epimorphism (Stacks 01UX): surjectivity is local on
sections, and on small affine opens it is `KaehlerDifferential.map_surjective`. -/
theorem Omega.compMap_epi : Epi (Omega.compMap f g) := by
  rw [Scheme.Modules.epi_iff_locally_surjective_sections]
  intro U₀ s p hp
  obtain ⟨W, hW, V, hV, U, hU, hpU, hU₀, e₀, e₁⟩ := Omega.exists_small_affine f g p U₀ hp
  obtain ⟨y, hy⟩ := Omega.compMap_app_surjective_affine f g hW hV hU e₀ e₁
    ((Omega f).presheaf.map (homOfLE hU₀).op s)
  exact ⟨U, hU₀, hpU, y, hy⟩

/-- The complex `f^*Ω_{Y/S} → Ω_{X/S} → Ω_{X/Y}` is exact in the middle (Stacks 01UX): exactness is local on
sections, and on small affine opens it is `KaehlerDifferential.exact_mapBaseChange_map` (Stacks 00RS). -/
theorem Omega.baseChangeMap_compMap_exact :
    (ShortComplex.mk (Omega.baseChangeMap f g) (Omega.compMap f g)
      (Omega.baseChangeMap_comp_compMap f g)).Exact := by
  rw [Scheme.Modules.exact_iff_locally_lift_sections]
  intro U₀ x hx p hp
  obtain ⟨W, hW, V, hV, U, hU, hpU, hU₀, e₀, e₁⟩ := Omega.exists_small_affine f g p U₀ hp
  have hx' : (Omega.compMap f g).app U ((Omega (f ≫ g)).presheaf.map (homOfLE hU₀).op x) = 0 := by
    refine (congr($((Omega.compMap f g).mapPresheaf.naturality (homOfLE hU₀).op) x)).trans ?_
    change (Omega f).presheaf.map (homOfLE hU₀).op ((Omega.compMap f g).app U₀ x) = 0
    rw [hx, map_zero]
  obtain ⟨y, hy⟩ := Omega.compMap_app_exact_affine f g hW hV hU e₀ e₁ _ hx'
  exact ⟨U, hU₀, hpU, y, hy⟩

/-- For `f` smooth, `α = Omega.baseChangeMap f g : f^*Ω_{Y/S} → Ω_{X/S}` is a monomorphism (Stacks 02K4):
`Mono α` is the exactness of `0 → f^*Ω_{Y/S} → Ω_{X/S}`, which is local on sections; on small affine opens
`α` is the base-change map `C ⊗_B Ω_{B/A} → Ω_{C/A}`, injective for `B → C` smooth (Stacks 00TA). -/
theorem Omega.baseChangeMap_mono [Smooth f] : Mono (Omega.baseChangeMap f g) := by
  let T : ShortComplex X.Modules :=
    ShortComplex.mk (0 : 0 ⟶ (Scheme.Modules.pullback f).obj (Omega g)) (Omega.baseChangeMap f g)
      zero_comp
  have hT : T.Exact := by
    rw [Scheme.Modules.exact_iff_locally_lift_sections]
    intro U₀ x hx p hp
    obtain ⟨W, hW, V, hV, U, hU, hpU, hU₀, e₀, e₁⟩ := Omega.exists_small_affine f g p U₀ hp
    refine ⟨U, hU₀, hpU, 0, ?_⟩
    have hx' : (Omega.baseChangeMap f g).app U
        (((Scheme.Modules.pullback f).obj (Omega g)).presheaf.map (homOfLE hU₀).op x) = 0 := by
      refine (congr($((Omega.baseChangeMap f g).mapPresheaf.naturality (homOfLE hU₀).op) x)).trans ?_
      change (Omega (f ≫ g)).presheaf.map (homOfLE hU₀).op ((Omega.baseChangeMap f g).app U₀ x) = 0
      rw [hx, map_zero]
    have h0 : ((Scheme.Modules.pullback f).obj (Omega g)).presheaf.map (homOfLE hU₀).op x = 0 :=
      Omega.baseChangeMap_app_injective_affine f g hW hV hU e₀ e₁
        (hx'.trans (map_zero ((Omega.baseChangeMap f g).app U).hom).symm)
    rw [h0]
    exact map_zero _
  exact (T.exact_iff_mono rfl).1 hT

end AlgebraicGeometry

end
