import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.OmegaQuasicoherent

/-! # The étale criterion via differentials

Étale criterion: let `Z`, `W` be smooth over `S` of the same relative dimension and `g : Z → W` an
`S`-morphism; if `Ω_{Z/W} = 0` (equivalently, `g^*Ω_{W/S} → Ω_{Z/S}` is an isomorphism), then `g` is
étale. This is a special case of EGA IV₄ Cor. 17.11.2 (c) ⇒ (a); it is used for the local coordinates
on the based jet space (§2.2 of the paper: the coordinate map "is étale near" the section).

Route:
* Algebraic core `Algebra.etale_of_isStandardSmoothOfRelativeDimension_of_subsingleton_kaehler`:
  for `A → P → B` with `A → P` and `A → B` standard smooth of the same relative dimension `d` and
  `Ω[B⁄P] = 0`, the Jacobi–Zariski sequence (Mathlib `Algebra.H1Cotangent.exact_map_δ`,
  `exact_δ_mapBaseChange`, `KaehlerDifferential.exact_mapBaseChange_map`) gives
  `H¹(L_{B/P}) = 0`: the linear part `B ⊗[P] Ω[P⁄A] → Ω[B⁄A]` is onto (its cokernel is `Ω[B⁄P]`)
  between free `B`-modules of rank `d`, hence bijective (Orzech), so `δ = 0` and `H¹(L_{B/A}) = 0`
  forces `H¹(L_{B/P}) = 0`. Finite presentation of `P → B` follows from Stacks 0561.
* Geometric part: étale = smooth of relative dimension `0` (Mathlib
  `Etale.iff_smoothOfRelativeDimension_zero`); around each `z` we take standard smooth charts of
  `q` and `g ≫ q`, shrink them to a common `S`-chart `S.basicOpen r` and to a `Z`-chart inside
  `g ⁻¹ᵁ (W.basicOpen s)` (basic-open shrinking as in Mathlib's `smoothOfRelativeDimension_comp`),
  read off `Ω[Γ(Z,V)⁄Γ(W,U)] ≅ Γ(V, Ω_{Z/W}) = 0` (Stacks 01UT, `Omega_appIso`) and apply the core.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

/-- **Algebraic étale criterion.** Let `A → P → B` be ring maps with `A → P` and `A → B` standard
smooth of the same relative dimension `d` and `Ω[B⁄P] = 0`. Then `P → B` is étale.

Proof (Stacks 00S2 Jacobi–Zariski, 00T7, 0561; EGA IV₄ 17.11.2): if `B = 0` there is nothing to
prove. Otherwise `P ≠ 0`; `B ⊗[P] Ω[P⁄A]` and `Ω[B⁄A]` are free `B`-modules of rank `d`
(`IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`), and
`B ⊗[P] Ω[P⁄A] → Ω[B⁄A] → Ω[B⁄P] → 0` is exact, so the first map is onto, hence bijective
(`OrzechProperty.bijective_of_surjective_of_finrank_le`). In
`H¹(L_{B/A}) → H¹(L_{B/P}) →δ B ⊗[P] Ω[P⁄A] → Ω[B⁄A]`, `δ` has kernel the image of
`H¹(L_{B/A}) = 0` (standard smooth) and image the kernel of an injective map, so `H¹(L_{B/P}) = 0`.
Together with `Ω[B⁄P] = 0` this is `FormallyEtale P B`; `FinitePresentation P B` is Stacks 0561. -/
theorem Algebra.etale_of_isStandardSmoothOfRelativeDimension_of_subsingleton_kaehler
    {A P B : Type u} [CommRing A] [CommRing P] [CommRing B] [Algebra A P] [Algebra A B] [Algebra P B]
    [IsScalarTower A P B] (d : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension d A P]
    [Algebra.IsStandardSmoothOfRelativeDimension d A B]
    [Subsingleton Ω[B⁄P]] : Algebra.Etale P B := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · infer_instance
  have : Nontrivial P := (algebraMap P B).domain_nontrivial
  have hsP : Algebra.IsStandardSmooth A P :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  have hsB : Algebra.IsStandardSmooth A B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  have hFP : Algebra.FinitePresentation P B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A P B
  have hsurj : Function.Surjective (KaehlerDifferential.mapBaseChange A P B) := by
    intro y
    have := (KaehlerDifferential.exact_mapBaseChange_map A P B) y
    exact this.mp (Subsingleton.elim _ _)
  have hrk1 : Module.finrank B (B ⊗[P] Ω[P⁄A]) = d := by
    rw [Module.finrank_baseChange]
    exact Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential d)
  have hrk2 : Module.finrank B Ω[B⁄A] = d :=
    Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential d)
  have hbij : Function.Bijective (KaehlerDifferential.mapBaseChange A P B) :=
    OrzechProperty.bijective_of_surjective_of_finrank_le _ hsurj (by rw [hrk1, hrk2])
  have hH1 : Subsingleton (Algebra.H1Cotangent P B) := by
    refine ⟨fun x y => ?_⟩
    have key : ∀ z : Algebra.H1Cotangent P B, z = 0 := by
      intro z
      have h1 : KaehlerDifferential.mapBaseChange A P B (Algebra.H1Cotangent.δ A P B z) = 0 :=
        (Algebra.H1Cotangent.exact_δ_mapBaseChange A P B).apply_apply_eq_zero z
      have h2 : Algebra.H1Cotangent.δ A P B z = 0 := hbij.1 (by rw [h1, map_zero])
      obtain ⟨w, hw⟩ := (Algebra.H1Cotangent.exact_map_δ A P B z).mp h2
      rw [← hw, Subsingleton.elim w 0, map_zero]
    rw [key x, key y]
  exact ⟨⟨inferInstance, hH1⟩, hFP⟩

/-- Ring-hom form of `Algebra.etale_of_isStandardSmoothOfRelativeDimension_of_subsingleton_kaehler`:
`φ : A → P`, `ψ : P → B` with `φ`, `ψ ∘ φ` standard smooth of relative dimension `d` and `ψ`
formally unramified (`Ω[B⁄P] = 0`) ⟹ `ψ` étale. -/
theorem RingHom.etale_of_isStandardSmoothOfRelativeDimension_of_formallyUnramified
    {A P B : Type u} [CommRing A] [CommRing P] [CommRing B] (φ : A →+* P) (ψ : P →+* B) (d : ℕ)
    (hφ : φ.IsStandardSmoothOfRelativeDimension d)
    (hψφ : (ψ.comp φ).IsStandardSmoothOfRelativeDimension d)
    (hψ : ψ.FormallyUnramified) : ψ.Etale := by
  algebraize [φ, ψ, ψ.comp φ]
  exact Algebra.etale_of_isStandardSmoothOfRelativeDimension_of_subsingleton_kaehler
    (A := A) (P := P) (B := B) d

/-- A zero object of `Z.Modules` has only the zero section over every open. -/
theorem AlgebraicGeometry.Omega.subsingleton_sections_of_isZero {Z W : AlgebraicGeometry.Scheme.{u}}
    (g : Z ⟶ W) (hΩ : IsZero (AlgebraicGeometry.Omega g)) (V : Z.Opens) :
    Subsingleton Γ(AlgebraicGeometry.Omega g, V) :=
  ModuleCat.subsingleton_of_isZero
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op V)).map_isZero hΩ)

/-- If `Ω_{Z/W} = 0` then for affine `U ⊆ W`, `V ⊆ g⁻¹U` the ring map `Γ(W,U) → Γ(Z,V)` is
formally unramified, i.e. `Ω[Γ(Z,V)⁄Γ(W,U)] = 0` (Stacks 01UT: `Γ(V, Ω_{Z/W}) ≅ Ω[Γ(Z,V)⁄Γ(W,U)]`,
`Omega_appIso`). -/
theorem AlgebraicGeometry.Omega.formallyUnramified_appLE_of_isZero {Z W : AlgebraicGeometry.Scheme.{u}}
    (g : Z ⟶ W) (hΩ : IsZero (AlgebraicGeometry.Omega g)) {U : W.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) {V : Z.Opens} (hV : AlgebraicGeometry.IsAffineOpen V)
    (e : V ≤ g ⁻¹ᵁ U) : (g.appLE U V e).hom.FormallyUnramified := by
  let _ := (g.appLE U V e).hom.toAlgebra
  have : Subsingleton Γ(AlgebraicGeometry.Omega g, V) :=
    AlgebraicGeometry.Omega.subsingleton_sections_of_isZero g hΩ V
  exact ⟨(AlgebraicGeometry.Omega_appIso g hU hV e).symm.toEquiv.subsingleton⟩

/-- **Étale criterion via differentials** (EGA IV₄ 17.11.2; §2.2 of the paper).
`Z → W → S` with `Z` and `W` smooth over `S` of the same relative dimension `d`; if
`Ω_{Z/W} = 0` then `g : Z → W` is étale. -/
theorem AlgebraicGeometry.etale_of_omega_isZero {Z W S : AlgebraicGeometry.Scheme.{u}}
    (g : Z ⟶ W) (q : W ⟶ S) (d : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension d (g ≫ q)]
    [AlgebraicGeometry.SmoothOfRelativeDimension d q]
    (hΩ : CategoryTheory.Limits.IsZero (AlgebraicGeometry.Omega g)) :
    AlgebraicGeometry.Etale g := by
  rw [AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero]
  constructor
  intro z
  obtain ⟨U₀, hU₀, V', hV', hzV', e', hh⟩ :=
    AlgebraicGeometry.SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := d) (f := g ≫ q) z
  obtain ⟨U₀', hU₀', U₁, hU₁, hgz, e₁, hq⟩ :=
    AlgebraicGeometry.SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := d) (f := q) (g z)
  have hqgz : q (g z) ∈ U₀ := e' hzV'
  obtain ⟨r, s, hgzs, es, hq'⟩ := AlgebraicGeometry.exists_basicOpen_le_appLE_of_appLE_of_isAffine
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway d).right
    (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves d).away
    (g z) ⟨U₀, hU₀⟩ ⟨U₀', hU₀'⟩ ⟨U₁, hU₁⟩ ⟨U₁, hU₁⟩ hgz hgz e₁ hq hqgz
  -- shrink the chart of `g ≫ q` to the `S`-chart `S.basicOpen r`
  set h := g ≫ q with hh_def
  let r' : Γ(Z, V') := h.appLE U₀ V' e' r
  have hr'aff : AlgebraicGeometry.IsAffineOpen (Z.basicOpen r') := hV'.basicOpen r'
  have hz2 : h z ∈ S.basicOpen r := es hgzs
  have hzr' : z ∈ Z.basicOpen r' := by
    simpa [r', AlgebraicGeometry.Scheme.Hom.appLE, ← AlgebraicGeometry.Scheme.preimage_basicOpen]
      using And.intro hzV' hz2
  have e_r' : Z.basicOpen r' ≤ h ⁻¹ᵁ S.basicOpen r := by
    simp [r', AlgebraicGeometry.Scheme.Hom.appLE]
  have hh' : RingHom.IsStandardSmoothOfRelativeDimension d
      (h.appLE (S.basicOpen r) (Z.basicOpen r') e_r').hom := by
    have := hU₀.isLocalization_basicOpen r
    have := hV'.isLocalization_basicOpen r'
    rw [hU₀.appLE_eq_away_map h hV' e' r]
    exact (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves d).away _ _ _ _ hh
  -- shrink the `Z`-chart into `g ⁻¹ᵁ W.basicOpen s`
  have hzg : z ∈ g ⁻¹ᵁ W.basicOpen s := hgzs
  obtain ⟨t, ht, hzt⟩ := hr'aff.exists_basicOpen_le (V := g ⁻¹ᵁ W.basicOpen s) ⟨z, hzg⟩ hzr'
  have htaff : AlgebraicGeometry.IsAffineOpen (Z.basicOpen t) := hr'aff.basicOpen t
  have e_t : Z.basicOpen t ≤ h ⁻¹ᵁ S.basicOpen r := (Z.basicOpen_le t).trans e_r'
  have hh'' : RingHom.IsStandardSmoothOfRelativeDimension d
      (h.appLE (S.basicOpen r) (Z.basicOpen t) e_t).hom := by
    have := hr'aff.isLocalization_basicOpen t
    have heq : h.appLE (S.basicOpen r) (Z.basicOpen t) e_t =
        h.appLE (S.basicOpen r) (Z.basicOpen r') e_r' ≫
          CommRingCat.ofHom (algebraMap Γ(Z, Z.basicOpen r') Γ(Z, Z.basicOpen t)) := by
      simp only [AlgebraicGeometry.Scheme.Hom.appLE, homOfLE_leOfHom, Category.assoc]
      congr
      apply Z.presheaf.map_comp
    rw [heq]
    exact (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
      d).right _ t _ hh'
  -- assemble
  refine ⟨W.basicOpen s, hU₁.basicOpen s, Z.basicOpen t, htaff, hzt, ht, ?_⟩
  rw [← RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero]
  have hcomp : h.appLE (S.basicOpen r) (Z.basicOpen t) e_t =
      q.appLE (S.basicOpen r) (W.basicOpen s) es ≫ g.appLE (W.basicOpen s) (Z.basicOpen t) ht :=
    (AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE g q _ _ _ es ht).symm
  rw [hcomp] at hh''
  exact RingHom.etale_of_isStandardSmoothOfRelativeDimension_of_formallyUnramified
    (q.appLE (S.basicOpen r) (W.basicOpen s) es).hom (g.appLE (W.basicOpen s) (Z.basicOpen t) ht).hom
    d hq' hh'' (AlgebraicGeometry.Omega.formallyUnramified_appLE_of_isZero g hΩ (hU₁.basicOpen s) htaff ht)

end
