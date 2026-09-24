import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.Stacks01xkInductionPrinciple
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.Stacks01xkAffineBase
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.Stacks01xkHPrimeOpenSubscheme

/-! # Cohomology of the preimage of a basic open is a localization (Stacks 01XJ, 01XK)

The sections form of Stacks 01XJ(1) + 01XK: for `f : X → Spec A` quasi-compact and quasi-separated and `M`
quasi-coherent, for every `g ∈ A` and `q ≥ 0`, `H^q(f⁻¹D(g), M|)` is the localization of the `A`-module
`H^q(X, M)` at the powers of `g`. This is the description on basic opens of "`R^q f_*M` is quasi-coherent
and `R^q f_*M ≅ H^q(X, M)~`" (higher direct images are not objects of this library, hence the statement in
terms of sections).

Source: Stacks 01XJ (coherent-lemma-quasi-coherence-higher-direct-images) (1), 01XK
(coherent-lemma-quasi-coherence-higher-direct-images-application); Hartshorne III.8.5 (`X` Noetherian).

The proof follows Stacks 01XJ (proof paragraphs 1–2: induction principle 08DR + relative Mayer–Vietoris
01EC), for `f` quasi-compact and quasi-separated:
1. `X` is quasi-compact and quasi-separated. Let `Y := f⁻¹D(g) = X.basicOpen (a g)` where
   `a : A → Γ(X, O_X)`. For an open `V ⊆ X` let `P(V)` (`LocProp`) be: for every `q`, the restriction
   `H'^q(V, M) → H'^q(V ∩ Y, M)` (Mathlib `Sheaf.H'` in `Ext` form, `Γ(X, ⊤)`-linear) is the
   localization at the powers of `a g`.
2. `P` holds for affine opens (`Stacks01xkAffineBase.lean`: degree 0 is sections, Stacks 01P7;
   degree ≥ 1 both sides vanish, Stacks 01XB) and satisfies the Mayer–Vietoris step
   `P V, P W, P (V ⊓ W) ⇒ P (V ⊔ W)` (`Stacks01xkMayerVietorisStep.lean`: two Mayer–Vietoris long exact
   sequences, the ladder of restriction maps, the five lemma for localizations).
3. The induction principle 08DR gives `P(⊤)`.
4. `H'^q(⊤, M) ≃ H^q(X, M)` (`sheafCohomologyTopLinearEquiv`) and `H'^q(Y, M) ≃ H^q(Y, M|_Y)`
   (Stacks 01E1) turn `P(⊤)` into the statement, and
   the `Γ(X, ⊤)`-linear localization is converted to an `A`-linear one along `a`
   (`IsLocalizedModule.exists_powers_of_compHom` below).

The separated case also has a Čech proof
(`AlgebraicGeometry.sheafCohomology_preimage_basicOpen_isLocalizedModule_of_isSeparated`, module
`Stacks01xkSeparated`), not used by this module. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Change of the base ring for a localization map: if `φ : M → N` is `R`-linear and a localization
at the powers of `a g` (`a : A → R`), then, for the `A`-module structures induced along `a` (on `N`
along `b = c ∘ a` for a further `c : R → R'`, `N` being an `R'`-module), some `A`-linear map `M → N`
(namely `φ` itself) is a localization at the powers of `g`. -/
theorem IsLocalizedModule.exists_powers_of_compHom {A R R' M N : Type*} [CommRing A] [CommRing R]
    [CommRing R'] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R' N]
    (a : A →+* R) (c : R →+* R') (b : A →+* R') (hb : ∀ x, b x = c (a x)) (g : A)
    (φ : letI : Module R N := Module.compHom N c; M →ₗ[R] N)
    (hφ : letI : Module R N := Module.compHom N c; IsLocalizedModule (Submonoid.powers (a g)) φ) :
    letI : Module A M := Module.compHom M a
    letI : Module A N := Module.compHom N b
    ∃ ψ : M →ₗ[A] N, IsLocalizedModule (Submonoid.powers g) ψ := by
  letI : Module R N := Module.compHom N c
  letI : Module A M := Module.compHom M a
  letI : Module A N := Module.compHom N b
  have hsmulN : ∀ (x : A) (y : N), x • y = a x • y := fun x y => by
    show b x • y = c (a x) • y
    rw [hb]
  have hsmulM : ∀ (x : A) (y : M), x • y = a x • y := fun x y => rfl
  let ψ : M →ₗ[A] N :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := fun x y => by
        rw [RingHom.id_apply, hsmulM, hsmulN]
        exact φ.map_smul (a x) y }
  refine ⟨ψ, ?_⟩
  have hψ : ∀ y, ψ y = φ y := fun _ => rfl
  constructor
  · rintro ⟨s, n, rfl⟩
    have := hφ.map_units ⟨a g ^ n, n, rfl⟩
    rw [Module.End.isUnit_iff] at this ⊢
    have e : ∀ y : N, (algebraMap A (Module.End A N) (g ^ n)) y =
        (algebraMap R (Module.End R N) (a g ^ n)) y := fun y => by
      show (g ^ n) • y = (a g ^ n) • y
      rw [hsmulN, map_pow]
    exact ⟨fun y₁ y₂ h => this.1 (by rw [← e, ← e, h]), fun y => by
      obtain ⟨x, hx⟩ := this.2 y
      exact ⟨x, by rw [e, hx]⟩⟩
  · intro y
    obtain ⟨⟨m, ⟨s, n, rfl⟩⟩, hs⟩ := hφ.surj y
    refine ⟨⟨m, ⟨g ^ n, n, rfl⟩⟩, ?_⟩
    show (g ^ n) • y = φ m
    rw [hsmulN, map_pow]
    exact hs
  · intro m₁ m₂ h
    obtain ⟨⟨s, n, rfl⟩, hs⟩ := hφ.exists_of_eq (x₁ := m₁) (x₂ := m₂) h
    refine ⟨⟨g ^ n, n, rfl⟩, ?_⟩
    show (g ^ n) • m₁ = (g ^ n) • m₂
    rw [hsmulM, hsmulM, map_pow]
    exact hs

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian CategoryTheory.Abelian.Ext

variable {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)

attribute [local instance] smulEndAction ExtAction.module

/-- From `P(⊤)` to the statement on `sheafCohomology`, over `Γ(X, ⊤)`: compose the restriction
`H'^q(⊤) → H'^q(Y)` with `H'^q(⊤) ≃ H^q(X, M)` and `H'^q(Y) ≃ H^q(Y, M|_Y)`. -/
theorem exists_isLocalizedModule_sheafCohomology_restrict_of_locProp_top (S : Submonoid Γ(X, ⊤))
    (Y : X.Opens) (hP : LocProp M S Y ⊤) (q : ℕ) :
    letI : Module Γ(X, ⊤) (AlgebraicGeometry.sheafCohomology Y (M.restrict Y.ι) q) :=
      Module.compHom _ Y.ι.appTop.hom
    ∃ φ : AlgebraicGeometry.sheafCohomology X M q →ₗ[Γ(X, ⊤)]
        AlgebraicGeometry.sheafCohomology Y (M.restrict Y.ι) q,
      IsLocalizedModule S φ := by
  letI : Module Γ(X, ⊤) (AlgebraicGeometry.sheafCohomology Y (M.restrict Y.ι) q) :=
    Module.compHom _ Y.ι.appTop.hom
  obtain ⟨e⟩ := nonempty_E_linearEquiv_sheafCohomology_restrict M Y q
  have h := hP Y le_top (top_inf_eq Y).symm q
  refine ⟨e.toLinearMap ∘ₗ ((precompLinear Γ(X, ⊤) M.toAddCommGrpSheaf
    ((freeSheafFunctor X).map (homOfLE (le_top : Y ≤ ⊤))) q) ∘ₗ (eTopLinearEquiv M q).symm.toLinearMap),
    ?_⟩
  have h2 := IsLocalizedModule.of_linearEquiv_right S _ (eTopLinearEquiv M q).symm (hf := h)
  exact IsLocalizedModule.of_linearEquiv S _ e (hf := h2)

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry.Scheme.Modules CategoryTheory.Abelian.Ext in
/-- The sections form of Stacks 01XJ/01XK: for `f : X → Spec A` quasi-compact and quasi-separated and `M`
quasi-coherent, for every `g ∈ A`, `H^q(f⁻¹D(g), M)` is the localization of `H^q(X, M)` at `g` (as
`A`-modules). This is the description on basic opens of "`R^q f_*M` is quasi-coherent and `≅ H^q(X, M)~`"
(higher direct images are not objects of this library, hence the statement in terms of sections).

**Source.** Stacks 01XJ(1) + 01XK; Hartshorne III.8.5 (Noetherian case).

**Proof.** Mayer–Vietoris induction over the quasi-compact opens of `X` (Stacks 08DR + 01EC), see the
module docstring: `LocProp` holds for affine opens (`locProp_of_isAffineOpen`) and is stable under the
Mayer–Vietoris step (`locProp_sup`), so it holds for `⊤` (`compact_open_induction_on_of_quasiSeparated`);
then `exists_isLocalizedModule_sheafCohomology_restrict_of_locProp_top` and the change of base ring
`IsLocalizedModule.exists_powers_of_compHom`. -/
theorem AlgebraicGeometry.sheafCohomology_preimage_basicOpen_isLocalizedModule {A : Type u} [CommRing A]
    {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (g : A) (q : ℕ) :
    letI : X.Over (AlgebraicGeometry.Spec (CommRingCat.of A)) := ⟨f⟩
    let U : X.Opens := f ⁻¹ᵁ (AlgebraicGeometry.Spec (CommRingCat.of A)).basicOpen
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom g)
    letI : (U : AlgebraicGeometry.Scheme.{u}).Over (AlgebraicGeometry.Spec (CommRingCat.of A)) := ⟨U.ι ≫ f⟩
    ∃ φ : AlgebraicGeometry.sheafCohomology X M q →ₗ[A]
        AlgebraicGeometry.sheafCohomology U (M.restrict U.ι) q,
      IsLocalizedModule (Submonoid.powers g) φ := by
  intro Y
  letI : X.Over (AlgebraicGeometry.Spec (CommRingCat.of A)) := ⟨f⟩
  letI : (Y : AlgebraicGeometry.Scheme.{u}).Over (AlgebraicGeometry.Spec (CommRingCat.of A)) :=
    ⟨Y.ι ≫ f⟩
  set a : A →+* Γ(X, ⊤) := ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom
    with ha
  have hY : Y = X.basicOpen (a g) := AlgebraicGeometry.Scheme.preimage_basicOpen_top f _
  haveI : CompactSpace X := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X := AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated f
  -- the induction
  have hP : LocProp M (Submonoid.powers (a g)) Y ⊤ := by
    rw [hY]
    exact AlgebraicGeometry.Scheme.compact_open_induction_on_of_quasiSeparated
      (LocProp M (Submonoid.powers (a g)) (X.basicOpen (a g)))
      (fun U hU => locProp_of_isAffineOpen M (a g) hU)
      (fun V W _ _ hV hW hVW => locProp_sup M _ _ V W hV hW hVW) ⊤ isCompact_univ
  obtain ⟨φ, hφ⟩ := exists_isLocalizedModule_sheafCohomology_restrict_of_locProp_top M
    (Submonoid.powers (a g)) Y hP q
  exact IsLocalizedModule.exists_powers_of_compHom a Y.ι.appTop.hom
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Y.ι ≫ f).appTop).hom
    (fun _ => rfl) g φ hφ

end
