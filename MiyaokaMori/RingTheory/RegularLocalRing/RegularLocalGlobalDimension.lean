import MiyaokaMori.Prelude
import Mathlib.RingTheory.Regular.ProjectiveDimension
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00o7GlobalDimension

/-! # The global dimension of a regular local ring

**Global dimension of a regular local ring is finite for *all* modules** (Stacks 00OC (3) ⇒ (2);
Stacks 065T `algebra-lemma-finite-gl-dim` / Auslander's theorem; Weibel, *An Introduction to
Homological Algebra*, Thm 4.1.2): if `R` is a regular local ring of dimension `d`, then every
`R`-module `M` (not only the finite ones) has `pd M ≤ d`.

For **finite** `M` this is `IsRegularLocalRing.hasProjectiveDimensionLE_of_finite`
(module `Stacks00o7GlobalDimension`). The content of this file is Auslander's
result "`sup_I pd (R/I) ≤ d ⇒ gl.dim R ≤ d`", proved along the Weibel 4.1.2 route (which matches
Mathlib's `Ext`-based `HasProjectiveDimensionLT`; Stacks 065T instead uses transfinite induction on
generators, 0D1U):

1. `ModuleCat.injective_of_subsingleton_ext_one` — **Baer's criterion in `Ext` form**: if
   `Ext¹(R/I, Y) = 0` for all ideals `I`, then `Y` is injective. The contravariant long exact
   `Ext`-sequence of `0 → I → R → R/I → 0` gives `Hom(R, Y) → Hom(I, Y) → Ext¹(R/I, Y) = 0`, so every
   `I → Y` extends to `R → Y`; Mathlib's `Module.Baer.injective` finishes.
2. `ModuleCat.subsingleton_ext_of_forall_quotient` — **injective dimension shifting**: by induction on
   `d`, "`Ext^{d+1}(R/I, Y) = 0 ∀ I ⇒ Ext^{d+1}(X, Y) = 0 ∀ X`". Base `d = 0` is (1) plus
   `Ext¹(X, injective) = 0`. Step: choose an injective presentation `0 → Y → J → Y' → 0`
   (`EnoughInjectives (ModuleCat R)`); for `k ≥ 1` the covariant sequence
   `Ext^k(Z, J) → Ext^k(Z, Y') → Ext^{k+1}(Z, Y) → Ext^{k+1}(Z, J)` with vanishing outer terms gives
   `Ext^{k+1}(Z, Y) = 0 ⇔ Ext^k(Z, Y') = 0`; apply the induction hypothesis to `Y'`.
3. `IsRegularLocalRing.forall_hasProjectiveDimensionLE_of_ringKrullDim_eq`: for every `M`, apply
   Mathlib `hasProjectiveDimensionLT_of_enoughInjectives` (only `Ext^{d+1}(M, Y) = 0 ∀ Y` is needed),
   which follows from (2) since `pd (R/I) ≤ d` for the finite modules `R/I`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Abelian

noncomputable section

/-- **Baer's criterion in `Ext` form**: an `R`-module `Y` with `Ext¹(R/I, Y) = 0` for every ideal
`I` is an injective object. -/
theorem ModuleCat.injective_of_subsingleton_ext_one {R : Type u} [CommRing R] (Y : ModuleCat.{u} R)
    (h : ∀ I : Ideal R, Subsingleton (Ext (ModuleCat.of R (R ⧸ I)) Y 1)) : Injective Y := by
  have hB : Module.Baer R Y := by
    intro I g
    let S : ShortComplex (ModuleCat.{u} R) :=
      ShortComplex.mk (ModuleCat.ofHom I.subtype) (ModuleCat.ofHom I.mkQ)
        (ModuleCat.hom_ext (LinearMap.ext fun x => by
          simpa using (Submodule.Quotient.mk_eq_zero I).mpr x.2))
    have hS : S.ShortExact :=
      { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr
          (LinearMap.exact_subtype_mkQ I)
        mono_f := (ModuleCat.mono_iff_injective (ModuleCat.ofHom I.subtype)).mpr I.injective_subtype
        epi_g := (ModuleCat.epi_iff_surjective (ModuleCat.ofHom I.mkQ)).mpr (Submodule.mkQ_surjective I) }
    have hI := h I
    have hx : hS.extClass.comp (Ext.mk₀ (ModuleCat.ofHom g)) (zero_add 1) = 0 :=
      Subsingleton.elim _ _
    obtain ⟨x₂, hx₂⟩ := Ext.contravariant_sequence_exact₁ hS Y (Ext.mk₀ (ModuleCat.ofHom g)) (zero_add 1) hx
    obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective _ _).2 x₂
    rw [Ext.mk₀_comp_mk₀] at hx₂
    have hφ := (Ext.mk₀_bijective _ _).1 hx₂
    refine ⟨φ.hom, fun x hx => ?_⟩
    have := congrArg (fun ψ : S.X₁ ⟶ Y => ψ.hom ⟨x, hx⟩) hφ
    simpa [S] using this
  have h1 : Module.Injective R Y := hB.injective
  exact (Module.injective_iff_injective_object R Y).mp h1

/-- **Injective dimension shifting**: if `Ext^{d+1}(R/I, Y) = 0` for all ideals `I`, then
`Ext^{d+1}(X, Y) = 0` for all `X` (induction on `d`; base case Baer, step via an injective
presentation `0 → Y → J → Y' → 0`). -/
theorem ModuleCat.subsingleton_ext_of_forall_quotient {R : Type u} [CommRing R] (d : ℕ) :
    ∀ (Y : ModuleCat.{u} R),
      (∀ I : Ideal R, Subsingleton (Ext (ModuleCat.of R (R ⧸ I)) Y (d + 1))) →
      ∀ X : ModuleCat.{u} R, Subsingleton (Ext X Y (d + 1)) := by
  induction d with
  | zero =>
    intro Y hY X
    have := ModuleCat.injective_of_subsingleton_ext_one Y hY
    exact ⟨fun a b => by rw [Ext.eq_zero_of_injective a, Ext.eq_zero_of_injective b]⟩
  | succ d ih =>
    intro Y hY X
    obtain ⟨p⟩ := EnoughInjectives.presentation Y
    have h : (ShortComplex.mk _ _ (cokernel.condition p.f)).ShortExact :=
      { exact := ShortComplex.exact_cokernel p.f }
    have key : ∀ (Z : ModuleCat.{u} R) (k : ℕ),
        Subsingleton (Ext Z Y (k + 1 + 1)) ↔ Subsingleton (Ext Z (cokernel p.f) (k + 1)) := by
      intro Z k
      constructor
      · intro hs
        have hz : ∀ a : Ext Z (cokernel p.f) (k + 1), a = 0 := by
          intro a
          have ha : a.comp h.extClass rfl = 0 := Subsingleton.elim _ _
          obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ Z h a rfl ha
          rw [← hx, Ext.eq_zero_of_injective x, Ext.zero_comp]
        exact ⟨fun a b => (hz a).trans (hz b).symm⟩
      · intro hs
        have hz : ∀ a : Ext Z Y (k + 1 + 1), a = 0 := by
          intro a
          obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₁ Z h a (Ext.eq_zero_of_injective _) rfl
          rw [← hx, Subsingleton.elim x 0, Ext.zero_comp]
        exact ⟨fun a b => (hz a).trans (hz b).symm⟩
    have hY' : ∀ I : Ideal R, Subsingleton (Ext (ModuleCat.of R (R ⧸ I)) (cokernel p.f) (d + 1)) :=
      fun I => (key _ d).mp (hY I)
    exact (key X d).mpr (ih (cokernel p.f) hY' X)

/-- **Auslander's theorem for a regular local ring** (Stacks 065T + 00O7; Weibel Thm 4.1.2):
if `dim R = d`, every `R`-module has projective dimension `≤ d`. -/
theorem IsRegularLocalRing.forall_hasProjectiveDimensionLE_of_ringKrullDim_eq
    (R : Type u) [CommRing R] [IsRegularLocalRing R] {d : ℕ} (hd : ringKrullDim R = d) :
    ∀ M : ModuleCat.{u} R, HasProjectiveDimensionLE M d := by
  intro M
  apply hasProjectiveDimensionLT_of_enoughInjectives M (d + 1)
  intro Y
  apply ModuleCat.subsingleton_ext_of_forall_quotient d Y
  intro I
  have := IsRegularLocalRing.hasProjectiveDimensionLE_of_finite (R := R) (R ⧸ I) d hd
  exact HasProjectiveDimensionLT.subsingleton (ModuleCat.of R (R ⧸ I)) (d + 1) (d + 1) le_rfl Y

end
