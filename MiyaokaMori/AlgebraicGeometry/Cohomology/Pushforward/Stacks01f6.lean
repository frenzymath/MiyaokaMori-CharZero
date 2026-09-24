import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.Stacks01f6DimensionShift
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.PushforwardCohomologyLerayDegeneration
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.Stacks01xkHPrimeOpenSubscheme

/-! # Degenerate Leray spectral sequence (Stacks 01F6)

The degenerate form of the Leray spectral sequence (Stacks 01F4(1), a consequence of 01F2/01F6): if
`H^q(f⁻¹V, F) = 0` for all affine opens `V` of `Y` and all `q > 0` (so `R^q f_*F = 0`), then
`H^p(X, F) ≅ H^p(Y, f_*F)`; relative form: for `g : Y → Z` and an open `W`,
`H^p((g∘f)⁻¹W, F) ≅ H^p(g⁻¹W, f_*F)`.

Source: Stacks 01F6 (cohomology-lemma-relative-Leray), 01F2 (cohomology-lemma-Leray), 01F4
(cohomology-lemma-apply-Leray) (1); Hartshorne III Ex. 8.1.

No spectral sequence and no Ext-adjunction is used; the proof is the dimension-shifting argument of
Hartshorne III.4.5 (p. 222) / Stacks 01F4 ("prove it directly without the spectral sequence"), in the
abstract form `sheafCohomology_addEquiv_of_dimensionShift` (`Stacks01f6DimensionShift.lean`), applied to
the pairs of functors
* absolute form: `T = 𝟭`, `T' = f_*` on `X.Modules`;
* relative form: `T = (−)|_{X'}` with `X' := (g∘f)⁻¹W = f⁻¹(g⁻¹W)`, `T' = ((f_*−)|_{Y'})` with
  `Y' := g⁻¹W` (Mathlib `Scheme.Modules.restrictFunctor`, whose sections over an open `V'` of the open
  subscheme are *definitionally* the sections over the image open; `(f ≫ g) ⁻¹ᵁ W = f ⁻¹ᵁ (g ⁻¹ᵁ W)` is
  `rfl`).

The absolute form is the same statement as `sheafCohomology_pushforward_addEquiv_of_hPrime_vanishing`
(`PushforwardCohomologyLerayDegeneration.lean`), up to the spelling of the hypothesis: here
`H^q(f⁻¹V, F|_{f⁻¹V}) = 0` (absolute cohomology of the open subscheme), there `H'^q(f⁻¹V, F) = 0`
(Mathlib's relative `Sheaf.H'`). The two spellings are identified by Stacks 01E1
(`nonempty_E_linearEquiv_sheafCohomology_restrict`), packaged below as `hPrime_subsingleton_of_restrict`.
So the absolute theorem is a corollary of that version, and the relative theorem runs the abstract
dimension shift with the `H'`-form Leray predicate, reusing the step lemmas
`epi_pushforward_map_of_hPrime_one`, `hPrime_subsingleton_quotient`, `hPrime_subsingleton_of_injective`.

The hypotheses of the abstract lemma for the relative form are verified as follows. `P M` is the
Leray hypothesis `∀ V affine, q > 0, H'^q(f⁻¹V, M) = 0`.
1. Degree 0: `Γ(X', M|_{X'}) = Γ(M, X'.ι(⊤)) = Γ(M, f⁻¹(Y'.ι(⊤))) = Γ(Y', (f_*M)|_{Y'})` (transport along
   the equality of opens `X'.ι ''ᵁ ⊤ = f ⁻¹ᵁ (Y'.ι ''ᵁ ⊤)`, both sides being `f⁻¹Y'`; Mathlib
   `Scheme.Opens.ι_image_top`).
2. For `M ∈ P` take `0 → M → I → R → 0` with `I` injective (`X.Modules` has enough injectives).
   * `T S` is short exact by `shortExact_map_restrictFunctor` (`Stacks01f6RestrictShortExact.lean`).
   * `T' S` is short exact: `f_*` is left exact (right adjoint), and `f_*g` is an epimorphism because
     it is locally surjective on sections over the affine basis of `Y`, using `H'^1(f⁻¹V, M) = 0`
     (`epi_pushforward_map_of_hPrime_one`, `shortExact_map_pushforward`). Then restrict to `Y'`.
   * Middle terms acyclic: `I` is flasque (Stacks 09SX), restrictions and pushforwards of flasque
     sheaves are flasque, flasque sheaves are acyclic (Stacks 09SY); `Stacks01f6RestrictShortExact.lean`
     and `PushforwardCohomologyLerayDegeneration.lean`.
   * `R ∈ P`: `H'^q(f⁻¹V, R) = 0` from `H'^q(f⁻¹V, I) = 0` and `H'^{q+1}(f⁻¹V, M) = 0` by the long
     exact sequence (`hPrime_subsingleton_quotient`, `hPrime_subsingleton_of_injective`).
   * The two cokernel groups `Γ(T R) ⧸ im Γ(T I)` and `Γ(T' R) ⧸ im Γ(T' I)` agree: they are the
     cokernel of the same map `Γ(I, f⁻¹Y') → Γ(R, f⁻¹Y')` written over two equal opens (transport along
     the same equality as in 1).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- **Stacks 01E1, `Subsingleton` form**: `H^q(U, M|_U) = 0` (absolute cohomology of the open
subscheme `U`) implies `H'^q(U, M) = 0` (Mathlib's relative cohomology `Sheaf.H'`). Transport along
the `Γ(X, ⊤)`-linear equivalence `nonempty_E_linearEquiv_sheafCohomology_restrict`. -/
theorem hPrime_subsingleton_of_restrict (M : X.Modules) (U : X.Opens) (q : ℕ)
    (h : Subsingleton (CategoryTheory.Sheaf.H (M.restrict U.ι).toAddCommGrpSheaf q)) :
    Subsingleton (M.toAddCommGrpSheaf.H' q U) := by
  obtain ⟨e⟩ := nonempty_E_linearEquiv_sheafCohomology_restrict M U q
  exact @Equiv.subsingleton _ _ e.toEquiv h

/-- The short exact sequence `0 → M → I → R → 0` with `I = Injective.under M`. -/
def injectiveCokernelShortComplex (M : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M)) (cokernel.condition _)

theorem injectiveCokernelShortComplex_shortExact (M : X.Modules) :
    (injectiveCokernelShortComplex M).ShortExact :=
  { exact := ShortComplex.exact_cokernel (Injective.ι M)
    mono_f := inferInstanceAs (Mono (Injective.ι M))
    epi_g := inferInstanceAs (Epi (cokernel.π (Injective.ι M))) }

theorem injectiveCokernelShortComplex_injective_X₂ (M : X.Modules) :
    Injective (injectiveCokernelShortComplex M).X₂ :=
  inferInstanceAs (Injective (Injective.under M))

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry.Scheme.Modules in
/-- The degenerate form of the Leray spectral sequence (Stacks 01F2 / 01F6): if `H^q(f⁻¹V, F) = 0` for all
affine opens `V` of `Y` and `q > 0` (which implies `R^q f_*F = 0`: `R^q f_*F` is the sheafification of the
presheaf `V ↦ H^q(f⁻¹V, F)`, which vanishes on the affine basis), then `H^p(X, F) ≅ H^p(Y, f_*F)` (absolute
form), and for `g : Y → Z` and an open `W` of `Z`, `H^p((g∘f)⁻¹W, F) ≅ H^p(g⁻¹W, f_*F)` (the relative form
on sections over `W`: comparison of `R^p(g∘f)_*F` with `R^p g_*(f_*F)`). -/

theorem AlgebraicGeometry.sheafCohomology_pushforward_equiv_of_vanishing {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (F : X.Modules)
    (hF : ∀ (V : Y.affineOpens) (q : ℕ), 0 < q →
      Subsingleton (CategoryTheory.Sheaf.H
        (AlgebraicGeometry.Scheme.Modules.restrict F (f ⁻¹ᵁ V.1).ι).toAddCommGrpSheaf q))
    (p : ℕ) :
    Nonempty (CategoryTheory.Sheaf.H F.toAddCommGrpSheaf p ≃+
      CategoryTheory.Sheaf.H ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj F).toAddCommGrpSheaf p) :=
  sheafCohomology_pushforward_addEquiv_of_hPrime_vanishing f p F fun V q hq =>
    hPrime_subsingleton_of_restrict F (f ⁻¹ᵁ V.1) q (hF V q hq)

open AlgebraicGeometry.Scheme.Modules in
theorem AlgebraicGeometry.sheafCohomology_restrict_comp_equiv_of_vanishing
    {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (F : X.Modules)
    (hF : ∀ (V : Y.affineOpens) (q : ℕ), 0 < q →
      Subsingleton (CategoryTheory.Sheaf.H
        (AlgebraicGeometry.Scheme.Modules.restrict F (f ⁻¹ᵁ V.1).ι).toAddCommGrpSheaf q))
    (W : Z.Opens) (p : ℕ) :
    Nonempty (CategoryTheory.Sheaf.H
        (AlgebraicGeometry.Scheme.Modules.restrict F ((f ≫ g) ⁻¹ᵁ W).ι).toAddCommGrpSheaf p ≃+
      CategoryTheory.Sheaf.H
        (AlgebraicGeometry.Scheme.Modules.restrict ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj F)
          (g ⁻¹ᵁ W).ι).toAddCommGrpSheaf p) := by
  have hX : (f ⁻¹ᵁ (g ⁻¹ᵁ W)).ι ''ᵁ ⊤ = f ⁻¹ᵁ ((g ⁻¹ᵁ W).ι ''ᵁ ⊤) := by
    rw [Scheme.Opens.ι_image_top, Scheme.Opens.ι_image_top]
  refine sheafCohomology_addEquiv_of_dimensionShift (restrictFunctor (f ⁻¹ᵁ (g ⁻¹ᵁ W)).ι)
    (pushforward f ⋙ restrictFunctor (g ⁻¹ᵁ W).ι)
    (fun M => ∀ (V : Y.affineOpens) (q : ℕ), 0 < q →
      Subsingleton (M.toAddCommGrpSheaf.H' q (f ⁻¹ᵁ V.1)))
    ?_ ?_ p F (fun V q hq => hPrime_subsingleton_of_restrict F (f ⁻¹ᵁ V.1) q (hF V q hq))
  · intro M _
    exact sections_addEquiv_of_eq M hX
  · intro M hM
    have := injectiveCokernelShortComplex_injective_X₂ M
    have hS := injectiveCokernelShortComplex_shortExact M
    have hepi := epi_pushforward_map_of_hPrime_one f _ hS (fun V => hM V 1 one_pos)
    refine ⟨injectiveCokernelShortComplex M, hS, rfl,
      fun V q hq => hPrime_subsingleton_quotient _ hS _ q
        (hPrime_subsingleton_of_injective _ _ q hq) (hM V (q + 1) (Nat.succ_pos q)),
      shortExact_map_restrictFunctor (f ⁻¹ᵁ (g ⁻¹ᵁ W)).ι hS,
      shortExact_map_restrictFunctor (g ⁻¹ᵁ W).ι (shortExact_map_pushforward f _ hS hepi),
      fun k => ?_, fun k => ?_, sectionsQuotient_addEquiv_of_eq (injectiveCokernelShortComplex M).g hX⟩
    · exact subsingleton_sheafCohomology_restrict_of_injective _ _ k
    · have h1 : TopCat.Sheaf.IsFlasque (injectiveCokernelShortComplex M).X₂.toAddCommGrpSheaf :=
        isFlasque_of_injective _
      have h2 := isFlasque_pushforward f (injectiveCokernelShortComplex M).X₂
      have h3 := isFlasque_restrict (g ⁻¹ᵁ W).ι ((pushforward f).obj (injectiveCokernelShortComplex M).X₂)
      exact subsingleton_sheafCohomology_of_isFlasque
        (((pushforward f).obj (injectiveCokernelShortComplex M).X₂).restrict (g ⁻¹ᵁ W).ι) k

end
