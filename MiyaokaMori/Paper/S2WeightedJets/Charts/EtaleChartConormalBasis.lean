import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundle
import MiyaokaMori.RingTheory.SectionExtensionCotangentEquiv
import MiyaokaMori.Paper.S2WeightedJets.Charts.EtaleChartCotangentSpaceSections
import MiyaokaMori.Paper.S2WeightedJets.Charts.EtaleChartOmegaSectionsFree

/-! # A basis of the conormal module along the seed section

On an affine open `U ⊆ C` on which `E = s^*T_{Z/C}` is trivial, let `W = p⁻¹U` (affine),
`B = Γ(W)`, `σ : B → Γ(U)` the ring map induced by the section `s|_U`, and `I = ker σ` the ideal
of `s(U)`. Then `I/I²` is a free `B/I`-module of rank `n+1`, and one can choose `n+1` elements
`h_i ∈ I` whose classes mod `I²` form a basis (§2.2 of the paper: "the conormal module is
`I/I² = E^∨|_U`; lift a basis to `n+1` functions in `I`").

The top level is assembled from
* `Algebra.Extension.exists_basis_ker_cotangent_of_basis_cotangentSpace`
  (Stacks 0474 in algebraic form, `I/I² ≃ A ⊗_B Ω_{B/A}` for an extension `A → B → A`, and the
  lifting of a basis);
* `etaleChart_omega_sections_free`: `Γ(U, (s^*Ω_{Z/C})|_U)` is free of rank `n+1` over `Γ(U)`;
* `etaleChart_cotangentSpace_equiv_sections`: `A ⊗_B Ω_{B/A} ≃ Γ(U, (s^*Ω_{Z/C})|_U)`
  (Stacks 01US, 01UT, 01I9).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- For a section `s` of `p` (`s ≫ p = 𝟙`), every open `U` satisfies `U ≤ s ⁻¹ᵁ p ⁻¹ᵁ U`
(indeed `s ⁻¹ᵁ p ⁻¹ᵁ U = (s ≫ p) ⁻¹ᵁ U = U`). Used to form the restriction
`s.resLE (p ⁻¹ᵁ U) U : U ⟶ p ⁻¹ᵁ U` of the section to `U`.
(Same statement as `etaleChart_section_le_preimage` in `EtaleChartCotangentSpaceSections`; kept
under this name because downstream statements refer to it.) -/
theorem etaleChart_le_preimage {C Z : AlgebraicGeometry.Scheme.{u}} (p : Z ⟶ C) (s : C ⟶ Z)
    (hs : s ≫ p = CategoryTheory.CategoryStruct.id C) (U : C.Opens) : U ≤ s ⁻¹ᵁ p ⁻¹ᵁ U :=
  etaleChart_section_le_preimage p s hs U

/-- **The conormal module of the section is free of rank `n + 1` on `U`, with a lifted basis.**

Setting: `p : Z ⟶ C` affine with a section `s` which is a closed immersion,
`Zx ⊆ Z` an open containing `s(C)` on which `p` is smooth of relative dimension `n + 1`,
`U ⊆ C` an affine open on which `E := s^*T_{Z/C}` (`coneTangentBundle p s hs`) is trivial (`htriv`).
Write `W := p ⁻¹ᵁ U` (affine, `IsAffineOpen.preimage`), `B := Γ(W, ⊤)`, `A := Γ(U, ⊤)`,
`σ := (s.resLE W U _).appTop : B ⟶ A` (the ring map of the restricted section `U ⟶ W`) and
`I := ker σ`. Conclusion: there are `h : Fin (n+1) → B` with `h i ∈ I` such that the classes
`h i mod I²` form a `B ⧸ I`-basis of `I.Cotangent = I/I²`.

Proof (§2.2 of the paper, made explicit; Stacks 0474 for the identification `I/I² = s^*Ω`).
1. `ι := (p ∣_ U).appTop : A → B` and `σ` satisfy `σ ∘ ι = id` (`s|_U` is a section of `p|_U`,
   `etaleChart_section_appTop_apply`), so `B` is an extension `P := etaleChartExtension p s hs U`
   of `A` over `A` in the sense of `Algebra.Extension`, with `P.ker = I` and
   `P.CotangentSpace = A ⊗_B Ω_{B/A}`.
2. (Stacks 0474, algebraic form — `Algebra.Extension.cotangentEquivCotangentSpaceOfSelf`, proved)
   `I/I² ≃ₗ[A] A ⊗_B Ω_{B/A}`: the naive cotangent complex `I/I² → A ⊗_B Ω_{B/A} → Ω_{A/A} = 0`
   is exact and its `H¹` vanishes because `P` and the trivial extension `A → A → A` map to each
   other.
3. (`etaleChart_omega_sections_free`, proved from `dual_pullback`, `dual_dual`, `dual_restrict`,
   `dual_free_iso`, 01US) `Γ(U, (s^*Ω_{Z/C})|_U)` has an `A`-basis indexed by `Fin (n+1)`: `s^*Ω_{Z/C}`
   is the double dual of itself near `s(C)` (locally free of rank `n+1` there) and its dual is
   `E`, which is trivial on `U`.
4. (`etaleChart_cotangentSpace_equiv_sections`, Stacks 01US + 01UT + 01I9)
   `A ⊗_B Ω_{B/A} ≃ₗ[A] Γ(U, (s^*Ω_{Z/C})|_U)`.
5. Transport the basis of step 3 through step 4 to `A ⊗_B Ω_{B/A}`, then through step 2 to
   `I/I²`; lift each basis vector along the surjection `I → I/I²`
   (`Algebra.Extension.exists_basis_ker_cotangent_of_basis_cotangentSpace`, which also converts
   the `A`-basis into a `B ⧸ I`-basis via `B ⧸ I ≃ A`). (No extra element `e ∈ I` with
   `(1-e)I ⊆ (h)` is needed on this route: the étaleness argument in
   `etaleChart_omega_vanishing` uses Nakayama for `Ω`, not for `I`.)

Edge cases: `U = ⊥` gives the zero ring `B = A = 0`, `I = ⊤`, `I.Cotangent = 0`; over the zero ring
any family indexed by `Fin (n+1)` is a basis of the zero module, so the statement holds.
`n` is arbitrary (`n + 1 ≥ 1`). -/
theorem exists_etaleChart_conormal_basis {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    {Z : AlgebraicGeometry.Scheme.{u}} (p : Z ⟶ C.toScheme) (s : C.toScheme ⟶ Z)
    (hs : s ≫ p = CategoryTheory.CategoryStruct.id C.toScheme)
    [AlgebraicGeometry.IsClosedImmersion s] [AlgebraicGeometry.IsAffineHom p]
    (Zx : Z.Opens) (hsZx : ∀ c, s.base c ∈ Zx) (n : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ p)]
    (U : C.toScheme.affineOpens)
    (htriv : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.1.ι).obj (coneTangentBundle p s hs) ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) (ULift.{u} (Fin (n + 1))))) :
    ∃ (h : ULift.{u} (Fin (n + 1)) → Γ((p ⁻¹ᵁ U.1).toScheme, ⊤))
      (hmem : ∀ i, h i ∈ RingHom.ker
        (s.resLE (p ⁻¹ᵁ U.1) U.1 (etaleChart_le_preimage p s hs U.1)).appTop.hom),
      ∃ b : Module.Basis (ULift.{u} (Fin (n + 1)))
          (Γ((p ⁻¹ᵁ U.1).toScheme, ⊤) ⧸ RingHom.ker
            (s.resLE (p ⁻¹ᵁ U.1) U.1 (etaleChart_le_preimage p s hs U.1)).appTop.hom)
          (RingHom.ker
            (s.resLE (p ⁻¹ᵁ U.1) U.1 (etaleChart_le_preimage p s hs U.1)).appTop.hom).Cotangent,
        ∀ i, b i = Ideal.toCotangent _ ⟨h i, hmem i⟩ := by
  obtain ⟨e⟩ := etaleChart_cotangentSpace_equiv_sections p s hs U.1 U.2
  obtain ⟨b⟩ := etaleChart_omega_sections_free p s Zx hsZx n U.1 htriv
  obtain ⟨h, hmem, b', hb'⟩ :=
    Algebra.Extension.exists_basis_ker_cotangent_of_basis_cotangentSpace
      (etaleChartExtension p s hs U.1) (b.map e.symm)
  exact ⟨h, hmem, b', hb'⟩

end
