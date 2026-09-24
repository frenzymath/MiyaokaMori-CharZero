import MiyaokaMori.Prelude

/-! # The conormal module of a section via the cotangent complex

Algebraic core of Stacks 0474 (conormal module of a section): for an extension `P` of `R` **over
`R` itself** — a ring `B := P.Ring` with `R → B → R` composing to the identity, e.g. `B = Γ(W)`,
`R = Γ(U)` for a section `s|_U : U → W` of `p|_U : W → U` — the cotangent complex map
`I/I² → R ⊗_B Ω_{B/R}` (`Algebra.Extension.cotangentComplex`, `I := ker (B → R)`) is an
isomorphism of `R`-modules. Consequently an `R`-basis of `R ⊗_B Ω_{B/R}` lifts to elements
`h_i ∈ I` whose classes form a `B/I`-basis of `I/I²`.

Source: Stacks 0474 (and Stacks 00RV / Algebra, Lemma 10.131.4 for the algebraic statement);
§2 of the paper (`I/I² = E^∨|_U`, "lift a basis to n+1 functions in I").

Proof: `H¹` of the naive cotangent complex does not depend on the extension when both
extensions map to each other (`Algebra.Extension.H1Cotangent.equiv`); `P` and the trivial
extension `Extension.self R R` map to each other (via `B → R` and `R → B`), and the trivial
extension has `I = 0`, so `H¹ = 0`, i.e. `cotangentComplex` is injective
(`Algebra.Extension.subsingleton_h1Cotangent`). It is surjective because the complex
`I/I² → R ⊗_B Ω_{B/R} → Ω_{R/R}` is exact (`exact_cotangentComplex_toKaehler`) and `Ω_{R/R} = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u w

open TensorProduct

namespace Algebra.Extension

variable {R : Type u} [CommRing R] (P : Algebra.Extension.{w} R R)

/-- The hom of extensions `P → self R R` given by the structure map `P.Ring → R`. -/
noncomputable def homToSelf : P.Hom (Algebra.Extension.self R R) where
  toRingHom := algebraMap P.Ring R
  toRingHom_algebraMap x := by
    show algebraMap P.Ring R (algebraMap R P.Ring x) = x
    exact (IsScalarTower.algebraMap_apply R P.Ring R x).symm
  algebraMap_toRingHom _ := rfl

/-- The hom of extensions `self R R → P` given by the structure map `R → P.Ring`. -/
noncomputable def selfHom : (Algebra.Extension.self R R).Hom P where
  toRingHom := algebraMap R P.Ring
  toRingHom_algebraMap _ := rfl
  algebraMap_toRingHom x := by
    show algebraMap P.Ring R (algebraMap R P.Ring x) = x
    exact (IsScalarTower.algebraMap_apply R P.Ring R x).symm

theorem ker_self : (Algebra.Extension.self R R).ker = ⊥ := by
  ext x
  simp only [Algebra.Extension.ker, RingHom.mem_ker, Ideal.mem_bot]
  exact Iff.rfl

theorem subsingleton_cotangent_self : Subsingleton (Algebra.Extension.self R R).Cotangent := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  obtain ⟨y, rfl⟩ := Cotangent.mk_surjective y
  have hx : x = 0 := Subtype.ext (by simpa [ker_self] using x.2)
  have hy : y = 0 := Subtype.ext (by simpa [ker_self] using y.2)
  rw [hx, hy]

theorem subsingleton_h1Cotangent_self : Subsingleton (Algebra.Extension.self R R).H1Cotangent := by
  have := subsingleton_cotangent_self (R := R)
  exact ⟨fun a b => Algebra.Extension.h1Cotangentι_ext a b (Subsingleton.elim _ _)⟩

/-- `H¹(L_P) = 0` for every extension of `R` over `R`: it is isomorphic to `H¹` of the trivial
extension. -/
theorem h1Cotangent_subsingleton_of_self : Subsingleton P.H1Cotangent := by
  have := subsingleton_h1Cotangent_self (R := R)
  exact (Algebra.Extension.H1Cotangent.equiv (homToSelf P) (selfHom P)).toEquiv.subsingleton

theorem cotangentComplex_injective_of_self : Function.Injective P.cotangentComplex :=
  (Algebra.Extension.subsingleton_h1Cotangent P).mp (h1Cotangent_subsingleton_of_self P)

theorem cotangentComplex_surjective_of_self : Function.Surjective P.cotangentComplex := by
  have : Subsingleton (KaehlerDifferential R R) :=
    KaehlerDifferential.subsingleton_of_surjective R R (fun x => ⟨x, rfl⟩)
  intro y
  exact (P.exact_cotangentComplex_toKaehler y).mp (Subsingleton.elim _ _)

/-- Stacks 0474, algebraic form: `I/I² ≃ R ⊗_B Ω_{B/R}` for an extension `R → B → R`. -/
noncomputable def cotangentEquivCotangentSpaceOfSelf : P.Cotangent ≃ₗ[R] P.CotangentSpace :=
  LinearEquiv.ofBijective P.cotangentComplex
    ⟨cotangentComplex_injective_of_self P, cotangentComplex_surjective_of_self P⟩

@[simp] theorem cotangentEquivCotangentSpaceOfSelf_apply (x : P.Cotangent) :
    cotangentEquivCotangentSpaceOfSelf P x = P.cotangentComplex x := rfl

/-- Lifting a basis: an `R`-basis of `R ⊗_B Ω_{B/R}` gives elements `h i ∈ I = ker (B → R)` whose
classes `h i mod I²` form a `B ⧸ I`-basis of `I.Cotangent = I/I²`. -/
theorem exists_basis_ker_cotangent_of_basis_cotangentSpace {ι : Type*}
    (b : Module.Basis ι R P.CotangentSpace) :
    ∃ (h : ι → P.Ring) (hmem : ∀ i, h i ∈ P.ker),
      ∃ b' : Module.Basis ι (P.Ring ⧸ P.ker) P.ker.Cotangent,
        ∀ i, b' i = Ideal.toCotangent _ ⟨h i, hmem i⟩ := by
  classical
  let b₁ : Module.Basis ι R P.Cotangent := b.map (cotangentEquivCotangentSpaceOfSelf P).symm
  choose y hy using fun i => Cotangent.mk_surjective (b₁ i)
  refine ⟨fun i => (y i).1, fun i => (y i).2, ?_⟩
  let e : P.Ring ⧸ P.ker ≃+* R := RingHom.quotientKerEquivOfSurjective P.algebraMap_surjective
  let E : P.Cotangent ≃ₗ[R] P.ker.Cotangent :=
    (Algebra.Extension.cotangentEquivCotangentKer (P := P)).restrictScalars R
  have hcompat : ∀ (c : R) (x : P.ker.Cotangent), e.symm c • x = c • x := by
    intro c x
    have h1 : e.symm c = Ideal.Quotient.mk P.ker (algebraMap R P.Ring c) := by
      have := RingHom.quotientKerEquivOfSurjective_symm_apply P.algebraMap_surjective
        (algebraMap R P.Ring c)
      rwa [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_self_apply] at this
    rw [h1, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul, algebraMap_smul]
  refine ⟨(b₁.map E).mapCoeffs e.symm hcompat, fun i => ?_⟩
  rw [Module.Basis.mapCoeffs_apply, Module.Basis.map_apply]
  show (b₁ i).val = _
  rw [← hy i, Cotangent.val_mk]

end Algebra.Extension
