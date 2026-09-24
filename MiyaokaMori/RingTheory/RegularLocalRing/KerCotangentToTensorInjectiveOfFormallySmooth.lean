import MiyaokaMori.Prelude
import Mathlib.RingTheory.Smooth.Kaehler

/-! # Injectivity of the conormal-to-cotangent map for formally smooth algebras

Let `R → P → S` be rings with `P → S` surjective, kernel `I`, and `S` **formally smooth over `R`**
(no hypothesis on `P`). Then the conormal map `I/I² → S ⊗[P] Ω_{P/R}`, `[x] ↦ 1 ⊗ dx`, is injective
(in fact split injective).

Source: Stacks 031I (Lemma 10.139.9? — "formally smooth ⇒ the sequence
`0 → I/I² → S ⊗ Ω_{P/R} → Ω_{S/R} → 0` is split exact"); Matsumura, *Commutative Ring Theory*,
Thm. 25.2 / EGA 0_IV 20.5.14 for the local-ring special case `P` local, `S = P/m` its residue field
(that special case is the one used downstream: `0 → m/m² → κ ⊗ Ω_{P/k}` is injective whenever the
residue field `κ` is formally smooth over `k`, e.g. `κ/k` separable, e.g. `k` perfect).

Proof (self-contained, follows Mathlib's `retractionKerCotangentToTensorEquivSection`):
1. `P/I² → S` is surjective with square-zero kernel `I/I²` (`AlgHom.ker_kerSquareLift`,
   `Ideal.cotangentIdeal_square`).
2. `S` formally smooth over `R` ⇒ the identity of `S` lifts along the nilpotent surjection
   `P/I² → S`, i.e. there is an `R`-algebra section `g : S → P/I²`
   (`Algebra.FormallySmooth.liftOfSurjective`).
3. Mathlib's `retractionKerCotangentToTensorEquivSection`: sections of `P/I² → S` correspond
   to `P`-linear retractions `l` of `kerCotangentToTensor R P S : I/I² → S ⊗[P] Ω_{P/R}`;
   `l ∘ kerCotangentToTensor = id` gives injectivity.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

open TensorProduct

noncomputable section

/-- If `P → S` is a surjection of `R`-algebras and `S` is formally smooth over `R`, the conormal
map `I/I² → S ⊗[P] Ω_{P/R}` (`I = ker (P → S)`) is injective. Stacks 031I; no hypothesis on `P`. -/
theorem KaehlerDifferential.kerCotangentToTensor_injective_of_formallySmooth
    (R P S : Type*) [CommRing R] [CommRing P] [CommRing S] [Algebra R P] [Algebra P S]
    [Algebra R S] [IsScalarTower R P S] [Algebra.FormallySmooth R S]
    (hf : Function.Surjective (algebraMap P S)) :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor R P S) := by
  classical
  let f : P →ₐ[R] S := IsScalarTower.toAlgHom R P S
  have hf' : Function.Surjective f.kerSquareLift := by
    intro s
    obtain ⟨p, rfl⟩ := hf s
    exact ⟨Ideal.Quotient.mk _ p, f.kerSquareLift_mk p⟩
  have hnil : IsNilpotent (RingHom.ker f.kerSquareLift.toRingHom) := by
    rw [AlgHom.ker_kerSquareLift]
    exact ⟨2, Ideal.cotangentIdeal_square _⟩
  let g := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R S) f.kerSquareLift hf' hnil
  have hg : f.kerSquareLift.comp g = AlgHom.id R S :=
    Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
  obtain ⟨l, hl⟩ := (retractionKerCotangentToTensorEquivSection (R := R) (P := P) (S := S) hf).symm
    ⟨g, hg⟩
  intro x y hxy
  have hx := LinearMap.congr_fun hl x
  have hy := LinearMap.congr_fun hl y
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hx hy
  rw [← hx, ← hy, hxy]

end
