import MiyaokaMori.Prelude

/-! # Injectivity of the Kähler differential map under base change for formally smooth algebras

Algebra half of Stacks 02K4 (= Stacks 04B2 / 00TA for the left end): for `R → A → B` with `B`
formally smooth over `A`, the base-change map `B ⊗[A] Ω[A⁄R] → Ω[B⁄R]` is injective.

Source: Stacks 00S2 (Jacobi–Zariski sequence `H_1(L_{B/A}) → B ⊗[A] Ω[A⁄R] → Ω[B⁄R]`, Mathlib
`Algebra.H1Cotangent.exact_δ_mapBaseChange`) together with `H_1(L_{B/A}) = 0` for `B` formally
smooth over `A` (Stacks 031J (6), the field `Algebra.FormallySmooth.subsingleton_h1Cotangent`).
Same argument as Mathlib's `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`.
-/

set_option autoImplicit false

universe u v w

/-- **Left end of the first fundamental exact sequence for a formally smooth algebra** (Stacks 02K4,
affine version 04B2). If `R → A → B` are commutative rings with `B` formally smooth over `A`, then
`B ⊗[A] Ω[A⁄R] → Ω[B⁄R]`, `b ⊗ da ↦ b · d(a)`, is injective.

Proof: the Jacobi–Zariski sequence `H_1(L_{B/A}) --δ--> B ⊗[A] Ω[A⁄R] --mapBaseChange--> Ω[B⁄R]` is
exact (Stacks 00S2), so the kernel of `mapBaseChange` is the image of `δ`; for `B` formally smooth
over `A`, `H_1(L_{B/A})` is a subsingleton, so that image is `0`. -/
theorem KaehlerDifferential.mapBaseChange_injective_of_formallySmooth
    (R : Type u) (A : Type v) (B : Type w) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [Algebra.FormallySmooth A B] :
    Function.Injective (KaehlerDifferential.mapBaseChange R A B) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B x).mp hx
  rw [Subsingleton.elim y 0, map_zero]
