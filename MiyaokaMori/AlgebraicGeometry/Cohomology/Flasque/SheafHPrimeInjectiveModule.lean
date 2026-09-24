import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafHasextInstance
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks09sx
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafHPrimeOneOfSurjective

/-! # Vanishing of `H'` for injective modules

Let `X` be a scheme, `I` an injective `O_X`-module, `U ⊆ X` open and `p > 0`. Then the cohomology of the
underlying abelian sheaf on `U`, `H'^p(U, I) = Ext^p(ℤ[h_U]^#, I)` (Mathlib's `Sheaf.H'`), vanishes.

Proof sketch:
1. The underlying abelian sheaf of an injective `O_X`-module is flasque (Stacks 09SX,
   `Scheme.Modules.isFlasque_of_injective`).
2. A flasque abelian sheaf `F` has `H'^p(U, F) = 0` for every open `U` and `p > 0`, by induction on `p`:
   choose an injective abelian sheaf `J` with a monomorphism `F → J` and quotient `Q`; `J` is flasque (09SX
   for abelian sheaves), `Q` is flasque (Mathlib `TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂`),
   and `J(U) → Q(U)` is surjective (Mathlib `TopCat.Sheaf.IsFlasque.epi_of_shortExact`). The long exact
   `Ext` sequence (`Abelian.Ext.covariant_sequence_exact₁`), `Ext^p(−, J) = 0`
   (`CategoryTheory.Abelian.Ext.eq_zero_of_injective`) and the lifting lemma of
   `SheafHPrimeOneOfSurjective.lean` (`Hom(ℤ[h_U]^#, J) → Hom(ℤ[h_U]^#, Q)` surjective) give
   `H'^1(U, F) = 0` and `H'^{p+1}(U, F) ≅ H'^p(U, Q)`.
`TopCat.Sheaf.hPrime_subsingleton_of_isFlasque` is the `H'(U)` version of Stacks 09SY.

Source: Stacks 09SX + 09SY (cohomology-lemma-flasque-acyclic).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The short exact sequence `0 → F → J → Q → 0` of an injective hull of a flasque sheaf `F`: `Q` is
flasque and `J(U) → Q(U)` is surjective. -/
theorem TopCat.Sheaf.flasque_setup {X : AlgebraicGeometry.Scheme.{u}}
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Sheaf.IsFlasque F] :
    ∃ (T : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
      (_ : T.ShortExact), T.X₁ = F ∧ Injective T.X₂ ∧ TopCat.Sheaf.IsFlasque T.X₃ ∧
        ∀ U : X.Opens, Function.Surjective (T.g.hom.app (op U)) := by
  let T : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
  have hT : T.ShortExact :=
    { exact := ShortComplex.exact_cokernel (Injective.ι F)
      mono_f := inferInstanceAs (Mono (Injective.ι F))
      epi_g := inferInstanceAs (Epi (cokernel.π (Injective.ι F))) }
  have hinj : Injective T.X₂ := inferInstanceAs (Injective (Injective.under F))
  have h1 : TopCat.Sheaf.IsFlasque T.X₁ := ‹TopCat.Sheaf.IsFlasque F›
  have h2 : TopCat.Sheaf.IsFlasque T.X₂ := TopCat.Sheaf.isFlasque_of_injective T.X₂
  refine ⟨T, hT, rfl, hinj, TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hT, fun U => ?_⟩
  exact (AddCommGrpCat.epi_iff_surjective _).1 (TopCat.Sheaf.IsFlasque.epi_of_shortExact hT)

/-- A flasque abelian sheaf has `H'^p(U, F) = 0` for every open `U` and `p > 0` (the `H'(U)` version of
Stacks 09SY). -/
theorem TopCat.Sheaf.hPrime_subsingleton_of_isFlasque {X : AlgebraicGeometry.Scheme.{u}}
    (p : ℕ) : ∀ (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Sheaf.IsFlasque F] (U : X.Opens), Subsingleton (F.H' (p + 1) U) := by
  induction p with
  | zero =>
    intro F _ U
    obtain ⟨T, hT, rfl, hinj, -, hsurj⟩ := TopCat.Sheaf.flasque_setup F
    exact SheafHPrimeAux.ext_one_subsingleton hT
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free))
      (fun φ => SheafHPrimeAux.exists_lift_of_surjective U _ (hsurj U) φ)
      ⟨fun a b => by rw [CategoryTheory.Abelian.Ext.eq_zero_of_injective a, CategoryTheory.Abelian.Ext.eq_zero_of_injective b]⟩
  | succ p ih =>
    intro F _ U
    obtain ⟨T, hT, rfl, hinj, hQ, -⟩ := TopCat.Sheaf.flasque_setup F
    exact SheafHPrimeAux.ext_succ hT
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free)) (p + 1)
      ⟨fun a b => by rw [CategoryTheory.Abelian.Ext.eq_zero_of_injective a, CategoryTheory.Abelian.Ext.eq_zero_of_injective b]⟩
      (ih T.X₃ U)

theorem AlgebraicGeometry.Scheme.Modules.hPrime_subsingleton_of_injective
    {X : AlgebraicGeometry.Scheme.{u}} (I : X.Modules) [CategoryTheory.Injective I]
    (U : X.Opens) (p : ℕ) (hp : 0 < p) :
    Subsingleton (I.toAddCommGrpSheaf.H' p U) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have : TopCat.Sheaf.IsFlasque I.toAddCommGrpSheaf :=
    AlgebraicGeometry.Scheme.Modules.isFlasque_of_injective I
  exact TopCat.Sheaf.hPrime_subsingleton_of_isFlasque q I.toAddCommGrpSheaf U

end
