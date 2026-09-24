import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks09sx
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.Stacks02uzExactAux

/-! # Flasque sheaves are acyclic (Stacks 09SY)

Stacks 09SY: the higher cohomology of a flasque abelian sheaf vanishes, `H^p(X, F) = 0` for `p > 0`
(applied to `F|_U` for an open `U`, this says `RΓ(U, −)` is acyclic on `F`).

Source: Stacks 09SY (cohomology-lemma-flasque-acyclic); Hartshorne III.2.5.

## Route (Hartshorne III.2.5)

Fix a flasque abelian sheaf `F` on the space `X`. The category of abelian sheaves on `Opens X` is
Grothendieck abelian (Mathlib), hence has enough injectives; let `ι : F ⟶ I := Injective.under F`
and `Q := cokernel ι`, so `0 → F → I → Q → 0` is short exact (`ShortComplex.cokernelSequence`).
* `I` is flasque (Stacks 09SX, `TopCat.Sheaf.isFlasque_of_injective`), hence so is `Q`
  (Mathlib `IsFlasque.of_shortExact_of_isFlasque₁₂`).
* `H^1(F) = 0` (`H_one_subsingleton_of_shortExact_of_isFlasque`): by the long exact `Ext`
  sequence, `H^0(I) → H^0(Q) → H^1(F) → H^1(I) = 0`; since `F` is flasque, `Γ(X, I) → Γ(X, Q)` is
  onto (Mathlib `IsFlasque.epi_of_shortExact`, U = ⊤), and `H^0 = Γ(X, −)` naturally
  (Mathlib `Sheaf.H.equiv₀`), so the connecting map `H^0(Q) → H^1(F)` is zero and `H^1(F) = 0`.
* `H^{n+2}(F) = 0`: `H^{n+1}(Q) → H^{n+2}(F) → H^{n+2}(I) = 0` with `H^{n+1}(Q) = 0` by
  induction on `n` applied to the flasque sheaf `Q`
  (`CategoryTheory.Sheaf.subsingleton_H_X₁_of_shortExact`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- `0 → F → Injective.under F → cokernel (Injective.ι F) → 0` is a short exact sequence of
abelian sheaves. -/
theorem cokernelSequence_injectiveι_shortExact
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (ShortComplex.cokernelSequence (Injective.ι F)).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := by
    rw [ShortComplex.cokernelSequence_f]
    exact Injective.ι_mono F
  epi_g := by
    rw [ShortComplex.cokernelSequence_g]
    exact coequalizer.π_epi

/-- Hartshorne III.2.5, first step: in a short exact sequence `0 → F → G → H → 0` of abelian
sheaves with `F` flasque and `H^1(G) = 0`, one has `H^1(F) = 0`. Indeed, by the long exact
sequence `H^0(G) → H^0(H) → H^1(F) → H^1(G) = 0` every class in `H^1(F)` is the image of a class
in `H^0(H) = Γ(X, H)`, and `Γ(X, G) → Γ(X, H)` is surjective because `F` is flasque
(Mathlib `IsFlasque.epi_of_shortExact`), so the connecting map vanishes. -/
theorem H_one_subsingleton_of_shortExact_of_isFlasque
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) [TopCat.Sheaf.IsFlasque S.X₁] [Subsingleton (CategoryTheory.Sheaf.H S.X₂ 1)] :
    Subsingleton (CategoryTheory.Sheaf.H S.X₁ 1) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨x₃, hx₃⟩ :=
    Abelian.Ext.covariant_sequence_exact₁ _ hS x (Subsingleton.elim _ _) (zero_add 1)
  have hepi : Epi (S.g.hom.app (op (⊤ : Opens X))) :=
    TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := ⊤) hS
  rw [AddCommGrpCat.epi_iff_surjective] at hepi
  obtain ⟨y, hy⟩ := hepi (CategoryTheory.Sheaf.H.equiv₀ S.X₃ Limits.isTerminalTop x₃)
  have h2 : CategoryTheory.Sheaf.H.map S.g 0
      ((CategoryTheory.Sheaf.H.equiv₀ S.X₂ Limits.isTerminalTop).symm y) = x₃ := by
    rw [CategoryTheory.Sheaf.H.equiv₀_symm_naturality, hy, AddEquiv.symm_apply_apply]
  rw [← hx₃, ← h2, CategoryTheory.Sheaf.H.map_apply, Abelian.Ext.comp_assoc_of_second_deg_zero,
    hS.comp_extClass, Abelian.Ext.comp_zero]

/-- Induction step data for Stacks 09SY: for every `n`, every flasque abelian sheaf `F` has
`H^{n+1}(F) = 0`. -/
theorem H_succ_subsingleton_of_isFlasque (n : ℕ) :
    ∀ (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      [TopCat.Sheaf.IsFlasque F], Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  induction n with
  | zero =>
    intro F hF
    have hS := cokernelSequence_injectiveι_shortExact F
    have h1 : TopCat.Sheaf.IsFlasque (ShortComplex.cokernelSequence (Injective.ι F)).X₁ := hF
    have h2 : Subsingleton
        (CategoryTheory.Sheaf.H (ShortComplex.cokernelSequence (Injective.ι F)).X₂ (0 + 1)) :=
      inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H (Injective.under F) (0 + 1)))
    exact H_one_subsingleton_of_shortExact_of_isFlasque hS
  | succ n ih =>
    intro F hF
    have hS := cokernelSequence_injectiveι_shortExact F
    have h1 : TopCat.Sheaf.IsFlasque (ShortComplex.cokernelSequence (Injective.ι F)).X₁ := hF
    have hI : TopCat.Sheaf.IsFlasque (ShortComplex.cokernelSequence (Injective.ι F)).X₂ :=
      TopCat.Sheaf.isFlasque_of_injective (Injective.under F)
    have hQ : TopCat.Sheaf.IsFlasque (ShortComplex.cokernelSequence (Injective.ι F)).X₃ :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS
    have h3 : Subsingleton
        (CategoryTheory.Sheaf.H (ShortComplex.cokernelSequence (Injective.ι F)).X₃ (n + 1)) :=
      ih _
    have h2 : Subsingleton
        (CategoryTheory.Sheaf.H (ShortComplex.cokernelSequence (Injective.ι F)).X₂ (n + 1 + 1)) :=
      inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H (Injective.under F) (n + 1 + 1)))
    exact CategoryTheory.Sheaf.subsingleton_H_X₁_of_shortExact hS (n + 1) (n + 1 + 1) rfl

end TopCat.Sheaf

/-- Stacks 09SY: the higher cohomology of a flasque abelian sheaf vanishes (acyclicity of `RΓ(U, -)` for
an open `U` follows by applying this to `F|_U`: the restriction of a flasque sheaf to an open is flasque). -/

theorem TopCat.Sheaf.H_subsingleton_of_isFlasque {X : TopCat.{u}}
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Sheaf.IsFlasque F] (p : ℕ) (hp : 0 < p) :
    Subsingleton (CategoryTheory.Sheaf.H F p) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  exact TopCat.Sheaf.H_succ_subsingleton_of_isFlasque n F

end
