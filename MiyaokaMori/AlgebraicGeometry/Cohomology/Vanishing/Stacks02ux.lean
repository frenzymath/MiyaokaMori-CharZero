import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks01ff
import MiyaokaMori.AlgebraicGeometry.Cohomology.ConstantSheaf.Stacks0a38
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks02uxAux
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks02uxFinGeneratedColimit
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.Stacks02uxExtendByZeroConstantMono

/-! # Reduction of vanishing to the sheaves `j_!ℤ_U` (Stacks 02UX)

Stacks 02UX: on a Noetherian topological space, if `H^p(X, j_!ℤ_U) = 0` for all opens `U` and all `p > d`,
then `H^p(X, F) = 0` for all abelian sheaves `F` and `p > d` (every sheaf is a filtered colimit of extensions
of sheaves of the form `j_!ℤ_U`, and on a Noetherian space cohomology commutes with filtered colimits).

Source: Stacks 02UX (cohomology-lemma-vanishing-generated-one-section).

The proof of `TopCat.Sheaf.H_subsingleton_of_extendByZero_constant` is the Stacks 02UX argument written out
(namespace `Stacks02ux`), using `TopCat.Sheaf.H_colimit_bijective` (Stacks 01FF, cohomology commutes with
filtered colimits), `TopCat.Sheaf.exists_filtration_subsheaf_constant` (Stacks 0A38, finitely generated
subsheaves of `ℤ_X`), `TopCat.Sheaf.exists_filtered_colimit_finGenerated`, plus the modules `Stacks02uxAux`
(two-out-of-three along the `Ext` sequence, jointly epimorphic families, `FinGenerated`),
`Stacks02uxExtendByZeroDesc` (`extendByZeroDesc : (G ⟶ F|_U) → (j_!G ⟶ F)`) and
`Stacks02uxExtendByZeroConstantMono` (the mono `j_!ℤ_U ⟶ ℤ_X`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace Stacks02ux

variable {X : TopCat.{u}} [TopologicalSpace.NoetherianSpace X]

/-- **Reduction to finitely generated subsheaves** (Stacks 02UX, first paragraph, via Stacks 01FF). If every
finitely generated subsheaf `G ⊆ F` has `H^p(G) = 0` for `p > d`, then so does `F`: `F = colim G_j` is a filtered
colimit of such subsheaves, and on a Noetherian space `H^p(colim G_j) = colim H^p(G_j)` (only the surjectivity
half of `H_colimit_bijective` is used). -/
theorem hVanishAbove_of_forall_finGenerated_sub (d : ℕ)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u},
      TopCat.Sheaf.FinGenerated G → (∃ ι : G ⟶ F, Mono ι) → CategoryTheory.Sheaf.HVanishAbove d G) :
    CategoryTheory.Sheaf.HVanishAbove d F := by
  intro p hp
  obtain ⟨J, _, _, G, ⟨e⟩, hG⟩ := TopCat.Sheaf.exists_filtered_colimit_finGenerated F
  have hB : TopologicalSpace.Opens.IsBasis {U : TopologicalSpace.Opens X | IsCompact (U : Set X)} := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro U x hx
    exact ⟨U, TopologicalSpace.NoetherianSpace.isCompact _, hx, le_rfl⟩
  have hsurj := (TopCat.Sheaf.H_colimit_bijective hB G p).1
  have hcolim : Subsingleton (CategoryTheory.Sheaf.H (colimit G) p) := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨j, e', he'⟩ := hsurj x
    have := hF (G.obj j) (hG j).1 (hG j).2 p hp
    rw [← he', Subsingleton.elim e' 0]
    simp
  exact CategoryTheory.Sheaf.subsingleton_H_of_iso e p

/-- **Subsheaves of the constant sheaf** (Stacks 02UX, third paragraph, via Stacks 0A38). If `H^p(j_!ℤ_U) = 0`
for all opens `U` and `p > d`, then every subsheaf `K ⊆ ℤ_X` has `H^p(K) = 0` for `p > d`: reduce to finitely
generated `K'` (previous lemma); such `K'` has a finite filtration `0 = K_0 ⊆ … ⊆ K_n = K'` whose graded pieces
`Q_i` sit in `0 → j'_!ℤ_W → j_!ℤ_V → Q_i → 0` (0A38); two-out-of-three along the long exact sequences, by
induction on `i`. -/
theorem hVanishAbove_of_mono_constant (d : ℕ)
    (hZU : ∀ U : Opens X, CategoryTheory.Sheaf.HVanishAbove d (TopCat.Sheaf.extendByZeroConstant U))
    (K : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (m : K ⟶ (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))) [Mono m] :
    CategoryTheory.Sheaf.HVanishAbove d K := by
  refine hVanishAbove_of_forall_finGenerated_sub d K fun K' hK' hι => ?_
  obtain ⟨ι, hι⟩ := hι
  obtain ⟨r, U, φ, hgen⟩ := hK'
  obtain ⟨n, Fil, ι', t, hmono, hcomm, h0, hiso, hquot⟩ :=
    TopCat.Sheaf.exists_filtration_subsheaf_constant K' (ι ≫ m) U
      (fun a => TopologicalSpace.NoetherianSpace.isCompact _) φ hgen
  have key : ∀ i, i ≤ n → CategoryTheory.Sheaf.HVanishAbove d (Fil i) := by
    intro i
    induction i with
    | zero => intro _; exact CategoryTheory.Sheaf.hVanishAbove_of_isZero h0 d
    | succ i ih =>
      intro hi
      obtain ⟨V, W, -, -, S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := hquot i (by omega)
      have hQ : CategoryTheory.Sheaf.HVanishAbove d (cokernel (t i)) :=
        CategoryTheory.Sheaf.hVanishAbove_of_iso e₃ d
          (CategoryTheory.Sheaf.hVanishAbove_X₃_of_shortExact hS d
            (CategoryTheory.Sheaf.hVanishAbove_of_iso e₁.symm d (hZU W))
            (CategoryTheory.Sheaf.hVanishAbove_of_iso e₂.symm d (hZU V)))
      have := hmono i
      have : Mono (t i) := mono_of_mono_fac (hcomm i)
      have hS' : (ShortComplex.mk (t i) (cokernel.π (t i)) (cokernel.condition _)).ShortExact :=
        { exact := ShortComplex.exact_cokernel _ }
      exact CategoryTheory.Sheaf.hVanishAbove_X₂_of_shortExact hS' d (ih (by omega)) hQ
  have := hiso
  exact CategoryTheory.Sheaf.hVanishAbove_of_iso (asIso (ι' n)) d (key n le_rfl)

/-- **One generator** (Stacks 02UX, third paragraph). A sheaf `F` generated by a single section over `U`, i.e.
a quotient `ψ : j_!ℤ_U ↠ F`, has `H^p(F) = 0` for `p > d`: `0 → K → j_!ℤ_U → F → 0` with `K = ker ψ ⊆ j_!ℤ_U ⊆ ℤ_X`,
so `H^p(K) = 0` for `p > d` (previous lemma), `H^p(j_!ℤ_U) = 0` by hypothesis, and two-out-of-three
(`H^p(j_!ℤ_U) → H^p(F) → H^{p+1}(K)`). -/
theorem hVanishAbove_of_epi_extendByZeroConstant (d : ℕ)
    (hZU : ∀ U : Opens X, CategoryTheory.Sheaf.HVanishAbove d (TopCat.Sheaf.extendByZeroConstant U))
    (U : Opens X) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (ψ : TopCat.Sheaf.extendByZeroConstant U ⟶ F) [Epi ψ] :
    CategoryTheory.Sheaf.HVanishAbove d F := by
  obtain ⟨m, hm⟩ := TopCat.Sheaf.exists_mono_extendByZeroConstant_to_constant U
  have := hm
  have hS : (ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition ψ)).ShortExact :=
    { exact := ShortComplex.exact_kernel ψ }
  exact CategoryTheory.Sheaf.hVanishAbove_X₃_of_shortExact hS d
    (hVanishAbove_of_mono_constant d hZU (kernel ψ) (kernel.ι ψ ≫ m)) (hZU U)

/-- **Finitely many generators** (Stacks 02UX, second paragraph), by induction on the number `n` of generators.
`n = 0`: `F = 0`. `n + 1`: with `F' := im(φ 0)` (a quotient of `j_!ℤ_{U_0}`, one generator) and `F/F'` generated by
the images of `φ 1, …, φ n` (`isJointlyEpi_succ_comp_cokernelπ`), `0 → F' → F → F/F' → 0` and two-out-of-three. -/
theorem hVanishAbove_of_isJointlyEpi (d : ℕ)
    (hZU : ∀ U : Opens X, CategoryTheory.Sheaf.HVanishAbove d (TopCat.Sheaf.extendByZeroConstant U)) :
    ∀ (n : ℕ) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (U : Fin n → Opens X) (φ : ∀ a, TopCat.Sheaf.extendByZeroConstant (U a) ⟶ F),
      IsJointlyEpi φ → CategoryTheory.Sheaf.HVanishAbove d F := by
  intro n
  induction n with
  | zero =>
    intro F U φ hφ
    exact CategoryTheory.Sheaf.hVanishAbove_of_isZero (isZero_of_isJointlyEpi_of_isEmpty φ hφ) d
  | succ n ih =>
    intro F U φ hφ
    have hS : (ShortComplex.mk (image.ι (φ 0)) (cokernel.π (image.ι (φ 0)))
        (cokernel.condition _)).ShortExact :=
      { exact := ShortComplex.exact_cokernel _ }
    refine CategoryTheory.Sheaf.hVanishAbove_X₂_of_shortExact hS d ?_ ?_
    · exact hVanishAbove_of_epi_extendByZeroConstant d hZU (U 0) (image (φ 0)) (factorThruImage (φ 0))
    · exact ih (cokernel (image.ι (φ 0))) (fun a => U a.succ)
        (fun a => φ a.succ ≫ cokernel.π (image.ι (φ 0))) (isJointlyEpi_succ_comp_cokernelπ φ hφ)

end Stacks02ux

/-- **Stacks 02UX** (cohomology-lemma-vanishing-generated-one-section; Tohoku Prop 3.6.1): `X` a Noetherian
topological space, `d ≥ 0`; if `H^p(X, j_!ℤ_U) = 0` for all opens `U` (all quasi-compact on a Noetherian
space) and all `p > d`, then `H^p(X, F) = 0` for all abelian sheaves `F` and `p > d`. This is the reduction
step used in Grothendieck vanishing (`Stacks02uz.vanish_of_irreducibleSpace`).

**Proof (Stacks 02UX; the Lean follows it in the order below).**
Write `Van F` for "`H^p(X, F) = 0` for all `p > d`" (`CategoryTheory.Sheaf.HVanishAbove d F`). `Van` is stable
under isomorphism, holds for `0`, and satisfies two-out-of-three along the long exact `Ext` sequence of a short
exact sequence `0 → F₁ → F₂ → F₃ → 0` (middle term: `H^p F₁ → H^p F₂ → H^p F₃`; right term:
`H^p F₂ → H^p F₃ → H^{p+1} F₁`, using `p + 1 > d`).
1. **Reduction to finitely generated subsheaves.** `F = colim_A F_A` is the filtered colimit of its subsheaves
   generated by finitely many sections (`A` finite subsets of `⨿_U F(U)`); on a Noetherian space (quasi-compact,
   quasi-compact opens form a basis and are stable under intersection) `H^p(X, colim F_A) = colim H^p(X, F_A)`
   (Stacks 01FF), so `Van F` follows from `Van F_A` for all `A`. Here "generated by finitely many sections" is
   `FinGenerated`: a jointly epimorphic family `φ_a : j_{a!}ℤ_{U_a} ⟶ F_A`, `a : Fin r`.
2. **Induction on the number of generators.** `r = 0`: `F = 0`. `r + 1`: `F' := im(φ 0) ⊆ F` is a quotient of
   `j_!ℤ_{U_0}`, and `F/F'` is generated by the images of `φ 1, …, φ r`; `0 → F' → F → F/F' → 0` and
   two-out-of-three reduce to `r = 1`.
3. **One generator.** `ψ : j_!ℤ_U ↠ F`, `K := ker ψ`, `0 → K → j_!ℤ_U → F → 0`. `Van (j_!ℤ_U)` is the hypothesis,
   so it suffices to show `Van K`; `K ⊆ j_!ℤ_U ⊆ ℤ_X` (the second inclusion is
   `exists_mono_extendByZeroConstant_to_constant`).
4. **Subsheaves of `ℤ_X`.** By step 1 reduce to finitely generated `K' ⊆ ℤ_X`. Stacks 0A38 gives a finite
   filtration `0 = K_0 ⊆ K_1 ⊆ … ⊆ K_n = K'` with `0 → j'_!ℤ_W → j_!ℤ_V → K_{i+1}/K_i → 0`; `Van (K_{i+1}/K_i)`
   by the hypothesis and two-out-of-three (right term), then `Van K_{i+1}` from `Van K_i` (middle term), by
   induction on `i`.

Edge cases: for `X` empty all sheaves are zero; `F = 0` is trivial; `d` is arbitrary (the claim is only for
`p > d`); for `U = ∅`, `j_!ℤ_∅ = 0`. -/
theorem TopCat.Sheaf.H_subsingleton_of_extendByZero_constant {X : TopCat.{u}} [TopologicalSpace.NoetherianSpace X]
    (d : ℕ)
    (h : ∀ (U : TopologicalSpace.Opens X) (p : ℕ), d < p →
      Subsingleton (CategoryTheory.Sheaf.H (TopCat.Sheaf.extendByZero U
        ((CategoryTheory.constantSheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift ℤ)))) p))
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (p : ℕ) (hp : d < p) :
    Subsingleton (CategoryTheory.Sheaf.H F p) := by
  have hZU : ∀ U : Opens X, CategoryTheory.Sheaf.HVanishAbove d (TopCat.Sheaf.extendByZeroConstant U) :=
    fun U q hq => h U q hq
  refine Stacks02ux.hVanishAbove_of_forall_finGenerated_sub d F (fun G hG _ => ?_) p hp
  obtain ⟨r, U, φ, hφ⟩ := hG
  exact Stacks02ux.hVanishAbove_of_isJointlyEpi d hZU r G U φ hφ

end
