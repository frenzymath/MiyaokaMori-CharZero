import MiyaokaMori.Prelude
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Limits

/-! # Induction principle for quasi-compact opens (Stacks 08DR)

**Stacks 08DR (coherent-lemma-induction-principle), in the form used for Stacks 01XK.**
Let `X` be a quasi-separated scheme and `P` a property of opens of `X`. Assume
(i) `P U` for every affine open `U`;
(ii) if `V` is a quasi-compact open, `W` an affine open, and `P V`, `P W`, `P (V ⊓ W)` hold, then
`P (V ⊔ W)`.
Then `P S` holds for every quasi-compact open `S` (in particular for `S = ⊤` when `X` is quasi-compact).

**Proof** (Stacks 08DR, two stages).
1. *Quasi-compact opens of an affine open.* Let `U` be affine and `T ⊆ U` a quasi-compact open.
   Around each point of `T` there is a basic open `D(f) ⊆ T`, `f ∈ Γ(X, U)`
   (`IsAffineOpen.exists_basicOpen_le`); by compactness `T = D(f₁) ∪ … ∪ D(fₙ)`. We show `P` for every
   finite union of basic opens of `U` by induction on the number `n` of basic opens (for all families
   at once): `n = 0` gives `⊥ = D(0)`, which is affine; for the step write the union as
   `T' ⊔ D(f)` with `T'` a union of `n` basic opens. `P T'` by induction, `P (D f)` by (i)
   (`IsAffineOpen.basicOpen`), and `T' ⊓ D(f) = ⋃ D(fᵢ f)` (`Scheme.basicOpen_mul`) is again a
   union of `n` basic opens, so `P (T' ⊓ D f)` by induction; `T'` is quasi-compact as a finite union of
   affines, so (ii) gives `P (T' ⊔ D f)`.
2. *General case.* `compact_open_induction_on` (Mathlib): it suffices to prove `P ⊥` (affine) and
   `P S → P (S ⊔ U)` for `S` quasi-compact and `U` affine. `S ⊓ U` is quasi-compact because `X` is
   quasi-separated (`QuasiSeparatedSpace.inter_isCompact`) and lies in the affine `U`, so `P (S ⊓ U)`
   by stage 1; `P U` by (i); hence `P (S ⊔ U)` by (ii).

Source: Stacks 08DR. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- A finite union of basic opens of an affine open is quasi-compact. -/
theorem isCompact_finset_sup_basicOpen {U : X.Opens} (hU : IsAffineOpen U)
    (s : Finset Γ(X, U)) : IsCompact ((s.sup fun f => X.basicOpen f : X.Opens) : Set X) := by
  refine Finset.sup_induction (p := fun V : X.Opens => IsCompact (V : Set X)) ?_ ?_ ?_
  · rw [Opens.coe_bot]; exact isCompact_empty
  · intro a ha b hb
    rw [Opens.coe_sup]; exact ha.union hb
  · intro f _
    exact (hU.basicOpen f).isCompact

/-- Stage 1 of Stacks 08DR: `P` holds for every finite union of basic opens of an affine open `U`,
provided `P` holds for affine opens and satisfies the Mayer–Vietoris step (ii). -/
theorem finset_sup_basicOpen_induction (P : X.Opens → Prop)
    (h_aff : ∀ U : X.Opens, IsAffineOpen U → P U)
    (h_step : ∀ V W : X.Opens, IsCompact (V : Set X) → IsAffineOpen W →
      P V → P W → P (V ⊓ W) → P (V ⊔ W))
    {U : X.Opens} (hU : IsAffineOpen U) (s : Finset Γ(X, U)) :
    P (s.sup fun f => X.basicOpen f) := by
  classical
  suffices h : ∀ n : ℕ, ∀ s : Finset Γ(X, U), s.card ≤ n → P (s.sup fun f => X.basicOpen f) from
    h s.card s le_rfl
  intro n
  induction n with
  | zero =>
    intro s hs
    rw [Nat.le_zero, Finset.card_eq_zero] at hs
    subst hs
    rw [Finset.sup_empty]
    refine h_aff ⊥ ?_
    rw [← X.basicOpen_zero U]
    exact hU.basicOpen 0
  | succ n ih =>
    intro s hs
    rcases s.eq_empty_or_nonempty with hs0 | ⟨f, hf⟩
    · subst hs0
      exact ih ∅ (Nat.zero_le n)
    · have hcard : (s.erase f).card ≤ n := by
        have := Finset.card_erase_add_one hf
        omega
      have hsup : (s.sup fun g => X.basicOpen g) =
          ((s.erase f).sup fun g => X.basicOpen g) ⊔ X.basicOpen f := by
        conv_lhs => rw [← Finset.insert_erase hf]
        rw [Finset.sup_insert, sup_comm]
      rw [hsup]
      refine h_step _ _ (isCompact_finset_sup_basicOpen hU _) (hU.basicOpen f) (ih _ hcard)
        (h_aff _ (hU.basicOpen f)) ?_
      have hinf : ((s.erase f).sup fun g => X.basicOpen g) ⊓ X.basicOpen f =
          ((s.erase f).image fun g => g * f).sup fun g => X.basicOpen g := by
        rw [Finset.sup_image, Finset.sup_inf_distrib_right]
        refine Finset.sup_congr rfl fun g _ => ?_
        show X.basicOpen g ⊓ X.basicOpen f = X.basicOpen (g * f)
        rw [X.basicOpen_mul]
      rw [hinf]
      exact ih _ (Finset.card_image_le.trans hcard)

/-- Every quasi-compact open contained in an affine open `U` is a finite union of basic opens of `U`. -/
theorem exists_finset_sup_basicOpen_eq {U : X.Opens} (hU : IsAffineOpen U) (T : X.Opens)
    (hTU : T ≤ U) (hT : IsCompact (T : Set X)) :
    ∃ s : Finset Γ(X, U), (s.sup fun f => X.basicOpen f) = T := by
  classical
  have hpt : ∀ x : T, ∃ f : Γ(X, U), X.basicOpen f ≤ T ∧ (x : X) ∈ X.basicOpen f :=
    fun x => hU.exists_basicOpen_le x (hTU x.2)
  choose f hfle hfmem using hpt
  obtain ⟨t, ht⟩ := hT.elim_finite_subcover (fun x : T => (X.basicOpen (f x) : Set X))
    (fun x => (X.basicOpen (f x)).isOpen)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hfmem ⟨x, hx⟩⟩)
  refine ⟨t.image f, le_antisymm ?_ ?_⟩
  · refine Finset.sup_le fun g hg => ?_
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hg
    exact hfle x
  · intro x hx
    obtain ⟨y, hy⟩ := Set.mem_iUnion₂.1 (ht hx)
    obtain ⟨hyt, hxy⟩ := hy
    have : X.basicOpen (f y) ≤ (t.image f).sup fun g => X.basicOpen g :=
      Finset.le_sup (f := fun g => X.basicOpen g) (Finset.mem_image_of_mem f hyt)
    exact this hxy

/-- **Stacks 08DR** for a quasi-separated scheme `X`: a property of opens which holds for affine
opens and is stable under the Mayer–Vietoris step (ii) holds for every quasi-compact open. -/
theorem compact_open_induction_on_of_quasiSeparated [QuasiSeparatedSpace X] (P : X.Opens → Prop)
    (h_aff : ∀ U : X.Opens, IsAffineOpen U → P U)
    (h_step : ∀ V W : X.Opens, IsCompact (V : Set X) → IsAffineOpen W →
      P V → P W → P (V ⊓ W) → P (V ⊔ W))
    (S : X.Opens) (hS : IsCompact (S : Set X)) : P S := by
  have hbot : P ⊥ := h_aff ⊥ (isAffineOpen_bot X)
  refine compact_open_induction_on S hS hbot ?_
  intro V hV U hPV
  have hinter : IsCompact ((V ⊓ (U : X.Opens) : X.Opens) : Set X) := by
    rw [Opens.coe_inf]
    exact QuasiSeparatedSpace.inter_isCompact _ _ V.isOpen hV U.1.isOpen U.2.isCompact
  obtain ⟨s, hs⟩ := exists_finset_sup_basicOpen_eq U.2 (V ⊓ U) inf_le_right hinter
  refine h_step V U hV U.2 hPV (h_aff U U.2) ?_
  rw [← hs]
  exact finset_sup_basicOpen_induction P h_aff h_step U.2 s

end AlgebraicGeometry.Scheme

end
