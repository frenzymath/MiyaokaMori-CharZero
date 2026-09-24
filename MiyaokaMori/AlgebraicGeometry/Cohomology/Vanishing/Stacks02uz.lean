import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.ClosedSubspaceCohomology
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks02uw
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks02ux
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.Stacks02ut
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.Stacks02uzExactAux
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks02uzDimensionAux
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.Stacks02uzExtendByZero

/-! # Grothendieck vanishing (Stacks 02UZ)

Grothendieck vanishing (Stacks 02UZ, Tohoku 3.6.5): if a Noetherian topological space `X` has dimension
`≤ d`, then `H^p(X, F) = 0` for every abelian sheaf `F` and every `p > d`.

Source: Stacks 02UZ.

The proof of `sheafCohomology_vanishing_noetherian_dimension` is the Stacks 02UZ induction written out
(namespace `Stacks02uz`), using `TopCat.Sheaf.shortExact_extendByZero_restrict` (Stacks 02UT),
`TopCat.Sheaf.H_pushforwardClosed_equiv` (Stacks 02UV), `TopCat.Sheaf.H_constantSheaf_subsingleton_of_irreducible`
(Stacks 02UW), `TopCat.Sheaf.H_subsingleton_of_extendByZero_constant` (Stacks 02UX), plus the helper modules
`Stacks02uzExactAux`, `Stacks02uzDimensionAux`, `Stacks02uzExtendByZero`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace Stacks02uz

/-- The vanishing statement for a space `T` and a bound `d`: `H^p(T, F) = 0` for every abelian sheaf `F`
and every `p ≥ d`. (`Vanish T (d+1)` is the conclusion of 02UZ for `dim T ≤ d`.) -/
def Vanish (T : Type u) [TopologicalSpace T] (d : ℕ) : Prop :=
  ∀ (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (p : ℕ),
    d ≤ p → Subsingleton (CategoryTheory.Sheaf.H F p)

/-- On the empty space all cohomology vanishes (every sheaf is zero). -/
theorem vanish_of_isEmpty (T : Type u) [TopologicalSpace T] [IsEmpty T] (d : ℕ) : Vanish T d :=
  fun F p _ => CategoryTheory.Sheaf.subsingleton_H_of_isZero (TopCat.Sheaf.isZero_of_isEmpty F) p

/-- **Irreducible case** (Stacks 02UZ, steps "d = 0" and "d > 0" for irreducible `X`), given the statement
for all Noetherian spaces of dimension `< d`. By 02UX it suffices to treat `F = j_!ℤ_V` for opens `V`.
If `V = ∅` the sheaf is zero. Otherwise `0 → j_!(ℤ_T|_V) → ℤ_T → i_*(ℤ_T|_Z) → 0` (02UT, `Z = T ∖ V`),
`H^q(T, ℤ_T) = 0` for `q ≥ 1` (02UW, `T` irreducible), `dim Z < d` (proper closed subset of an irreducible
space), so `H^{q-1}(Z, −) = 0` by the induction hypothesis for `q - 1 ≥ d`, and `i_*` preserves cohomology;
the long exact sequence gives `H^q(T, j_!(ℤ_T|_V)) = 0`, and `ℤ_T|_V ≅ ℤ_V`. -/
theorem vanish_of_irreducibleSpace (d : ℕ)
    (IH : ∀ (T' : Type u) [TopologicalSpace T'] [NoetherianSpace T'],
      topologicalKrullDim T' < d → Vanish T' d)
    (T : Type u) [TopologicalSpace T] [NoetherianSpace T] [IrreducibleSpace T]
    (hT : topologicalKrullDim T < (d + 1 : ℕ)) : Vanish T (d + 1) := by
  intro F p hp
  refine @TopCat.Sheaf.H_subsingleton_of_extendByZero_constant (TopCat.of T) ‹_› d ?_ F p hp
  intro V q hq
  by_cases hV : IsEmpty V
  · exact CategoryTheory.Sheaf.subsingleton_H_of_isZero
      (TopCat.Sheaf.isZero_extendByZero_of_isZero V (TopCat.Sheaf.isZero_of_isEmpty _)) q
  · rw [not_isEmpty_iff] at hV
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    set Z : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u} :=
      (constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) with hZ
    obtain ⟨S, hS, ⟨e₂⟩, ⟨e₁⟩, ⟨e₃⟩⟩ :=
      TopCat.Sheaf.shortExact_extendByZero_restrict (X := TopCat.of T) Z V
    have h2 : Subsingleton (CategoryTheory.Sheaf.H S.X₂ (q' + 1)) :=
      CategoryTheory.Sheaf.subsingleton_H_of_iso e₂.symm _
        (hF := TopCat.Sheaf.H_constantSheaf_subsingleton_of_irreducible (X := TopCat.of T) _ _
          (Nat.succ_pos q'))
    have h3 : Subsingleton (CategoryTheory.Sheaf.H S.X₃ q') := by
      have hne : ((V : Set T)ᶜ) ≠ Set.univ := by
        intro h
        obtain ⟨v⟩ := hV
        have hv : (v : T) ∈ (V : Set T)ᶜ := h ▸ Set.mem_univ _
        exact hv v.2
      have hdim : topologicalKrullDim (((V : Set T)ᶜ : Set T)) < d :=
        topologicalKrullDim_lt_of_isClosed_of_ne_univ V.isOpen.isClosed_compl hne hT
      have hG : Subsingleton (CategoryTheory.Sheaf.H
          (TopCat.Sheaf.restrictClosed (X := TopCat.of T) Z ((V : Set T)ᶜ)) q') :=
        IH _ hdim (TopCat.Sheaf.restrictClosed (X := TopCat.of T) Z ((V : Set T)ᶜ)) q' (by omega)
      obtain ⟨e⟩ := TopCat.Sheaf.H_pushforwardClosed_equiv (X := TopCat.of T) ((V : Set T)ᶜ)
        V.isOpen.isClosed_compl (TopCat.Sheaf.restrictClosed (X := TopCat.of T) Z ((V : Set T)ᶜ)) q'
      have hP : Subsingleton (CategoryTheory.Sheaf.H (TopCat.Sheaf.pushforwardClosed (X := TopCat.of T) ((V : Set T)ᶜ)
          (TopCat.Sheaf.restrictClosed (X := TopCat.of T) Z ((V : Set T)ᶜ))) q') :=
        e.symm.injective.subsingleton
      exact CategoryTheory.Sheaf.subsingleton_H_of_iso e₃.symm _ (hF := hP)
    have h1 : Subsingleton (CategoryTheory.Sheaf.H S.X₁ (q' + 1)) :=
      CategoryTheory.Sheaf.subsingleton_H_X₁_of_shortExact hS q' (q' + 1) rfl
    have h1' : Subsingleton (CategoryTheory.Sheaf.H
        (TopCat.Sheaf.extendByZero (X := TopCat.of T) V (TopCat.Sheaf.restrict (X := TopCat.of T) Z V)) (q' + 1)) :=
      CategoryTheory.Sheaf.subsingleton_H_of_iso e₁ _ (hF := h1)
    exact CategoryTheory.Sheaf.subsingleton_H_of_iso
      ((TopCat.Sheaf.extendByZeroFunctor V).mapIso (TopCat.Sheaf.restrictConstantSheafIso V _)) _
      (hF := h1')

/-- **Two disjoint opens with vanishing closed complements** (the sheaf-theoretic core of the reduction to
irreducible components in Stacks 02UZ): if `U, U'` are disjoint opens of `X` and `H^p(−) = 0` (for `p ≥ n`) on the
closed subspaces `Uᶜ` and `U'ᶜ`, then `H^p(X, F) = 0` for all `F` and `p ≥ n`. Proof: `0 → j_!(F|_U) → F → i_*(F|_{Uᶜ}) → 0`
(02UT); for `F₁ = j_!(F|_U)`, `0 → j'_!(F₁|_{U'}) → F₁ → i'_*(F₁|_{U'ᶜ}) → 0` with `F₁|_{U'} = 0` (support of `j_!`);
closed pushforward preserves cohomology (02UV); two-out-of-three along the long exact sequences. -/
theorem vanish_of_disjoint_opens (X : TopCat.{u}) (U U' : Opens X)
    (hdisj : Disjoint (U : Set X) (U' : Set X)) (n : ℕ)
    (hV₁ : Vanish (((U : Set X)ᶜ : Set X)) n) (hV₂ : Vanish (((U' : Set X)ᶜ : Set X)) n) :
    Vanish X n := by
  intro F p hp
  obtain ⟨S, hS, ⟨e₂⟩, ⟨e₁⟩, ⟨e₃⟩⟩ := TopCat.Sheaf.shortExact_extendByZero_restrict F U
  have h3 : Subsingleton (CategoryTheory.Sheaf.H S.X₃ p) := by
    obtain ⟨e⟩ := TopCat.Sheaf.H_pushforwardClosed_equiv ((U : Set X)ᶜ)
      U.isOpen.isClosed_compl (TopCat.Sheaf.restrictClosed F ((U : Set X)ᶜ)) p
    have hG : Subsingleton (CategoryTheory.Sheaf.H
        (TopCat.Sheaf.restrictClosed F ((U : Set X)ᶜ)) p) := hV₁ _ p hp
    have hP : Subsingleton (CategoryTheory.Sheaf.H (TopCat.Sheaf.pushforwardClosed ((U : Set X)ᶜ)
        (TopCat.Sheaf.restrictClosed F ((U : Set X)ᶜ))) p) :=
      e.symm.injective.subsingleton
    exact CategoryTheory.Sheaf.subsingleton_H_of_iso e₃.symm _ (hF := hP)
  have h1 : Subsingleton (CategoryTheory.Sheaf.H S.X₁ p) := by
    obtain ⟨S', hS', ⟨e₂'⟩, ⟨e₁'⟩, ⟨e₃'⟩⟩ := TopCat.Sheaf.shortExact_extendByZero_restrict
      (TopCat.Sheaf.extendByZero U (TopCat.Sheaf.restrict F U)) U'
    have h1' : Subsingleton (CategoryTheory.Sheaf.H S'.X₁ p) := by
      have hz : IsZero (TopCat.Sheaf.extendByZero U'
          (TopCat.Sheaf.restrict (TopCat.Sheaf.extendByZero U (TopCat.Sheaf.restrict F U)) U')) :=
        TopCat.Sheaf.isZero_extendByZero_of_isZero U'
          (TopCat.Sheaf.isZero_restrict_extendByZero_of_disjoint U _ U' hdisj)
      exact CategoryTheory.Sheaf.subsingleton_H_of_iso e₁'.symm _
        (hF := CategoryTheory.Sheaf.subsingleton_H_of_isZero hz p)
    have h3' : Subsingleton (CategoryTheory.Sheaf.H S'.X₃ p) := by
      obtain ⟨e⟩ := TopCat.Sheaf.H_pushforwardClosed_equiv ((U' : Set X)ᶜ)
        U'.isOpen.isClosed_compl (TopCat.Sheaf.restrictClosed
          (TopCat.Sheaf.extendByZero U (TopCat.Sheaf.restrict F U)) ((U' : Set X)ᶜ)) p
      have hG : Subsingleton (CategoryTheory.Sheaf.H (TopCat.Sheaf.restrictClosed
          (TopCat.Sheaf.extendByZero U (TopCat.Sheaf.restrict F U)) ((U' : Set X)ᶜ)) p) :=
        hV₂ _ p hp
      have hP : Subsingleton (CategoryTheory.Sheaf.H (TopCat.Sheaf.pushforwardClosed ((U' : Set X)ᶜ)
          (TopCat.Sheaf.restrictClosed
            (TopCat.Sheaf.extendByZero U (TopCat.Sheaf.restrict F U)) ((U' : Set X)ᶜ))) p) :=
        e.symm.injective.subsingleton
      exact CategoryTheory.Sheaf.subsingleton_H_of_iso e₃'.symm _ (hF := hP)
    have h2' : Subsingleton (CategoryTheory.Sheaf.H S'.X₂ p) :=
      CategoryTheory.Sheaf.subsingleton_H_X₂_of_shortExact hS' p
    have hF₁ : Subsingleton (CategoryTheory.Sheaf.H
        (TopCat.Sheaf.extendByZero U (TopCat.Sheaf.restrict F U)) p) :=
      CategoryTheory.Sheaf.subsingleton_H_of_iso e₂' p
    exact CategoryTheory.Sheaf.subsingleton_H_of_iso e₁.symm _ (hF := hF₁)
  have h2 : Subsingleton (CategoryTheory.Sheaf.H S.X₂ p) :=
    CategoryTheory.Sheaf.subsingleton_H_X₂_of_shortExact hS p
  exact CategoryTheory.Sheaf.subsingleton_H_of_iso e₂ p

/-- **Induction on the number of irreducible components** (Stacks 02UZ, step "reduce to irreducible"),
given the statement for all Noetherian spaces of dimension `< d`. If `T` is not irreducible and nonempty,
pick an irreducible component `Z₁ ≠ T` and let `W` be the union of the other components (closed, with fewer
components, `T = Z₁ ∪ W`). With `U = T ∖ Z₁`, `U' = T ∖ W ⊆ Z₁` (so `U ∩ U' = ∅`):
`0 → j_!(F|_U) → F → i_*(F|_{Z₁}) → 0` and, for `F₁ = j_!(F|_U)`,
`0 → j'_!(F₁|_{U'}) → F₁ → i'_*(F₁|_W) → 0`, where `F₁|_{U'} = 0` (support of `j_!`), `H^p(Z₁, −) = 0`
(irreducible case) and `H^p(W, −) = 0` (inner induction). -/
theorem vanish_step (d : ℕ)
    (IH : ∀ (T' : Type u) [TopologicalSpace T'] [NoetherianSpace T'],
      topologicalKrullDim T' < d → Vanish T' d) :
    ∀ (c : ℕ) (T : Type u) [TopologicalSpace T] [NoetherianSpace T],
      (irreducibleComponents T).ncard ≤ c → topologicalKrullDim T < (d + 1 : ℕ) →
        Vanish T (d + 1) := by
  intro c
  induction c with
  | zero =>
    intro T _ _ hc hT
    have hfin : (irreducibleComponents T).Finite := NoetherianSpace.finite_irreducibleComponents
    have hempty : irreducibleComponents T = ∅ := (Set.ncard_eq_zero hfin).mp (Nat.le_zero.mp hc)
    have : IsEmpty T := ⟨fun x => by
      have hx := irreducibleComponent_mem_irreducibleComponents x
      rw [hempty] at hx
      exact hx⟩
    exact vanish_of_isEmpty T _
  | succ c ihc =>
    intro T _ _ hc hT
    by_cases hirr : IrreducibleSpace T
    · exact vanish_of_irreducibleSpace d IH T hT
    rcases isEmpty_or_nonempty T with hem | hne
    · exact vanish_of_isEmpty T _
    obtain ⟨x⟩ := hne
    obtain ⟨Z₁, hZ₁def⟩ : ∃ Z₁ : Set T, Z₁ = irreducibleComponent x := ⟨_, rfl⟩
    have hZ₁ : Z₁ ∈ irreducibleComponents T :=
      hZ₁def ▸ irreducibleComponent_mem_irreducibleComponents x
    have hZ₁irr : IsIrreducible Z₁ := hZ₁.1
    have hZ₁cl : IsClosed Z₁ := isClosed_of_mem_irreducibleComponents Z₁ hZ₁
    have hfin : (irreducibleComponents T).Finite := NoetherianSpace.finite_irreducibleComponents
    obtain ⟨W, hWdef⟩ : ∃ W : Set T, W = ⋃₀ (irreducibleComponents T \ {Z₁}) := ⟨_, rfl⟩
    have hWcl : IsClosed W := by
      rw [hWdef, Set.sUnion_eq_biUnion]
      exact (hfin.subset Set.sdiff_subset).isClosed_biUnion
        fun Y hY => isClosed_of_mem_irreducibleComponents Y hY.1
    have hWc : Wᶜ ⊆ Z₁ := by
      have h := closure_sUnion_irreducibleComponents_sdiff_singleton hfin Z₁ hZ₁
      rw [← hWdef] at h
      exact h ▸ subset_closure
    have hcW : (irreducibleComponents W).ncard ≤ c := by
      have h := ncard_irreducibleComponents_sUnion_sdiff_lt hZ₁
      rw [← hWdef] at h
      omega
    let U : Opens T := ⟨Z₁ᶜ, hZ₁cl.isOpen_compl⟩
    let U' : Opens T := ⟨Wᶜ, hWcl.isOpen_compl⟩
    have hdisj : Disjoint (U : Set T) (U' : Set T) := by
      rw [Set.disjoint_left]
      intro y hyU hyU'
      exact hyU (hWc hyU')
    have hV₁ : Vanish (((U : Set T)ᶜ : Set T)) (d + 1) := by
      have hirr' : IrreducibleSpace (((U : Set T)ᶜ : Set T)) := by
        show IrreducibleSpace ((Z₁ᶜᶜ : Set T))
        rw [compl_compl]
        exact Subtype.irreducibleSpace hZ₁irr
      exact vanish_of_irreducibleSpace d IH (((U : Set T)ᶜ : Set T))
        (lt_of_le_of_lt (topologicalKrullDim_subspace_le T _) hT)
    have hV₂ : Vanish (((U' : Set T)ᶜ : Set T)) (d + 1) := by
      refine ihc (((U' : Set T)ᶜ : Set T)) ?_ (lt_of_le_of_lt (topologicalKrullDim_subspace_le T _) hT)
      show (irreducibleComponents ((Wᶜᶜ : Set T))).ncard ≤ c
      rw [compl_compl]
      exact hcW
    exact vanish_of_disjoint_opens (TopCat.of T) U U' hdisj (d + 1) hV₁ hV₂

/-- **Stacks 02UZ by induction on `d`**: every Noetherian space `T` with `dim T < d` satisfies `Vanish T d`.
Base `d = 0`: `dim T < 0` forces `T = ∅`. Step: `vanish_step` (inner induction on the number of irreducible
components, using `vanish_of_irreducibleSpace`). -/
theorem vanish_all (d : ℕ) : ∀ (T : Type u) [TopologicalSpace T] [NoetherianSpace T],
    topologicalKrullDim T < d → Vanish T d := by
  induction d with
  | zero =>
    intro T _ _ hT
    have : IsEmpty T := by
      by_contra h
      rw [not_isEmpty_iff] at h
      obtain ⟨x⟩ := h
      haveI : Nonempty (IrreducibleCloseds T) :=
        ⟨⟨irreducibleComponent x, isIrreducible_irreducibleComponent, isClosed_irreducibleComponent⟩⟩
      rw [Nat.cast_zero] at hT
      exact absurd hT (not_lt.mpr Order.krullDim_nonneg)
    exact vanish_of_isEmpty T 0
  | succ d ih =>
    intro T _ _ hT
    exact vanish_step d ih _ T le_rfl hT

end Stacks02uz

/-- **Grothendieck vanishing** (Stacks 02UZ, cohomology-proposition-vanishing-Noetherian; Grothendieck,
Tohoku 3.6.5): `X` a Noetherian topological space with `dim X ≤ d` ⇒ `H^p(X, F) = 0` for every abelian sheaf
`F` and every `p > d`.

This is the lemma that rules out the infinite-support fallback of the `finsum` in the Euler characteristic
(via `sheafCohomology_subsingleton_of_dimension_lt` in `EulerCharacteristic.lean`: a scheme proper over a
field is a Noetherian space with `topologicalKrullDim X ≤ X.dimension`).

Universes: the `Sheaf.H` here is `Sheaf.H.{u} F p : Type u` under Mathlib's `HasExt.{u}` for Grothendieck
abelian categories; `sheafCohomology` uses the same `HasExt.{u}` (`sheafAddCommGrpHasExt` is a shortcut for
this instance), so the carrier of `sheafCohomology X M i` is **definitionally** `Sheaf.H.{u} M.toAddCommGrpSheaf i`
and this theorem applies by `exact`.

**Proof (Stacks 02UZ; the Lean follows it with the induction reorganised as below).**
Prove, by induction on `d`, that every Noetherian space `T` with `dim T < d` has `H^p(T, F) = 0` for all `F` and
all `p ≥ d` (`Stacks02uz.Vanish T d`). `d = 0`: `dim T < 0` forces `T = ∅`, where every sheaf is zero.
`d → d + 1`: inner induction on the number `c` of irreducible components of `T` (finite, Stacks 0052).
0. Basic tools: for an open `U ⊂ X` with closed complement `Z`, inclusions `j : U → X`, `i : Z → X`, there is a
   short exact sequence `0 → j_!j^*F → F → i_*i^*F → 0` (Stacks 02UT). `j_!j^*F` vanishes on opens disjoint
   from `U` (`isZero_restrict_extendByZero_of_disjoint`, the second half of 02UT). Pushforward along a closed
   subspace preserves cohomology: `H^p(X, i_*G) = H^p(Z, G)` (the topological version of Stacks 02UV). A short
   exact sequence gives the long exact cohomology sequence (`Sheaf.H` = `Ext(ℤ_X, −)`). Closed subspaces of a
   Noetherian space are Noetherian of dimension `≤ d`.
1. **Reduction to the irreducible case**: if `X` is nonempty and irreducible, go to step 2. Otherwise choose
   an irreducible component `Z₁ ≠ X` and let `W` := the union of the other components (closed, with fewer
   components, `X = Z₁ ∪ W`), `U := X ∖ Z₁`, `U′ := X ∖ W ⊆ Z₁` (so `U ∩ U′ = ∅`). For `F`:
   `H^p(i_*F|_{Z₁}) = H^p(Z₁, −) = 0` (irreducible case); for `F₁ := j_!F|_U` apply 02UT once more (to the open
   `U′`): `j′_!(F₁|_{U′}) = 0` (support), `H^p(i′_*F₁|_W) = H^p(W, −) = 0` (induction on the number of
   components), so `H^p(F₁) = 0`; hence `H^p(F) = 0`.
2. **Irreducible case**: by Stacks 02UX it suffices to treat `F = j_!ℤ_V` (`V ⊂ X` open). For `V = ∅`,
   `j_!ℤ_∅ = 0`. Otherwise use `0 → j_!(ℤ_X|_V) → ℤ_X → i_*(ℤ_X|_Z) → 0` (`Z = X ∖ V`): `H^q(X, ℤ_X) = 0` for
   `q ≥ 1` (02UW, `X` irreducible); `Z` is a proper closed subset of an irreducible space, so `dim Z < d`
   (chains of irreducible closed subsets strictly lengthen), and by the outer induction
   `H^{q−1}(X, i_*(ℤ_X|_Z)) = H^{q−1}(Z, ℤ_X|_Z) = 0` (`q − 1 ≥ d`); the long exact sequence
   `H^{q−1}(X, i_*(ℤ_X|_Z)) → H^q(X, j_!(ℤ_X|_V)) → H^q(X, ℤ_X)` has both ends zero for `q > d`, so
   `H^q(X, j_!(ℤ_X|_V)) = 0`, and `ℤ_X|_V ≅ ℤ_V` (`restrictConstantSheafIso`).

Edge cases: for `X` empty, `dim = ⊥ ≤ d` and all cohomology vanishes; `d = 0` with `X` a finite set of points
(discrete or irreducible) is covered by steps 1 and 2; `F = 0` is trivial. -/
theorem sheafCohomology_vanishing_noetherian_dimension {X : TopCat.{u}}
    [NoetherianSpace X] {d : ℕ} (hd : topologicalKrullDim X ≤ d)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (p : ℕ) (hp : d < p) :
    Subsingleton (CategoryTheory.Sheaf.H F p) := by
  have hlt : topologicalKrullDim X < ((d + 1 : ℕ) : WithBot ℕ∞) :=
    lt_of_le_of_lt hd (by exact_mod_cast Nat.lt_succ_self d)
  exact Stacks02uz.vanish_all (d + 1) X hlt F p hp

end
