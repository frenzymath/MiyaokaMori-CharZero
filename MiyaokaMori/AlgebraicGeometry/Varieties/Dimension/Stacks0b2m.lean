import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.LocalDimensionOpenEmbedding
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimensionFinite
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks02fy
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks02js
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0b7i

/-! # Dimension of a product (Stacks 0B2M)

Stacks 0B2M (2): for locally algebraic schemes `X`, `Y` over a field `k`,
`dim (X ×_k Y) = dim X + dim Y`.

Proof sketch (Stacks 0B2M, part (2) from part (1)), assembled from
`localDimension_flat_additive` (02JS), `localDimension_fiber_baseChange` (02FY) and
`topologicalKrullDim_eq_iSup_localDimension` (0B7I):

1. `p := pullback.snd pX pY : X ×_k Y → Y` is the base change of `pX`; morphisms to the spectrum of a
   field are flat (Mathlib instance, `Spec k` is a one-point integral scheme) and flatness / local
   finite type are stable under base change, so `p` is flat and locally of finite type.
2. For `z ↦ (x, y)`: 02JS gives `dim_z(X ×_k Y) = dim_y Y + dim_z(p⁻¹(y))`; 02FY identifies
   `dim_z(p⁻¹(y))` with the local dimension of the fibre of `pX` over the unique point of `Spec k` at
   `x`; that fibre is `X` itself (its embedding `fiberι` into `X` is a surjective embedding, hence a
   homeomorphism), so `dim_z(X ×_k Y) = dim_x X + dim_y Y` (part (1) of 0B2M).
3. Local dimensions of schemes locally of finite type over a field are finite natural numbers
   (an affine open neighbourhood has finite Krull dimension), so the untruncated local dimension
   `⨅_{U ∋ z} dim U` equals `localDimension` as an element of `WithBot ℕ∞`.
4. 0B7I: `dim = ⨆_z ⨅_{U ∋ z} dim U`; every pair `(x, y)` is hit by some `z`
   (`Scheme.Pullback.exists_preimage_pullback`, as `Spec k` is a single point), and
   `⨆_z (a(fst z) + b(snd z)) = ⨆_x a x + ⨆_y b y` in `WithBot ℕ∞`; if `X` or `Y` is empty so is
   the product and both sides are `⊥`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- Step 3 of the route: for a scheme `Z` locally of finite type over a field `k`, the untruncated
local dimension `⨅_{U ∋ p} dim U ∈ WithBot ℕ∞` at any point is neither `⊥` (every neighbourhood is
nonempty) nor `⊤` (an affine open neighbourhood has finite Krull dimension,
`topologicalKrullDim_affineOpen_ne_top`), hence it equals the `ℕ`-valued `localDimension Z p`.
Compared with `localDimension_spec`, this needs no global finiteness of `dim Z`. -/
theorem iInf_topologicalKrullDim_opens_eq_localDimension_of_locallyOfFiniteType
    {k : Type u} [Field k] (Z : Scheme.{u}) [Z.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k))] (p : Z) :
    (⨅ (U : Z.Opens) (_ : p ∈ U), topologicalKrullDim U) = (localDimension Z p : WithBot ℕ∞) := by
  show (⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U) = (localDimension Z p : WithBot ℕ∞)
  obtain ⟨_, ⟨V, hV0, rfl⟩, hpV, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  have hV : IsAffineOpen V := hV0
  have hle : (⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U) ≤ topologicalKrullDim V :=
    iInf₂_le V hpV
  have hbot : (⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U) ≠ ⊥ := by
    intro hb
    have h0 : (0 : WithBot ℕ∞) ≤ ⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U := by
      refine le_iInf₂ fun U hU => ?_
      have : Nonempty (IrreducibleCloseds U) :=
        ⟨⟨closure {(⟨p, hU⟩ : U)}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
      exact Order.krullDim_nonneg
    rw [hb] at h0
    exact absurd h0 (by simp)
  have htop : (⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U) ≠ ⊤ := by
    intro ht
    rw [ht, top_le_iff] at hle
    exact topologicalKrullDim_affineOpen_ne_top (k := k) Z V hV hle
  unfold localDimension
  generalize (⨅ U ∈ {U : Z.Opens | p ∈ U}, topologicalKrullDim U) = I at hbot htop
  cases I with
  | bot => exact (hbot rfl).elim
  | coe a =>
    have ha : a ≠ ⊤ := by
      rintro rfl
      exact htop rfl
    rw [WithBot.unbotD_coe]
    exact congrArg (fun z : ℕ∞ => (z : WithBot ℕ∞)) (ENat.natCast_toNat ha).symm

/-- Step 2 of the route: the scheme-theoretic fibre of `pX : X → Spec k` over the unique point of
`Spec k` is `X` itself on the level of topological spaces: `fiberι` is an embedding
(`IsPreimmersion`) with range `pX ⁻¹' {pt} = univ`, hence a surjective embedding, hence an open
embedding, and local dimension is invariant under open embeddings
(`Topology.IsOpenEmbedding.iInf_topologicalKrullDim_opens_eq`). -/
theorem localDimension_fiber_over_field {k : Type u} [Field k] {X : Scheme.{u}}
    (pX : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    localDimension (pX.fiber (pX.base x)) (pX.asFiber x) = localDimension X x := by
  have hsurj : Function.Surjective (pX.fiberι (pX.base x)).base := by
    intro x'
    have hmem : x' ∈ Set.range (pX.fiberι (pX.base x)).base := by
      rw [Scheme.Hom.range_fiberι]
      exact Subsingleton.elim (α := PrimeSpectrum k) _ _
    exact hmem
  have hopen : Topology.IsOpenEmbedding (pX.fiberι (pX.base x)).base :=
    (pX.fiberι (pX.base x)).isEmbedding.isOpenEmbedding_of_surjective hsurj
  have h := hopen.iInf_topologicalKrullDim_opens_eq (pX.asFiber x)
  rw [Scheme.Hom.fiberι_asFiber] at h
  have h' : (⨅ U ∈ {U : (pX.fiber (pX.base x)).Opens | pX.asFiber x ∈ U}, topologicalKrullDim U) =
      (⨅ U ∈ {U : X.Opens | x ∈ U}, topologicalKrullDim U) := h
  unfold localDimension
  rw [h']

/-- Step 4 of the route (pure order theory in `WithBot ℕ∞`): if every pair `(x, y)` is hit by some
`z` then `⨆_z (a (f z) + b (g z)) = ⨆_x a x + ⨆_y b y`; if `α` or `β` is empty both sides are `⊥`. -/
private theorem withBot_iSup_add_iSup_eq_of_surjective {α β γ : Type*} (a : α → ℕ) (b : β → ℕ)
    (f : γ → α) (g : γ → β) (hsurj : ∀ x y, ∃ z, f z = x ∧ g z = y) :
    (⨆ z : γ, ((a (f z) + b (g z) : ℕ) : WithBot ℕ∞)) =
      (⨆ x : α, ((a x : ℕ) : WithBot ℕ∞)) + ⨆ y : β, ((b y : ℕ) : WithBot ℕ∞) := by
  cases isEmpty_or_nonempty α with
  | inl hα =>
    have := hα
    have : IsEmpty γ := ⟨fun z => hα.false (f z)⟩
    simp
  | inr hα =>
  cases isEmpty_or_nonempty β with
  | inl hβ =>
    have := hβ
    have : IsEmpty γ := ⟨fun z => hβ.false (g z)⟩
    simp
  | inr hβ =>
  have : Nonempty γ := by
    obtain ⟨x⟩ := hα
    obtain ⟨y⟩ := hβ
    obtain ⟨z, -, -⟩ := hsurj x y
    exact ⟨z⟩
  have e1 : ∀ n : ℕ, ((n : ℕ) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) :=
    fun n => (WithBot.coe_natCast n).symm
  simp_rw [e1]
  rw [← WithBot.coe_iSup (OrderTop.bddAbove _), ← WithBot.coe_iSup (OrderTop.bddAbove _),
    ← WithBot.coe_iSup (OrderTop.bddAbove _), ← WithBot.coe_add, WithBot.coe_inj]
  apply le_antisymm
  · refine iSup_le fun z => ?_
    push_cast
    exact add_le_add (le_iSup (fun x => (a x : ℕ∞)) (f z)) (le_iSup (fun y => (b y : ℕ∞)) (g z))
  · refine ENat.iSup_add_iSup_le fun x y => ?_
    obtain ⟨z, rfl, rfl⟩ := hsurj x y
    refine le_trans ?_ (le_iSup (fun z => ((a (f z) + b (g z) : ℕ) : ℕ∞)) z)
    push_cast
    exact le_rfl

end AlgebraicGeometry

set_option linter.style.haveILetI false in
/-- Stacks 0B2M(2): for schemes `X`, `Y` locally of finite type over a field `k`,
`dim (X ×_k Y) = dim X + dim Y` (in `WithBot ℕ∞`; both sides are `⊥` if `X` or `Y` is empty).
See the module docstring for the route. -/
theorem stacks_0B2M {k : Type u} [Field k] {X Y : AlgebraicGeometry.Scheme.{u}}
    (pX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (pY : Y ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pX] [AlgebraicGeometry.LocallyOfFiniteType pY] :
    topologicalKrullDim ↥(CategoryTheory.Limits.pullback pX pY) =
      topologicalKrullDim X + topologicalKrullDim Y := by
  -- structure-morphism instances needed by the leaves
  letI : X.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) := { hom := pX }
  letI : Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) := { hom := pY }
  letI : (pullback pX pY).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) := { hom := pullback.fst pX pY ≫ pX }
  have : AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := ‹AlgebraicGeometry.LocallyOfFiniteType pX›
  have : AlgebraicGeometry.LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := ‹AlgebraicGeometry.LocallyOfFiniteType pY›
  have : AlgebraicGeometry.LocallyOfFiniteType (pullback pX pY ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    inferInstanceAs (AlgebraicGeometry.LocallyOfFiniteType (pullback.fst pX pY ≫ pX))
  have : Subsingleton (AlgebraicGeometry.Spec (CommRingCat.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have : AlgebraicGeometry.Flat pX := inferInstance
  -- part (1) of 0B2M at a point z ↦ (x, y)
  have hpt : ∀ z : ↥(pullback pX pY),
      (⨅ (U : (pullback pX pY).Opens) (_ : z ∈ U), topologicalKrullDim U) =
        ((localDimension X ((pullback.fst pX pY).base z) +
          localDimension Y ((pullback.snd pX pY).base z) : ℕ) : WithBot ℕ∞) := by
    intro z
    rw [AlgebraicGeometry.iInf_topologicalKrullDim_opens_eq_localDimension_of_locallyOfFiniteType (k := k)
      (pullback pX pY) z]
    have hz : localDimension (pullback pX pY) z =
        localDimension Y ((pullback.snd pX pY).base z) +
          localDimension X ((pullback.fst pX pY).base z) := by
      rw [AlgebraicGeometry.localDimension_flat_additive (k := k) (pullback.snd pX pY) z,
        AlgebraicGeometry.localDimension_fiber_baseChange pX pY z,
        AlgebraicGeometry.localDimension_fiber_over_field pX]
    rw [hz, Nat.add_comm]
  have hX : ∀ x : X, (⨅ (U : X.Opens) (_ : x ∈ U), topologicalKrullDim U) =
      ((localDimension X x : ℕ) : WithBot ℕ∞) :=
    fun x => AlgebraicGeometry.iInf_topologicalKrullDim_opens_eq_localDimension_of_locallyOfFiniteType (k := k) X x
  have hY : ∀ y : Y, (⨅ (U : Y.Opens) (_ : y ∈ U), topologicalKrullDim U) =
      ((localDimension Y y : ℕ) : WithBot ℕ∞) :=
    fun y => AlgebraicGeometry.iInf_topologicalKrullDim_opens_eq_localDimension_of_locallyOfFiniteType (k := k) Y y
  -- every pair (x, y) is hit
  have hsurj : ∀ (x : X) (y : Y), ∃ z : ↥(pullback pX pY),
      (pullback.fst pX pY).base z = x ∧ (pullback.snd pX pY).base z = y := by
    intro x y
    obtain ⟨z, hz1, hz2⟩ :=
      AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback (f := pX) (g := pY) x y
        (Subsingleton.elim (α := PrimeSpectrum k) _ _)
    exact ⟨z, hz1, hz2⟩
  rw [topologicalKrullDim_eq_iSup_localDimension (pullback pX pY),
    topologicalKrullDim_eq_iSup_localDimension X, topologicalKrullDim_eq_iSup_localDimension Y]
  simp_rw [hpt, hX, hY]
  exact AlgebraicGeometry.withBot_iSup_add_iSup_eq_of_surjective (fun x => localDimension X x)
    (fun y => localDimension Y y) (pullback.fst pX pY).base (pullback.snd pX pY).base hsurj

end
