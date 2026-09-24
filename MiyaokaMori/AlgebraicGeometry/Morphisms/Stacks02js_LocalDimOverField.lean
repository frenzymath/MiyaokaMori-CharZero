import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.LocalDimensionOpenEmbedding
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimensionFinite
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.LocalDimension
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks02fx
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks0ha1

/-! # Local dimension at a point over a field: stalk dimension plus transcendence degree

Stacks 0A21(10) in the form needed by 02JS: for `p : Z → Spec k` locally of finite type over a
field `k` and `z ∈ Z`, the (untruncated) local dimension is
`⨅_{U ∋ z} dim U = dim 𝒪_{Z,z} + trdeg_{κ(p z)} κ(z)`,
where `κ(p z)` is the residue field of `Spec k` at the point `p z` (isomorphic to `k`) and
`κ(z)` is a `κ(p z)`-algebra via `p.residueFieldMap z`.

Source: Stacks 0A21(10) = Stacks 02FX applied to `p` itself: `Spec k` has a
single point, so the fibre of `p` over `p z` is `Z`.

Proof. Apply Stacks 02FX to `p` at `z`: in the fibre `Z_{p z} = Z ×_{Spec k} Spec κ(p z)`
at the point `z' = p.asFiber z`, `⨅_{U' ∋ z'} dim U' = dim 𝒪_{Z_{pz},z'} + trdeg_{κ(p z)} κ(z)`.
Then identify the two terms with those of `Z`:
* the fibre inclusion `Z_{p z} → Z` is an embedding (a preimmersion) with image `p⁻¹(p z) = Z`
  (`Spec k` is a point), hence a surjective embedding, hence an open embedding, and the untruncated
  local dimension is invariant under open embeddings
  (`Topology.IsOpenEmbedding.iInf_topologicalKrullDim_opens_eq`);
* by Stacks 0HA1 (`fiber_stalk_iso`), `𝒪_{Z_{pz},z'} ≅ 𝒪_{Z,z} / 𝔪_{p z} 𝒪_{Z,z}`, and the maximal
  ideal `𝔪_{p z}` of `𝒪_{Spec k, p z}` is zero: this stalk is the localization of
  `Γ(Spec k, ⊤) ≅ k` at a prime, and a localization of a field is a field
  (`IsField.localization_map_bijective`). So `𝒪_{Z_{pz},z'} ≅ 𝒪_{Z,z}`.

The module also contains the truncation lemma `coe_localDimension_eq_iInf_of_locallyOfFiniteType`
(for `Z` locally of finite type over a field the untruncated local dimension is a natural number, so
it equals the `ℕ`-valued `localDimension`), stated with an explicit structure morphism so that it can
be applied to the fibre `X_y` over `Spec κ(y)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace IsLocalRing
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

section truncation

variable {Z : Scheme.{u}}

/-- Truncation: if the untruncated local dimension `⨅_{U ∋ z} dim U ∈ WithBot ℕ∞` is not `⊤`, it
equals the `ℕ`-valued `localDimension Z z` (it is never `⊥`: every neighbourhood of `z` is
nonempty). -/
theorem coe_localDimension_eq_iInf_of_ne_top (z : Z)
    (htop : (⨅ U ∈ {U : Z.Opens | z ∈ U}, topologicalKrullDim U) ≠ ⊤) :
    (⨅ U ∈ {U : Z.Opens | z ∈ U}, topologicalKrullDim U) = (localDimension Z z : WithBot ℕ∞) := by
  have hbot : (⨅ U ∈ {U : Z.Opens | z ∈ U}, topologicalKrullDim U) ≠ ⊥ := by
    intro hb
    have h0 : (0 : WithBot ℕ∞) ≤ ⨅ U ∈ {U : Z.Opens | z ∈ U}, topologicalKrullDim U := by
      refine le_iInf₂ fun U hU => ?_
      have : Nonempty (IrreducibleCloseds U) :=
        ⟨⟨closure {(⟨z, hU⟩ : U)}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
      exact Order.krullDim_nonneg
    rw [hb] at h0
    exact absurd h0 (by simp)
  unfold localDimension
  generalize (⨅ U ∈ {U : Z.Opens | z ∈ U}, topologicalKrullDim U) = I at hbot htop
  cases I with
  | bot => exact (hbot rfl).elim
  | coe a =>
    have ha : a ≠ ⊤ := by
      rintro rfl
      exact htop rfl
    rw [WithBot.unbotD_coe]
    exact congrArg (fun z : ℕ∞ => (z : WithBot ℕ∞)) (ENat.natCast_toNat ha).symm

/-- For `p : Z → Spec k` locally of finite type over a field `k`, the untruncated local dimension
at any point is finite: it is bounded by the dimension of an affine open neighbourhood, which is
the Krull dimension of a finite type `k`-algebra (`topologicalKrullDim_affineOpen_ne_top`). -/
theorem iInf_topologicalKrullDim_opens_ne_top_of_locallyOfFiniteType {k : Type u} [Field k]
    (p : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (z : Z) :
    (⨅ U ∈ {U : Z.Opens | z ∈ U}, topologicalKrullDim U) ≠ ⊤ := by
  let _ : Z.Over (Spec (CommRingCat.of k)) := { hom := p }
  have : LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k)) := ‹LocallyOfFiniteType p›
  obtain ⟨_, ⟨V, hV0, rfl⟩, hzV, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hV : IsAffineOpen V := hV0
  have hle : (⨅ U ∈ {U : Z.Opens | z ∈ U}, topologicalKrullDim U) ≤ topologicalKrullDim V :=
    iInf₂_le V hzV
  intro ht
  rw [ht, top_le_iff] at hle
  exact topologicalKrullDim_affineOpen_ne_top (k := k) Z V hV hle

/-- The untruncated local dimension of the fibre `X_{f x}` at `x` is at most that of `X` at `x`:
the fibre is a subspace of `X` (the fibre inclusion is an embedding), and for `U ∋ x` open in `X`
the open `ι⁻¹ U ∋ x'` of the fibre embeds into `U`. -/
theorem iInf_topologicalKrullDim_fiber_le {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    (⨅ U ∈ {U : (f.fiber (f.base x)).Opens | f.asFiber x ∈ U}, topologicalKrullDim U) ≤
      ⨅ U ∈ {U : X.Opens | x ∈ U}, topologicalKrullDim U := by
  refine le_iInf₂ fun U hU => ?_
  have hmem : f.asFiber x ∈ (f.fiberι (f.base x)) ⁻¹ᵁ U := by
    show (f.fiberι (f.base x)).base (f.asFiber x) ∈ U
    rw [Scheme.Hom.fiberι_asFiber]
    exact hU
  refine (iInf₂_le ((f.fiberι (f.base x)) ⁻¹ᵁ U) hmem).trans ?_
  -- the restriction of the embedding `fiberι` to `ι⁻¹ U → U` is inducing
  have hind : Topology.IsInducing
      (fun a : ((f.fiberι (f.base x)) ⁻¹ᵁ U : Set (f.fiber (f.base x))) =>
        (⟨(f.fiberι (f.base x)).base a.1, a.2⟩ : (U : Set X))) := by
    refine Topology.IsInducing.of_comp ?_ continuous_subtype_val ?_
    · exact ((f.fiberι (f.base x)).continuous.comp continuous_subtype_val).subtype_mk _
    · exact (f.fiberι (f.base x)).isEmbedding.isInducing.comp Topology.IsInducing.subtypeVal
  exact hind.topologicalKrullDim_le

end truncation

section field_stalk

variable {k : Type u} [Field k]

/-- The stalk of `Spec k` (`k` a field) at its point is a field: its maximal ideal is zero. -/
theorem maximalIdeal_stalk_Spec_eq_bot (q : Spec (CommRingCat.of k)) :
    maximalIdeal ((Spec (CommRingCat.of k)).presheaf.stalk q) = ⊥ := by
  rw [← IsLocalRing.isField_iff_maximalIdeal_eq]
  have hV : IsAffineOpen (⊤ : (Spec (CommRingCat.of k)).Opens) := isAffineOpen_top _
  let _ : Algebra Γ(Spec (CommRingCat.of k), ⊤) ((Spec (CommRingCat.of k)).presheaf.stalk q) :=
    TopCat.Presheaf.algebra_section_stalk _ (⟨q, trivial⟩ : (⊤ : (Spec (CommRingCat.of k)).Opens))
  have hloc := hV.isLocalization_stalk ⟨q, trivial⟩
  have hfield : IsField Γ(Spec (CommRingCat.of k), ⊤) :=
    MulEquiv.isField (Field.toIsField k)
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv
  have h0 : (0 : Γ(Spec (CommRingCat.of k), ⊤)) ∉ (hV.primeIdealOf ⟨q, trivial⟩).asIdeal.primeCompl :=
    fun h => h (Ideal.zero_mem _)
  have hbij := hfield.localization_map_bijective
    (Rₘ := (Spec (CommRingCat.of k)).presheaf.stalk q) h0
  exact MulEquiv.isField hfield (RingEquiv.ofBijective _ hbij).symm.toMulEquiv

variable {Z : Scheme.{u}}

/-- Over a field, the stalk of the fibre `Z_{p z}` at `z` has the same Krull dimension as the
stalk of `Z` at `z` (in fact they are isomorphic: `𝔪_{p z} = 0`). -/
theorem ringKrullDim_fiber_stalk_eq_over_field (p : Z ⟶ Spec (CommRingCat.of k)) (z : Z) :
    ringKrullDim ((p.fiber (p.base z)).presheaf.stalk (p.asFiber z)) =
      ringKrullDim (Z.presheaf.stalk z) := by
  obtain ⟨e⟩ := p.fiber_stalk_iso z
  rw [ringKrullDim_eq_of_ringEquiv e, maximalIdeal_stalk_Spec_eq_bot, Ideal.map_bot]
  exact ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)

/-- Over a field, the untruncated local dimension of the fibre `Z_{p z}` at `z` equals that of `Z`
at `z`: the fibre inclusion is a surjective embedding, hence an open embedding. -/
theorem iInf_topologicalKrullDim_fiber_eq_over_field (p : Z ⟶ Spec (CommRingCat.of k)) (z : Z) :
    (⨅ U ∈ {U : (p.fiber (p.base z)).Opens | p.asFiber z ∈ U}, topologicalKrullDim U) =
      ⨅ U ∈ {U : Z.Opens | z ∈ U}, topologicalKrullDim U := by
  have hsurj : Function.Surjective (p.fiberι (p.base z)).base := by
    intro z'
    have hmem : z' ∈ Set.range (p.fiberι (p.base z)).base := by
      rw [Scheme.Hom.range_fiberι]
      exact Subsingleton.elim (α := PrimeSpectrum k) _ _
    exact hmem
  have hopen : Topology.IsOpenEmbedding (p.fiberι (p.base z)).base :=
    (p.fiberι (p.base z)).isEmbedding.isOpenEmbedding_of_surjective hsurj
  have h := hopen.iInf_topologicalKrullDim_opens_eq (p.asFiber z)
  rw [Scheme.Hom.fiberι_asFiber] at h
  exact h

/-- **Stacks 0A21(10), residue-field form.** For `p : Z → Spec k` locally of finite type over a
field and `z ∈ Z`: `⨅_{U ∋ z} dim U = dim 𝒪_{Z,z} + trdeg_{κ(p z)} κ(z)`, where `κ(z)` is a
`κ(p z)`-algebra via `p.residueFieldMap z`. Obtained from Stacks 02FX for `p`, whose fibre
over `p z` is `Z` itself. -/
theorem iInf_topologicalKrullDim_opens_eq_stalk_add_trdeg_over_field
    (p : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (z : Z) :
    letI : Algebra ((Spec (CommRingCat.of k)).residueField (p.base z)) (Z.residueField z) :=
      (p.residueFieldMap z).hom.toAlgebra
    (⨅ U ∈ {U : Z.Opens | z ∈ U}, topologicalKrullDim U) =
      ringKrullDim (Z.presheaf.stalk z) +
        (Cardinal.toENat (Algebra.trdeg ((Spec (CommRingCat.of k)).residueField (p.base z))
          (Z.residueField z)) : WithBot ℕ∞) := by
  have h := iInf_topologicalKrullDim_fiber_eq_stalk_add_trdeg p z
  rw [iInf_topologicalKrullDim_fiber_eq_over_field, ringKrullDim_fiber_stalk_eq_over_field] at h
  exact h

end field_stalk

end AlgebraicGeometry

end
