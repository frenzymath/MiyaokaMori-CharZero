import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Algebra.Exact.Basic
import MiyaokaMori.Algebra.ExteriorPowerMul
import MiyaokaMori.Algebra.ExteriorPowerDetFree

/-! # The determinant wedge map: algebraic core

The **algebraic core** of the determinant wedge map (the free/split special case of the proof of
Stacks 0FJB, used on the stalk at a point).

Let `0 → M' →f M →g M'' → 0` be exact with `f` injective and `σ` a section of `g`, and let `M'`, `M''`
be free with bases `e' : Fin a`, `e'' : Fin b`. Write
`Λ := Module.exteriorPowerDetEquivOfBasis e' e'' eM : ⋀^a M' ⊗ ⋀^b M'' ≃ ⋀^{a+b} M`, where `eM` is the
concatenated basis `(f e'_1, …, f e'_a, σ e''_1, …, σ e''_b)` of `M` (`splitBasis`).

**Key identity** (`detWedge_key`): on `⋀^a M' ⊗ ⋀^b M`,

`Λ ∘ (1 ⊗ ⋀^b g) = wedge multiplication ∘ (⋀^a f ⊗ 1)`.

It immediately gives the two facts needed on stalks for the determinant of a short exact sequence
of locally free sheaves:
* `mul_map_eq_zero_of_map_eq_zero`: `(1 ⊗ ⋀^b g) t = 0 ⇒ wedge((⋀^a f ⊗ 1) t) = 0` (well-definedness);
* `bijective_of_comp_eq`: any `μ` with `μ ∘ (1 ⊗ ⋀^b g) = wedge ∘ (⋀^a f ⊗ 1)` equals `Λ`, hence is
  bijective (isomorphism property).

Proof of the key identity: both sides are linear maps out of `⋀^a M' ⊗ ⋀^b M`, so it suffices to
compare them on generators `ιMulti v ⊗ ιMulti w`. Since `⋀^a M'` is free of rank 1,
`ιMulti v = r • ιMulti e'`, and both sides are linear in the first factor, so we may take `v = e'`.
Then both sides are linear maps on `⋀^b M`, compared on the basis `eM.exteriorPower b` (indexed by
`b`-element subsets `s` of `Fin (a+b)`):
* if `s` contains an index `< a` (some `f e'_j`), then on the left `⋀^b g` sends that factor to
  `g f e'_j = 0`, and on the right the wedge `f e' ∧ eM_s` contains the factor `f e'_j` twice; both are `0`;
* otherwise `s` is exactly the last `b` indices and `eM_s = σ e''`; the left side is
  `Λ(ιMulti e' ⊗ ιMulti (g σ e'')) = Λ(ιMulti e' ⊗ ιMulti e'') = ιMulti eM`
  (`exteriorPowerDetEquivOfBasis_wedge`), the right side is `ιMulti (f e' ++ σ e'') = ιMulti eM`.

Reference: Stacks 0FJB.
-/

set_option autoImplicit false

universe u v w

open scoped TensorProduct

noncomputable section

namespace MiyaokaMori.DetWedgeAlgebra

variable {R : Type u} [CommRing R] {M' M M'' : Type v}
  [AddCommGroup M'] [Module R M'] [AddCommGroup M] [Module R M] [AddCommGroup M''] [Module R M'']
  {a b : ℕ} {f : M' →ₗ[R] M} {g : M →ₗ[R] M''}

/-- Exterior powers preserve surjections: if `g` is surjective so is `⋀^n g` (a pure wedge lifts to
the pure wedge of lifts). -/
theorem exteriorPower_map_surjective {n : ℕ} (hg : Function.Surjective g) :
    Function.Surjective (exteriorPower.map n g) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← exteriorPower.ιMulti_span R n M'', Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  choose w' hw' using fun k => hg (w k)
  refine ⟨exteriorPower.ιMulti R n w', ?_⟩
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext k
  exact hw' k

section Split

variable (hexact : Function.Exact f g) (hf : Function.Injective f) (σ : M'' →ₗ[R] M)
  (hσ : g ∘ₗ σ = LinearMap.id)

/-- The map `(m, p) ↦ f m + σ p`. -/
def splitMap (f : M' →ₗ[R] M) (σ : M'' →ₗ[R] M) : M' × M'' →ₗ[R] M :=
  f ∘ₗ LinearMap.fst R M' M'' + σ ∘ₗ LinearMap.snd R M' M''

theorem splitMap_apply (m : M') (p : M'') : splitMap f σ (m, p) = f m + σ p := rfl

include hσ in
theorem g_σ_apply (p : M'') : g (σ p) = p := LinearMap.congr_fun hσ p

include hexact hf hσ in
theorem splitMap_bijective : Function.Bijective (splitMap f σ) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro ⟨m, p⟩ h
    rw [splitMap_apply] at h
    have hp : p = 0 := by
      have h' := congrArg g h
      rwa [map_add, hexact.apply_apply_eq_zero, zero_add, g_σ_apply σ hσ, map_zero] at h'
    subst hp
    rw [map_zero, add_zero] at h
    have hm : m = 0 := hf (h.trans (map_zero f).symm)
    rw [hm]
    rfl
  · intro m
    have hker : g (m - σ (g m)) = 0 := by rw [map_sub, g_σ_apply σ hσ, sub_self]
    obtain ⟨m', hm'⟩ := (hexact _).mp hker
    exact ⟨(m', g m), by rw [splitMap_apply, hm', sub_add_cancel]⟩

/-- A split short exact sequence gives `M' × M'' ≃ M`, `(m, p) ↦ f m + σ p`. -/
def splitEquiv : (M' × M'') ≃ₗ[R] M :=
  LinearEquiv.ofBijective (splitMap f σ) (splitMap_bijective hexact hf σ hσ)

theorem splitEquiv_apply (m : M') (p : M'') : splitEquiv hexact hf σ hσ (m, p) = f m + σ p := rfl

variable (e' : Module.Basis (Fin a) R M') (e'' : Module.Basis (Fin b) R M'')

/-- The concatenated basis `(f e'_1, …, f e'_a, σ e''_1, …, σ e''_b)` of `M`. -/
def splitBasis : Module.Basis (Fin (a + b)) R M :=
  ((e'.prod e'').reindex finSumFinEquiv).map (splitEquiv hexact hf σ hσ)

theorem splitBasis_castAdd (j : Fin a) :
    splitBasis hexact hf σ hσ e' e'' (Fin.castAdd b j) = f (e' j) := by
  simp only [splitBasis, Module.Basis.map_apply, Module.Basis.reindex_apply,
    finSumFinEquiv_symm_apply_castAdd, Module.Basis.prod_apply, Sum.elim_inl,
    Function.comp_apply, LinearMap.coe_inl]
  rw [splitEquiv_apply, map_zero, add_zero]

theorem splitBasis_natAdd (j : Fin b) :
    splitBasis hexact hf σ hσ e' e'' (Fin.natAdd a j) = σ (e'' j) := by
  simp only [splitBasis, Module.Basis.map_apply, Module.Basis.reindex_apply,
    finSumFinEquiv_symm_apply_natAdd, Module.Basis.prod_apply, Sum.elim_inr,
    Function.comp_apply, LinearMap.coe_inr]
  rw [splitEquiv_apply, map_zero, zero_add]

theorem splitBasis_coe :
    ⇑(splitBasis hexact hf σ hσ e' e'') = Fin.append (f ∘ e') (σ ∘ e'') := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [splitBasis_castAdd, Fin.append_left]; rfl
  · rw [splitBasis_natAdd, Fin.append_right]; rfl

/-- The key identity checked on the basis of `⋀^b M` (the case `v = e'`). -/
theorem key_basis (η : ⋀[R]^b M) :
    Module.exteriorPowerDetEquivOfBasis e' e'' (splitBasis hexact hf σ hσ e' e'')
        (exteriorPower.ιMulti R a e' ⊗ₜ[R] exteriorPower.map b g η) =
      Module.exteriorPowerMul R M a b
        (exteriorPower.map a f (exteriorPower.ιMulti R a e') ⊗ₜ[R] η) := by
  classical
  set eM := splitBasis hexact hf σ hσ e' e'' with heM
  set Λ := Module.exteriorPowerDetEquivOfBasis e' e'' eM with hΛ
  let P : ⋀[R]^b M →ₗ[R] ⋀[R]^(a + b) M :=
    Λ.toLinearMap ∘ₗ TensorProduct.mk R _ _ (exteriorPower.ιMulti R a e') ∘ₗ exteriorPower.map b g
  let Q : ⋀[R]^b M →ₗ[R] ⋀[R]^(a + b) M :=
    Module.exteriorPowerMul R M a b ∘ₗ
      TensorProduct.mk R _ _ (exteriorPower.map a f (exteriorPower.ιMulti R a e'))
  have hPQ : P = Q := by
    apply (eM.exteriorPower b).ext
    intro s
    rw [exteriorPower.basis_apply]
    unfold exteriorPower.ιMulti_family
    set ρ : Fin b → Fin (a + b) := ⇑(Set.powersetCard.ofFinEmbEquiv.symm s) with hρ
    simp only [P, Q, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.mk_apply,
      exteriorPower.map_apply_ιMulti, Module.exteriorPowerMul_ιMulti]
    by_cases hA : ∃ k, (ρ k).val < a
    · obtain ⟨k, hk⟩ := hA
      set j : Fin a := ⟨(ρ k).val, hk⟩ with hj
      have hρk : ρ k = Fin.castAdd b j := Fin.ext rfl
      have hval : eM (ρ k) = f (e' j) := by rw [hρk, heM, splitBasis_castAdd]
      -- the left side is 0
      have hL : exteriorPower.ιMulti R b (⇑g ∘ ⇑eM ∘ ρ) = 0 := by
        apply AlternatingMap.map_coord_zero _ k
        simp only [Function.comp_apply, hval, hexact.apply_apply_eq_zero]
      rw [hL, TensorProduct.tmul_zero, map_zero]
      -- the right side is 0: two equal factors
      symm
      apply AlternatingMap.map_eq_zero_of_eq _ _ (i := Fin.castAdd b j) (j := Fin.natAdd a k)
      · rw [Fin.append_left, Fin.append_right, Function.comp_apply, Function.comp_apply, hval]
      · intro h
        have := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at this
        omega
    · push Not at hA
      -- `s` is exactly the last `b` indices: `ρ = natAdd a`
      have hmem : ∀ i, i ∈ s.1 → ∃ k, ρ k = i := fun i hi =>
        (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr hi
      have hsub : s.1 ⊆ Finset.univ.image (Fin.natAdd a : Fin b → Fin (a + b)) := by
        intro i hi
        obtain ⟨k, rfl⟩ := hmem i hi
        refine Finset.mem_image.mpr ⟨⟨(ρ k).val - a, ?_⟩, Finset.mem_univ _, ?_⟩
        · have := (ρ k).isLt; have := hA k; omega
        · apply Fin.ext
          simp only [Fin.val_natAdd]
          have := hA k
          omega
      have hcard : (Finset.univ.image (Fin.natAdd a : Fin b → Fin (a + b))).card ≤ s.1.card := by
        rw [Finset.card_image_of_injective (s := Finset.univ) (f := (Fin.natAdd a : Fin b → Fin (a + b)))
          (Fin.natAdd_injective _ _), Finset.card_univ,
          Fintype.card_fin, s.2]
      have hs : s.1 = Finset.univ.image (Fin.natAdd a : Fin b → Fin (a + b)) :=
        Finset.eq_of_subset_of_card_le hsub hcard
      have hρ' : (Fin.natAdd a : Fin b → Fin (a + b)) = ρ := by
        rw [hρ, Set.powersetCard.ofFinEmbEquiv_symm_apply]
        exact Finset.orderEmbOfFin_unique s.2
          (fun x => by rw [hs]; exact Finset.mem_image_of_mem _ (Finset.mem_univ x))
          (Fin.strictMono_natAdd a)
      have hcomp : ⇑eM ∘ ρ = ⇑σ ∘ ⇑e'' := by
        funext k
        rw [← hρ', Function.comp_apply, Function.comp_apply, heM, splitBasis_natAdd]
      have hg : ⇑g ∘ ⇑eM ∘ ρ = ⇑e'' := by
        rw [hcomp]; funext k; simp only [Function.comp_apply, g_σ_apply σ hσ]
      rw [hg, hΛ, Module.exteriorPowerDetEquivOfBasis_wedge, hcomp, ← splitBasis_coe hexact hf σ hσ]
  exact LinearMap.congr_fun hPQ η

/-- Two linear maps out of `⋀^a M' ⊗ ⋀^b M` agreeing on tensors of pure wedges are equal
(the two-module version of `Module.exteriorPowerMul_hom_ext`). -/
theorem tensor_exterior_hom_ext {P : Type w} [AddCommGroup P] [Module R P]
    {φ ψ : ((⋀[R]^a M') ⊗[R] (⋀[R]^b M)) →ₗ[R] P}
    (h : ∀ (v : Fin a → M') (w : Fin b → M),
      φ (exteriorPower.ιMulti R a v ⊗ₜ[R] exteriorPower.ιMulti R b w) =
        ψ (exteriorPower.ιMulti R a v ⊗ₜ[R] exteriorPower.ιMulti R b w)) :
    φ = ψ := by
  apply TensorProduct.curry_injective
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v => ?_)
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun w => ?_)
  exact h v w

/-- **Key identity**: `Λ ∘ (1 ⊗ ⋀^b g) = wedge multiplication ∘ (⋀^a f ⊗ 1)` on `⋀^a M' ⊗ ⋀^b M`. -/
theorem detWedge_key :
    (Module.exteriorPowerDetEquivOfBasis e' e'' (splitBasis hexact hf σ hσ e' e'')).toLinearMap ∘ₗ
        TensorProduct.map LinearMap.id (exteriorPower.map b g) =
      Module.exteriorPowerMul R M a b ∘ₗ TensorProduct.map (exteriorPower.map a f) LinearMap.id := by
  refine tensor_exterior_hom_ext fun v w => ?_
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe]
  -- write `ιMulti v` as `r • ιMulti e'`
  set r := MiyaokaMori.Algebra.TopExteriorBasis.topExteriorEquiv e' (exteriorPower.ιMulti R a v) with hr
  have hv : exteriorPower.ιMulti R a v = r • exteriorPower.ιMulti R a e' := by
    rw [hr, ← MiyaokaMori.Algebra.TopExteriorBasis.topExteriorEquiv_symm_apply,
      LinearEquiv.symm_apply_apply]
  rw [hv, ← TensorProduct.smul_tmul' r (exteriorPower.ιMulti R a e')
      (exteriorPower.map b g (exteriorPower.ιMulti R b w)),
    LinearEquiv.map_smul, LinearMap.map_smul (exteriorPower.map a f),
    ← TensorProduct.smul_tmul' r _ (exteriorPower.ιMulti R b w), LinearMap.map_smul]
  exact congrArg (r • ·) (key_basis hexact hf σ hσ e' e'' (exteriorPower.ιMulti R b w))

include hexact hf σ hσ e' e'' in
/-- Well-definedness: `(1 ⊗ ⋀^b g) t = 0 ⇒ wedge multiplication ((⋀^a f ⊗ 1) t) = 0`. -/
theorem mul_map_eq_zero_of_map_eq_zero (t : (⋀[R]^a M') ⊗[R] (⋀[R]^b M))
    (ht : TensorProduct.map LinearMap.id (exteriorPower.map b g) t = 0) :
    Module.exteriorPowerMul R M a b (TensorProduct.map (exteriorPower.map a f) LinearMap.id t) = 0 := by
  have h := LinearMap.congr_fun (detWedge_key hexact hf σ hσ e' e'') t
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  rw [← h, ht, map_zero]

include hexact hf σ hσ e' e'' in
/-- Isomorphism property: a `μ` with `μ ∘ (1 ⊗ ⋀^b g) = wedge multiplication ∘ (⋀^a f ⊗ 1)` is
bijective (it equals `Λ`). -/
theorem bijective_of_comp_eq (hg : Function.Surjective g)
    (μ : (⋀[R]^a M') ⊗[R] (⋀[R]^b M'') →ₗ[R] ⋀[R]^(a + b) M)
    (hμ : ∀ t : (⋀[R]^a M') ⊗[R] (⋀[R]^b M),
      μ (TensorProduct.map LinearMap.id (exteriorPower.map b g) t) =
        Module.exteriorPowerMul R M a b (TensorProduct.map (exteriorPower.map a f) LinearMap.id t)) :
    Function.Bijective μ := by
  have hsurj : Function.Surjective (TensorProduct.map (LinearMap.id : (⋀[R]^a M') →ₗ[R] _)
      (exteriorPower.map b g)) :=
    LinearMap.lTensor_surjective _ (exteriorPower_map_surjective hg)
  have hμ' : μ = (Module.exteriorPowerDetEquivOfBasis e' e''
      (splitBasis hexact hf σ hσ e' e'')).toLinearMap := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨t, rfl⟩ := hsurj y
    rw [hμ]
    have h := LinearMap.congr_fun (detWedge_key hexact hf σ hσ e' e'') t
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h ⊢
    exact h.symm
  rw [hμ']
  exact (Module.exteriorPowerDetEquivOfBasis e' e'' _).bijective

end Split

end MiyaokaMori.DetWedgeAlgebra

end
