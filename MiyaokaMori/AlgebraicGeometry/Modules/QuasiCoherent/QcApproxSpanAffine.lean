import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcSectionsBasicOpenLocalization
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentAffineLocal
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcApproxGoodOn

/-! # Spans of finitely many sections on an affine open

Support module for `QcFiniteTypeApproxFiniteSections` (Stacks 01PD–01PE).

Let `F` be a quasi-coherent module on a scheme `S`, `U` an affine open and `e : ι → Γ(F, U)` finitely many
sections. Two elementary facts about the `Γ(S, U)`-span of the `e i` (Stacks 01I8: sections over basic
opens are localizations):

* `exists_pow_smul_mem_span_of_map_mem_span`: if `t|_{D(g)}` lies in the span of the `e i|_{D(g)}`, then
  `g ^ N • t` lies in the span of the `e i` for some `N`. (Write the coefficients as `b i / g ^ n i`, clear
  denominators, and use that a section of `F` over `U` vanishing on `D(g)` is killed by a power of `g`.)
* `mem_span_of_locally` ("locally in the span ⇒ in the span" on an affine): if every point of `U` has a
  neighbourhood on which `t` is a combination of the `e i`, then `t` is a combination on `U`. (Shrink the
  neighbourhoods to basic opens `D(g_x)`; by the first fact `g_x ^ N_x • t` is in the span; the ideal of
  `c ∈ Γ(S, U)` with `c • t ∈ span` contains a power of `g_x` with `x ∈ D(g_x)` for every `x ∈ U`, hence is
  the unit ideal — `QcAffineLocalAux.ideal_eq_top`.)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.QcApprox

variable {S : AlgebraicGeometry.Scheme.{u}} (F : S.Modules)

/-- Restriction maps the span of the `e i` into the span of the restricted `e i`. -/
theorem map_mem_span_range_map {U V : S.Opens} (h : V ≤ U) {ι : Type v} (e : ι → Γ(F, U))
    {t : Γ(F, U)} (ht : t ∈ Submodule.span Γ(S, U) (Set.range e)) :
    F.presheaf.map (homOfLE h).op t ∈
      Submodule.span Γ(S, V) (Set.range fun i => F.presheaf.map (homOfLE h).op (e i)) := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha =>
    rw [AlgebraicGeometry.Scheme.Modules.map_smul]
    exact Submodule.smul_mem _ _ ha

variable [F.IsQuasicoherent]

/-- **Clearing denominators.** `U` affine, `g ∈ Γ(S, U)`, `e : ι → Γ(F, U)` finite. If `t|_{D(g)}` lies in
the `Γ(S, D(g))`-span of the `e i|_{D(g)}`, then `g ^ N • t` lies in the `Γ(S, U)`-span of the `e i` for
some `N`. -/
theorem exists_pow_smul_mem_span_of_map_mem_span {U : S.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    (g : Γ(S, U)) {ι : Type v} [Fintype ι] (e : ι → Γ(F, U)) (t : Γ(F, U))
    (ht : F.presheaf.map (homOfLE (S.basicOpen_le g)).op t ∈ Submodule.span Γ(S, S.basicOpen g)
      (Set.range fun i => F.presheaf.map (homOfLE (S.basicOpen_le g)).op (e i))) :
    ∃ N : ℕ, g ^ N • t ∈ Submodule.span Γ(S, U) (Set.range e) := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp ht
  have hloc : IsLocalization.Away g Γ(S, S.basicOpen g) := hU.isLocalization_basicOpen g
  have hcoef : ∀ i, ∃ (b : Γ(S, U)) (n : ℕ),
      c i * (S.presheaf.map (homOfLE (S.basicOpen_le g)).op g) ^ n =
        S.presheaf.map (homOfLE (S.basicOpen_le g)).op b := by
    intro i
    obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers g) (c i)
    refine ⟨b, n, ?_⟩
    have e1 : algebraMap Γ(S, U) Γ(S, S.basicOpen g) = (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom :=
      rfl
    rw [e1, map_pow] at hb
    exact hb
  choose b n hbn using hcoef
  set N := Finset.univ.sup n with hN
  set u : Γ(F, U) := ∑ i, (g ^ (N - n i) * b i) • e i with hu
  have hres : F.presheaf.map (homOfLE (S.basicOpen_le g)).op (g ^ N • t - u) = 0 := by
    rw [map_sub, AlgebraicGeometry.Scheme.Modules.map_smul, map_pow, ← hc, Finset.smul_sum, hu, map_sum,
      sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [AlgebraicGeometry.Scheme.Modules.map_smul, map_mul, map_pow, smul_smul, ← hbn i]
    congr 1
    have hle : n i ≤ N := Finset.le_sup (f := n) (Finset.mem_univ i)
    conv_lhs => rw [← Nat.sub_add_cancel hle, pow_add]
    ring
  obtain ⟨m, hm⟩ := F.exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero hU g _ hres
  refine ⟨m + N, ?_⟩
  have h1 : g ^ (m + N) • t = g ^ m • u := by
    rw [smul_sub, sub_eq_zero] at hm
    rw [pow_add, mul_smul]
    exact hm
  rw [h1, hu, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **Locally in the span ⇒ in the span, on an affine open.** `U` affine, `e : ι → Γ(F, U)` finite. If every
`x ∈ U` has an open neighbourhood `U₀ ≤ U` on which `t|_{U₀}` is a `Γ(S, U₀)`-combination of the
`e i|_{U₀}`, then `t` is a `Γ(S, U)`-combination of the `e i`. -/
theorem mem_span_of_locally {U : S.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) {ι : Type v} [Fintype ι]
    (e : ι → Γ(F, U)) (t : Γ(F, U))
    (h : ∀ x ∈ U, ∃ (U₀ : S.Opens) (h₀ : U₀ ≤ U), x ∈ U₀ ∧ F.presheaf.map (homOfLE h₀).op t ∈
      Submodule.span Γ(S, U₀) (Set.range fun i => F.presheaf.map (homOfLE h₀).op (e i))) :
    t ∈ Submodule.span Γ(S, U) (Set.range e) := by
  classical
  set N := Submodule.span Γ(S, U) (Set.range e) with hN
  set I : Ideal Γ(S, U) := N.colon {t} with hI
  have key : ∀ p : S, p ∈ U → ∃ (f : Γ(S, U)) (n : ℕ), p ∈ S.basicOpen f ∧ f ^ n ∈ I := by
    intro p hp
    obtain ⟨U₀, h₀, hp₀, ht₀⟩ := h p hp
    obtain ⟨f, hf, hpf⟩ := hU.exists_basicOpen_le ⟨p, hp₀⟩ hp
    have ht₁ := map_mem_span_range_map F hf _ ht₀
    simp only [map_map] at ht₁
    obtain ⟨n, hn⟩ := exists_pow_smul_mem_span_of_map_mem_span F hU f e t ht₁
    exact ⟨f, n, hpf, Submodule.mem_colon_singleton.mpr hn⟩
  have htop : I = ⊤ := QcAffineLocalAux.ideal_eq_top hU I key
  have h1 : (1 : Γ(S, U)) ∈ I := htop ▸ Submodule.mem_top
  have := Submodule.mem_colon_singleton.mp h1
  rwa [one_smul] at this

end AlgebraicGeometry.Scheme.Modules.QcApprox

end
