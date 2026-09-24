import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLinearMap

/-! # `H^0` is global sections

For a module `M` on a scheme `X`, `H^0(X, M)` is `Γ(X, O_X)`-linearly isomorphic to the global
sections `Γ(M, ⊤)` (hence `K`-linearly when `X` is a `K`-scheme); the isomorphism is natural in
`f : M ⟶ N`, matching `H^0(f)` with the action of `f` on global sections. Corollaries:
`H^0(X, M) ≠ 0` iff `M` has a nonzero global section; `H^0(f)` is surjective iff `f` is surjective on
global sections.

Proof sketch:
1. `H^0(X, M) = Ext^0(ℤ_X, M) = Hom(ℤ_X, M) = M(⊤)`: Mathlib's `Sheaf.H.equiv₀` (constant sheaf –
   global sections adjunction; `⊤` is the terminal object of `Opens X`), an additive equivalence.
2. Linearity: a scalar `r` acts on `H^0` by `Sheaf.H.map μ_r`; `Sheaf.H.equiv₀_naturality` for `μ_r`
   gives `equiv₀(r • x) = μ_r(⊤)(equiv₀ x)`, and `μ_r` on `⊤` is multiplication by `r|_⊤ = r`.
3. Naturality: `Sheaf.H.equiv₀_naturality` for the underlying morphism of abelian sheaves of `f`,
   together with `sheafCohomology.map_apply`.

Source: `H^0 = Γ` (Stacks 01E0 / 01FT); Mathlib `CategoryTheory/Sites/SheafCohomology/Basic.lean`
(`H.equiv₀`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- On global sections, `μ_r` is multiplication by `r`. -/
theorem Scheme.Modules.smulEnd_app_top (M : X.Modules) (r : Γ(X, ⊤)) (y : Γ(M, ⊤)) :
    (M.smulEnd r).hom.app (op ⊤) y = r • y := by
  have h : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) = 𝟙 _ := Subsingleton.elim _ _
  change X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op r • y = r • y
  rw [h, op_id, X.presheaf.map_id]
  rfl

theorem sheafCohomology.exists_zeroEquiv (M : X.Modules) :
    ∃ e : sheafCohomology X M 0 ≃ₗ[Γ(X, ⊤)] Γ(M, ⊤),
      ∀ x : sheafCohomology X M 0,
        e x = Sheaf.H.equiv₀ M.toAddCommGrpSheaf (Limits.isTerminalTop (α := X.Opens)) x := by
  refine ⟨{ Sheaf.H.equiv₀ M.toAddCommGrpSheaf (Limits.isTerminalTop (α := X.Opens)) with
    map_smul' := ?_ }, fun _ => rfl⟩
  intro r x
  have h := Sheaf.H.equiv₀_naturality (f := M.smulEnd r)
    (hT := (Limits.isTerminalTop (α := X.Opens))) (x := x)
  exact h.symm.trans (Scheme.Modules.smulEnd_app_top M r _)

/-- `H^0(X, M) ≃ Γ(M, ⊤)`, `Γ(X, O_X)`-linearly. -/
def sheafCohomologyZeroEquiv (M : X.Modules) :
    sheafCohomology X M 0 ≃ₗ[Γ(X, ⊤)] Γ(M, ⊤) :=
  Classical.choose (sheafCohomology.exists_zeroEquiv M)

/-- Unfolding: this is Mathlib's `Sheaf.H.equiv₀`. -/
theorem sheafCohomologyZeroEquiv_apply (M : X.Modules) (x : sheafCohomology X M 0) :
    sheafCohomologyZeroEquiv M x =
      Sheaf.H.equiv₀ M.toAddCommGrpSheaf (Limits.isTerminalTop (α := X.Opens)) x :=
  Classical.choose_spec (sheafCohomology.exists_zeroEquiv M) x

/-- Naturality: `H^0(f)` corresponds to the action of `f` on global sections. -/
theorem sheafCohomologyZeroEquiv_naturality {M N : X.Modules} (f : M ⟶ N)
    (x : sheafCohomology X M 0) :
    sheafCohomologyZeroEquiv N (sheafCohomology.map f 0 x) =
      f.app ⊤ (sheafCohomologyZeroEquiv M x) := by
  rw [sheafCohomologyZeroEquiv_apply, sheafCohomology.map_apply, sheafCohomologyZeroEquiv_apply]
  exact (Sheaf.H.equiv₀_naturality (Scheme.Modules.toAddCommGrpSheafMap f)
    (hT := (Limits.isTerminalTop (α := X.Opens))) (x := x)).symm

/-- On a `K`-scheme the isomorphism is compatible with the `K`-action (`K` acts on global sections
via `K → Γ(X, O_X)`). -/
theorem sheafCohomologyZeroEquiv_smulOver {K : Type u} [CommRing K]
    [X.Over (Spec (CommRingCat.of K))] (M : X.Modules) (c : K) (x : sheafCohomology X M 0) :
    sheafCohomologyZeroEquiv M (c • x) =
      (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (X ↘ Spec (CommRingCat.of K)).appTop).hom c) • sheafCohomologyZeroEquiv M x :=
  (sheafCohomologyZeroEquiv M).map_smul _ x

/-- `H^0(X, M) ≠ 0` ⇒ `M` has a nonzero global section (written as an element of
`M.val.obj (op ⊤)`). -/
theorem exists_section_ne_zero_of_nontrivial_sheafCohomology_zero (M : X.Modules)
    [Nontrivial (sheafCohomology X M 0)] :
    ∃ s : (M.val.obj (Opposite.op ⊤) : Type u), s ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : sheafCohomology X M 0)
  exact ⟨sheafCohomologyZeroEquiv M x, fun h => hx ((sheafCohomologyZeroEquiv M).map_eq_zero_iff.mp h)⟩

/-- `h^0(X, M) > 0` over `K` ⇒ `M` has a nonzero global section. -/
theorem exists_section_ne_zero_of_finrank_pos {K : Type u} [Field K]
    [X.Over (Spec (CommRingCat.of K))] (M : X.Modules)
    (h : 0 < Module.finrank K (sheafCohomology X M 0)) :
    ∃ s : (M.val.obj (Opposite.op ⊤) : Type u), s ≠ 0 := by
  have : Nontrivial (sheafCohomology X M 0) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    rw [Module.finrank_zero_of_subsingleton] at h
    exact lt_irrefl _ h
  exact exists_section_ne_zero_of_nontrivial_sheafCohomology_zero M

/-- `H^0(f)` is surjective iff `f` is surjective on global sections. -/
theorem sheafCohomology_map_zero_surjective_iff {M N : X.Modules} (f : M ⟶ N) :
    Function.Surjective (sheafCohomology.map f 0) ↔ Function.Surjective (f.app ⊤) := by
  constructor
  · intro h t
    obtain ⟨x, hx⟩ := h ((sheafCohomologyZeroEquiv N).symm t)
    exact ⟨sheafCohomologyZeroEquiv M x, by
      rw [← sheafCohomologyZeroEquiv_naturality, hx, LinearEquiv.apply_symm_apply]⟩
  · intro h y
    obtain ⟨s, hs⟩ := h (sheafCohomologyZeroEquiv N y)
    refine ⟨(sheafCohomologyZeroEquiv M).symm s, (sheafCohomologyZeroEquiv N).injective ?_⟩
    rw [sheafCohomologyZeroEquiv_naturality, LinearEquiv.apply_symm_apply, hs]

end AlgebraicGeometry

end
