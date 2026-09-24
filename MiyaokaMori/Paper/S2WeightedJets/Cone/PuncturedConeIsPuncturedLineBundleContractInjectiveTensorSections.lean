import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.NonvanishingLocusTensorSection
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedTautologicalSectionFrame

/-! # Tensoring with a family of sections without common zero determines a section

Let `L, N` be line bundles on a scheme `X` and `q : ι → Γ(X, N)` a family of global sections such that at
every point at least one `q i` is nonzero (`¬ IsZeroAt (q i) y`). If `w, w' ∈ Γ(X, L)` satisfy
`w ⊗ q i = w' ⊗ q i` (`sectionTensor`, for all `i`), then `w = w'`.

Proof (on stalks): fix `y`; choose `i` with `q i` nonzero at `y`, so `q i` is a frame of `N` on some open
neighbourhood `W₂` (`IsFrame.exists_of_not_isZeroAt`, Stacks 01CY); take a frame `e` of `L` at `y` (on `W₁`)
and put `W = W₁ ⊓ W₂`. On `W` write `w = c • e`, `w' = c' • e`; then `w ⊗ q = c • (e ⊗ q)` and
`w' ⊗ q = c' • (e ⊗ q)`. The isomorphism `(L ⊗ N)_y ≃ 𝒪_y` sends `(e ⊗ q)_y` to `1`
(`IsFrame.tensorStalkEquivOfFrames_germ_frame`, Stacks 01CB), so `c_y = c'_y` and
`w_y = c_y • e_y = c'_y • e_y = w'_y`. Since `y` is arbitrary, separatedness of the sheaf
(`TopCat.Presheaf.section_ext`) gives `w = w'`.

Source: Stacks 01CB (stalks of tensor products), 01CY (a section is a frame on its nonvanishing locus);
eq. (2.1) of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- For frames `e` (of `L`) and `f` (of `N`) on `W ∋ y`: if `a ⊗ f = a' ⊗ f` in `Γ(L ⊗ N, W)`, then `a_y = a'_y`.
Write `a = c • e`, `a' = c' • e`; then `a ⊗ f = c • (e ⊗ f)`, and `(L ⊗ N)_y ≃ 𝒪_y` sends `(e ⊗ f)_y` to `1`,
so `c_y = c'_y`. -/
theorem IsFrame.germ_eq_of_moduleTensorSection_eq {L N : X.Modules} {W : X.Opens} {e : Γ(L, W)} {f : Γ(N, W)}
    (he : IsFrame L W e) (hf : IsFrame N W f) {y : X} (hy : y ∈ W) (a a' : Γ(L, W))
    (h : AlgebraicGeometry.Scheme.Modules.moduleTensorSection a f = AlgebraicGeometry.Scheme.Modules.moduleTensorSection a' f) :
    L.presheaf.germ W y hy a = L.presheaf.germ W y hy a' := by
  have ha := he.coord_smul_frame le_rfl a
  rw [res_self] at ha
  have ha' := he.coord_smul_frame le_rfl a'
  rw [res_self] at ha'
  -- a ⊗ f = c • (e ⊗ f)
  have hsmul : ∀ c : Γ(X, W), AlgebraicGeometry.Scheme.Modules.moduleTensorSection (c • e) f =
      c • AlgebraicGeometry.Scheme.Modules.moduleTensorSection e f := by
    intro c
    have h1 := AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul c 1 e f
    rw [one_smul, mul_one] at h1
    exact h1
  -- `Θ : (L ⊗ N)_y ≃ 𝒪_y` sends `(c • (e ⊗ f))_y` to `c_y`
  have hΘ : ∀ c : Γ(X, W),
      he.tensorStalkEquivOfFrames hf hy
        ((AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ W y hy
          (c • AlgebraicGeometry.Scheme.Modules.moduleTensorSection e f)) = X.presheaf.germ W y hy c := by
    intro c
    have hg : (AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ W y hy
        (c • AlgebraicGeometry.Scheme.Modules.moduleTensorSection e f) =
          X.presheaf.germ W y hy c •
            (AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ W y hy
              (AlgebraicGeometry.Scheme.Modules.moduleTensorSection e f) :=
      germ_smul' (AlgebraicGeometry.Scheme.Modules.tensor L N) hy c (AlgebraicGeometry.Scheme.Modules.moduleTensorSection e f)
    rw [hg, LinearEquiv.map_smul, he.tensorStalkEquivOfFrames_germ_frame hf hy, smul_eq_mul, mul_one]
  have hc : X.presheaf.germ W y hy (he.coord le_rfl a) = X.presheaf.germ W y hy (he.coord le_rfl a') := by
    have e1 := hΘ (he.coord le_rfl a)
    have e2 := hΘ (he.coord le_rfl a')
    rw [← hsmul, ha] at e1
    rw [← hsmul, ha'] at e2
    rw [← e1, ← e2, h]
  have hLa : L.presheaf.germ W y hy a =
      X.presheaf.germ W y hy (he.coord le_rfl a) • L.presheaf.germ W y hy e := by
    conv_lhs => rw [← ha]
    exact germ_smul' L hy _ _
  have hLa' : L.presheaf.germ W y hy a' =
      X.presheaf.germ W y hy (he.coord le_rfl a') • L.presheaf.germ W y hy e := by
    conv_lhs => rw [← ha']
    exact germ_smul' L hy _ _
  rw [hLa, hLa', hc]

/-- **Tensoring with a family of sections without common zero determines a section**: for line bundles `L, N`
and `q : ι → Γ(X, N)` with some `q i` nonzero at every point, `w ⊗ q i = w' ⊗ q i` for all `i` implies
`w = w'`. -/
theorem eq_of_sectionTensor_eq_of_forall_exists_not_isZeroAt (L N : X.Modules) [L.IsLineBundle] [N.IsLineBundle]
    {ι : Type*} (q : ι → Γ(N, ⊤)) (hq : ∀ y : X, ∃ i, ¬ IsZeroAt (q i) y)
    (w w' : Γ(L, ⊤)) (h : ∀ i, sectionTensor w (q i) = sectionTensor w' (q i)) : w = w' := by
  refine TopCat.Presheaf.section_ext (⟨L.presheaf, L.isSheaf⟩ : TopCat.Sheaf Ab X) ⊤ w w' ?_
  intro y _
  obtain ⟨i, hi⟩ := hq y
  obtain ⟨W₂, hyW₂, hf₂⟩ := IsFrame.exists_of_not_isZeroAt N (q i) y hi
  obtain ⟨W₁, hyW₁, e₁, he₁⟩ := exists_frame L y
  have hy : y ∈ W₁ ⊓ W₂ := ⟨hyW₁, hyW₂⟩
  have hle : W₁ ⊓ W₂ ≤ ⊤ := le_top
  have he : IsFrame L (W₁ ⊓ W₂) (L.res inf_le_left e₁) := he₁.restrict inf_le_left
  have hf : IsFrame N (W₁ ⊓ W₂) (N.res hle (q i)) := by
    have h2 := hf₂.restrict (W₁ := W₁ ⊓ W₂) inf_le_right
    rwa [res_res] at h2
  have hst : ∀ v : Γ(L, ⊤),
      (AlgebraicGeometry.Scheme.Modules.tensor L N).res hle (sectionTensor v (q i)) =
        AlgebraicGeometry.Scheme.Modules.moduleTensorSection (L.res hle v) (N.res hle (q i)) := fun v =>
    AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict (homOfLE hle) v (q i)
  have hw := IsFrame.germ_eq_of_moduleTensorSection_eq he hf hy (L.res hle w) (L.res hle w')
    (by rw [← hst w, ← hst w', h i])
  have hres : ∀ v : Γ(L, ⊤),
      L.presheaf.germ (W₁ ⊓ W₂) y hy (L.res hle v) = L.presheaf.germ ⊤ y trivial v :=
    fun v => TopCat.Presheaf.germ_res_apply L.presheaf (homOfLE hle) y hy v
  rw [hres w, hres w'] at hw
  exact hw

end AlgebraicGeometry.Scheme.Modules

end
