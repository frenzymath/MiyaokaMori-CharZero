import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleContractInjectiveTensorSections

/-! # A tuple with vanishing minors against a nowhere-zero tuple is a scalar multiple of it

A tuple of global sections of a line bundle whose `2×2` minors with a nowhere-vanishing tuple all vanish is a
global scalar multiple of that tuple.

Source: §3 of the paper ("the coefficient tuple is a multiple of the seed") and the proof of Theorem 4.2 ("the affine tuple would therefore be a scalar multiple of the seed tuple"); this is the global
version of the local argument of `ScalarRatioOfSeedMinorsZero`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Proportional tuples: minors zero ⇒ global scalar.** `M` is a line bundle on a scheme `Z`, `P, s : ι → Γ(M)`,
`s` is nowhere zero (at every point some `s i` is not zero at that point) and `P i ⊗ s j = P j ⊗ s i` in `Γ(M ⊗ M)`
for all `i, j`. Then there is `a ∈ Γ(Z, O)` with `P i = a • s i` for all `i`.

**Proof.** For every point `z` choose `i z` with `s (i z)` not zero at `z`; by Stacks 01CY
(`IsFrame.exists_of_not_isZeroAt`) there is an open `W z ∋ z` on which `e_z := s (i z)|` is a frame of `M`
(`IsFrame`: `r ↦ r • e_z` is bijective on every open of `W z`). The `W z` cover `Z`.
1. On `W z` let `lam z ∈ Γ(W z, O)` be the coordinate of `P (i z)|` in the frame `e_z`
   (`IsFrame.coord`): `P (i z)| = lam z • e_z`.
2. For every `j`, on `W z`: write `s j| = σ • e_z`. Restricting the minor `P j ⊗ s (i z) = P (i z) ⊗ s j`
   (`moduleTensorSection_restrict`) gives `P j| ⊗ e_z = (lam z • e_z) ⊗ (σ • e_z) = ((lam z * σ) • e_z) ⊗ e_z`
   (`moduleTensorSection_smul`). Cancelling the frame `e_z` in the second factor — stalkwise via
   `(M ⊗ M)_y ≃ O_y`, `IsFrame.germ_eq_of_moduleTensorSection_eq`, then separation
   (`TopCat.Presheaf.section_ext`) — yields `P j| = (lam z * σ) • e_z = lam z • s j|` (**).
3. On `W z ⊓ W z'`: by (**) for `z` and for `z'` with `j = i z'`, `lam z • s (i z')| = P (i z')| = lam z' • s (i z')|`,
   and `s (i z')` is a frame there, so `lam z = lam z'` on `W z ⊓ W z'` (injectivity of `r ↦ r • frame`).
4. By the gluing axiom of the sheaf `O_Z` (`TopCat.Sheaf.existsUnique_gluing'`) there is `a ∈ Γ(Z, O)` with
   `a|_{W z} = lam z` for all `z`. Then for each `j`, `(a • s j)|_{W z} = lam z • s j|_{W z} = P j|_{W z}` for all `z`
   by (**), so `a • s j = P j` by separation (`TopCat.Sheaf.eq_of_locally_eq'`).
Edge cases: `Z` empty — the cover is empty and gluing gives some `a`, separation over the empty cover is vacuous;
`ι` empty and `Z` nonempty — the nowhere-zero hypothesis is false.
Note: `P`, `s` are typed as `M.val.obj (op ⊤)`, which is defeq but not reducibly equal to `Γ(M, ⊤)`; the proof
first retypes them (`suffices`) so that the frame API (`res`, `IsFrame`, `coord`, stated for `Γ(M, U)`) applies.
Library facts used: `IsFrame`, `coord`, `res_smul`, `res_res`, `IsFrame.exists_of_not_isZeroAt`,
`IsFrame.germ_eq_of_moduleTensorSection_eq`, and the tensor-power lemmas of `ModuleTensorPowers`. -/
theorem exists_smul_eq_of_sectionTensor_eq_of_nowhere_zero {Z : AlgebraicGeometry.Scheme.{u}}
    (M : Z.Modules) [M.IsLineBundle] {ι : Type v}
    (P s : ι → (M.val.obj (Opposite.op ⊤) : Type u))
    (hs : ∀ z : Z, ∃ i, ¬ IsZeroAt (s i) z)
    (h : ∀ i j, sectionTensor (P i) (s j) = sectionTensor (P j) (s i)) :
    ∃ a : Γ(Z, ⊤), ∀ i, P i = (show Z.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) • s i := by
  classical
  -- Retype `P`, `s` as sections of `M.presheaf` (`Γ(M, ⊤)`): the two carriers are defeq but not reducibly so,
  -- and the frame API (`res`, `IsFrame`, `coord`) is stated for `Γ(M, U)`.
  suffices H : ∀ P s : ι → Γ(M, ⊤), (∀ z : Z, ∃ i, ¬ IsZeroAt (s i) z) →
      (∀ i j, sectionTensor (P i) (s j) = sectionTensor (P j) (s i)) →
      ∃ a : Γ(Z, ⊤), ∀ i, P i = a • s i from H P s hs h
  clear P s hs h
  intro P s hs h
  open AlgebraicGeometry.Scheme.Modules in
  -- Step 0: for each point `z` choose `i z` with `s (i z)` not zero at `z`, and an open `W z ∋ z` on which
  -- `s (i z)` is a frame (Stacks 01CY, `IsFrame.exists_of_not_isZeroAt`).
  choose i hi using hs
  choose W hzW hfr using fun z => IsFrame.exists_of_not_isZeroAt M (s (i z)) z (hi z)
  have hcover : (⊤ : Z.Opens) ≤ iSup W := fun z _ => Opens.mem_iSup.mpr ⟨z, hzW z⟩
  -- Step 1: the local scalar `lam z := P (i z) / s (i z)` on `W z`.
  let lam : ∀ z : Z, Γ(Z, W z) := fun z => (hfr z).coord le_rfl (M.res le_top (P (i z)))
  have hlam : ∀ z : Z, M.res (le_top : W z ≤ ⊤) (P (i z)) = lam z • M.res le_top (s (i z)) := by
    intro z
    have h1 := (hfr z).coord_smul_frame le_rfl (M.res le_top (P (i z)))
    rw [res_self] at h1
    exact h1.symm
  -- restriction of the minors to `W z`
  have hst : ∀ (z : Z) (v w : Γ(M, ⊤)),
      (AlgebraicGeometry.Scheme.Modules.tensor M M).res (le_top : W z ≤ ⊤) (sectionTensor v w) =
        AlgebraicGeometry.Scheme.Modules.moduleTensorSection (M.res le_top v) (M.res le_top w) := fun z v w =>
    AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict (homOfLE (le_top : W z ≤ ⊤)) v w
  -- Step 2 (**): on `W z`, `P j = lam z • s j` for every `j`.
  have key : ∀ (z : Z) (j : ι), M.res (le_top : W z ≤ ⊤) (P j) = lam z • M.res le_top (s j) := by
    intro z j
    -- `e := s (i z)|` is a frame on `W z`; `P (i z)| = lam z • e`, `s j| = σ • e`
    obtain ⟨e, he⟩ : ∃ e : Γ(M, W z), e = M.res le_top (s (i z)) := ⟨_, rfl⟩
    have hfe : IsFrame M (W z) e := he ▸ hfr z
    have hlam' : M.res (le_top : W z ≤ ⊤) (P (i z)) = lam z • e := he ▸ hlam z
    obtain ⟨σ, hσ⟩ : ∃ σ : Γ(Z, W z), M.res (le_top : W z ≤ ⊤) (s j) = σ • e := by
      refine ⟨hfe.coord le_rfl (M.res le_top (s j)), ?_⟩
      have h1 := hfe.coord_smul_frame le_rfl (M.res le_top (s j))
      rw [res_self] at h1
      exact h1.symm
    -- `P j ⊗ e = P (i z) ⊗ s j = (lam z * σ) • (e ⊗ e) = ((lam z * σ) • e) ⊗ e`
    have hmin : AlgebraicGeometry.Scheme.Modules.moduleTensorSection (M.res (le_top : W z ≤ ⊤) (P j)) e =
        AlgebraicGeometry.Scheme.Modules.moduleTensorSection ((lam z * σ) • e) e := by
      have h0 := congrArg ((AlgebraicGeometry.Scheme.Modules.tensor M M).res (le_top : W z ≤ ⊤)) (h j (i z))
      rw [hst, hst, ← he] at h0
      rw [h0, hlam', hσ, AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul]
      have h2 := AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul (lam z * σ) (1 : Γ(Z, W z)) e e
      rw [one_smul, mul_one] at h2
      exact h2.symm
    -- cancel the frame `e` (stalkwise, then separation)
    have hgerm := fun (y : Z) (hy : y ∈ W z) =>
      IsFrame.germ_eq_of_moduleTensorSection_eq hfe hfe hy _ _ hmin
    have hsec : M.res (le_top : W z ≤ ⊤) (P j) = (lam z * σ) • e :=
      TopCat.Presheaf.section_ext (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab Z) (W z) _ _ hgerm
    rw [hsec, hσ, mul_smul]
  -- Step 3: the local scalars agree on overlaps (uniqueness of the coordinate in the frame `s (i z')`).
  have compat : TopCat.Presheaf.IsCompatible Z.sheaf.1 W lam := by
    intro z z'
    have hfr' : IsFrame M (W z ⊓ W z') (M.res le_top (s (i z'))) := by
      have h2 := (hfr z').restrict (W₁ := W z ⊓ W z') inf_le_right
      rwa [res_res] at h2
    have h1 := congrArg (M.res (inf_le_left : W z ⊓ W z' ≤ W z)) (key z (i z'))
    have h2 := congrArg (M.res (inf_le_right : W z ⊓ W z' ≤ W z')) (key z' (i z'))
    rw [res_smul, res_res, res_res] at h1 h2
    exact (hfr' (W z ⊓ W z') le_rfl).1 (by
      rw [res_self]
      exact h1.symm.trans h2)
  -- Step 4: glue to a global `a`, and check `P j = a • s j` by separation.
  obtain ⟨a, ha, -⟩ := Z.sheaf.existsUnique_gluing' W ⊤ (fun z => homOfLE le_top) hcover lam compat
  refine ⟨show Γ(Z, ⊤) from a, fun j => ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab Z) W ⊤
    (fun z => homOfLE le_top) hcover _ _ fun z => ?_
  change M.res (le_top : W z ≤ ⊤) (P j) = M.res le_top ((show Γ(Z, ⊤) from a) • s j)
  rw [res_smul, key z j]
  exact congrArg (fun r : Γ(Z, W z) => r • M.res (le_top : W z ≤ ⊤) (s j)) (ha z).symm

end
