import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOfNowhereZeroTuple
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.SectionIsZeroAtIso
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrameIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant

/-! # Projectivization morphism congr iso

Statement: the projectivization morphism `V → P^N` of a nowhere-vanishing tuple of sections
`P_0, …, P_N` of a line bundle `M` only depends on the tuple up to an isomorphism of the line
bundle: for `θ : M ≅ M'`, `projectivizationMorphism M P = projectivizationMorphism M' (θ ∘ P)`.

Source: Theorem 4.2 of the paper (the paper freely identifies `ρ^*f^*O_X(1)`, `(σ ≫ p)^*…`, etc.,
and speaks of "the projectivization of the tuple" without tracking the canonical isomorphisms).

, where the tuples to compare live on line bundles that are
identified through `pullbackComp` / `pullbackCongr` / `pullbackId` / `eqToHom (OX_toModules 1)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

/-- Transport of a chart morphism `Proj.fromOfGlobalSections` along an equality of opens `U = U'`:
if the two ratio tuples correspond under restriction along the equality, the chart morphism on `U'`
precomposed with `V.homOfLE` is the chart morphism on `U`. Proof: `subst` the equality of opens, then
the ratio tuples coincide (`homOfLE le_rfl` restricts trivially) and `homOfLE_rfl`. This isolates the
"transport along equal opens" step of . -/
theorem projectivizationChartMorphism_fromOfGlobalSections_congr {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (U U' : V.Opens) (hU : U = U')
    (r : Fin (N + 1) → Γ(V, U)) (r' : Fin (N + 1) → Γ(V, U'))
    (hr : ∀ j, V.presheaf.map (homOfLE hU.le).op (r' j) = r j)
    (h : (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).toIdeal.map
        (MvPolynomial.eval₂Hom
          ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
            (U.ι ≫ (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop).hom
          (fun j => U.topIso.inv.hom (r j))) = ⊤)
    (h' : (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).toIdeal.map
        (MvPolynomial.eval₂Hom
          ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
            (U'.ι ≫ (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop).hom
          (fun j => U'.topIso.inv.hom (r' j))) = ⊤) :
    V.homOfLE hU.le ≫
      AlgebraicGeometry.Proj.fromOfGlobalSections (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
        (MvPolynomial.eval₂Hom
          ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
            (U'.ι ≫ (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop).hom
          (fun j => U'.topIso.inv.hom (r' j))) h' =
    AlgebraicGeometry.Proj.fromOfGlobalSections (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
        (MvPolynomial.eval₂Hom
          ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
            (U.ι ≫ (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop).hom
          (fun j => U.topIso.inv.hom (r j))) h := by
  subst hU
  have hrr : r' = r := by
    funext j
    rw [← hr j]
    have hid : (homOfLE (le_of_eq (rfl : U = U))).op = 𝟙 (Opposite.op U) := rfl
    rw [hid, V.presheaf.map_id]
    rfl
  subst hrr
  rw [AlgebraicGeometry.Scheme.homOfLE_rfl, Category.id_comp]

/-- Non-vanishing loci agree under a line bundle isomorphism: `projectivizationChart P ℓ` is by
definition `M.nonvanishingLocus (P ℓ)`, and `nonvanishingLocus_iso`
(`NonvanishingLocusIsoInvariant`) gives the equality. -/
theorem projectivizationChart_congr_iso {V : AlgebraicGeometry.Scheme.{u}}
    {M M' : V.Modules} [M.IsLineBundle] [M'.IsLineBundle] (θ : M ≅ M') {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1)) :
    projectivizationChart P ℓ = projectivizationChart (fun j => θ.hom.app ⊤ (P j)) ℓ :=
  (AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso θ (P ℓ)).symm

/-- Ratios agree under a line bundle isomorphism: the ratio of `θ ∘ P`, restricted along the equality
of charts, is the ratio of `P` (uniqueness `projectivizationRatio_unique`; `θ` is `O`-linear and commutes
with restriction, and `θ.hom.app U` is injective). -/
theorem projectivizationRatio_congr_iso {V : AlgebraicGeometry.Scheme.{u}}
    {M M' : V.Modules} [M.IsLineBundle] [M'.IsLineBundle] (θ : M ≅ M') {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ j : Fin (N + 1)) :
    V.presheaf.map (homOfLE (projectivizationChart_congr_iso θ P ℓ).le).op
        (projectivizationRatio (fun i => θ.hom.app ⊤ (P i)) ℓ j) =
      projectivizationRatio P ℓ j := by
  symm
  apply projectivizationRatio_unique P ℓ j
  rw [AlgebraicGeometry.Scheme.Modules.res_self]
  apply (AlgebraicGeometry.Scheme.Modules.Iso.app_bijective θ (projectivizationChart P ℓ)).1
  have e1 : θ.hom.app (projectivizationChart P ℓ) (M.res le_top (P ℓ)) =
      M'.res le_top (θ.hom.app ⊤ (P ℓ)) :=
    AlgebraicGeometry.Scheme.Modules.Hom.app_res θ.hom le_top (P ℓ)
  have e2 : θ.hom.app (projectivizationChart P ℓ) (M.res le_top (P j)) =
      M'.res le_top (θ.hom.app ⊤ (P j)) :=
    AlgebraicGeometry.Scheme.Modules.Hom.app_res θ.hom le_top (P j)
  rw [AlgebraicGeometry.Scheme.Modules.Hom.app_smul, e1, e2]
  have h := projectivizationRatio_smul (fun i => θ.hom.app ⊤ (P i)) ℓ j
  rw [AlgebraicGeometry.Scheme.Modules.res_self] at h
  have h2 := congrArg (M'.res (projectivizationChart_congr_iso θ P ℓ).le) h
  rw [AlgebraicGeometry.Scheme.Modules.res_smul, AlgebraicGeometry.Scheme.Modules.res_res,
    AlgebraicGeometry.Scheme.Modules.res_res] at h2
  exact h2

/-- **Transport of `projectivizationMorphism` along an isomorphism of line bundles.**

Natural-language proof (self-contained; follows the construction in
).
1. `projectivizationMorphism M P hP` is glued (`Scheme.Cover.glueMorphisms`) from the chart
   morphisms `projectivizationChartMorphism P ℓ : V_ℓ → P^N`, where `V_ℓ := projectivizationChart P ℓ`
   is the non-vanishing locus of `P_ℓ` and the chart morphism is `Proj.fromOfGlobalSections` of the
   ring map `k[X_0,…,X_N] → Γ(V_ℓ, O)` sending `X_i` to the ratio `P_i / P_ℓ`
   (`projectivizationRatio P ℓ i`, the unique function `r` with `r • P_ℓ|_{V_ℓ} = P_i|_{V_ℓ}`,
   `projectivizationRatio_unique`).
2. Non-vanishing loci agree: `¬IsZeroAt (θ P_ℓ) v ↔ ¬IsZeroAt P_ℓ v` for every point `v`
  , so `projectivizationChart (θ ∘ P) ℓ = projectivizationChart P ℓ`
   as opens (`Opens.ext`; the non-vanishing locus is defined pointwise by `IsZeroAt`).
3. Ratios agree: `θ` is `O_V`-linear, so `r • (θ P_ℓ)|_{V_ℓ} = θ (r • P_ℓ|_{V_ℓ}) = θ (P_i|_{V_ℓ}) = (θ P_i)|_{V_ℓ}`
   (`Scheme.Modules.Hom.app_smul` and naturality of `θ.hom` with respect to restriction);
   by uniqueness of the ratio (`projectivizationRatio_unique`),
   `projectivizationRatio (θ ∘ P) ℓ i = projectivizationRatio P ℓ i` (after transporting along the
   equality of opens from step 2, which is an `eqToHom` on `Opens`; the function is unchanged
   because restriction along `eqToHom rfl`-type maps is the identity).
4. Hence the chart ring maps, the chart morphisms and the covers (`projectivizationCover`) agree,
   and the two glued morphisms agree by uniqueness in `Scheme.Cover.hom_ext`
   (`projectivizationMorphism_restrict` identifies the restriction of each glued morphism to the
   chart `V_ℓ` with the chart morphism).
5. Practical formalisation route: use `(projectivizationCover M P hP).hom_ext`, and for each `ℓ`
   rewrite both sides with `projectivizationMorphism_restrict` (for the right-hand side first
   transport the chart inclusion along the equality of opens of step 2 via `eqToHom`), then reduce
   to equality of the chart ring maps `projectivizationChartEval`, which is
   `MvPolynomial.ringHom_ext` on the generators `X_i ↦ ratio`, closed by step 3.

Auxiliary facts: `nonvanishingLocus_iso` (imported) and, possibly, a lemma that
`projectivizationRatio` is compatible with `Hom.app` of an `O`-linear isomorphism
(direct from `projectivizationRatio_unique` + `Hom.app_smul`).

Estimated 120 lines, level medium-hard (transport along equality of opens is the fiddly part). -/
theorem projectivizationMorphism_congr_iso {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M M' : V.Modules) [M.IsLineBundle] [M'.IsLineBundle] (θ : M ≅ M') {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v)
    (hP' : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (θ.hom.app ⊤ (P ℓ)) v) :
    projectivizationMorphism (k := k) M P hP =
      projectivizationMorphism (k := k) M' (fun ℓ => θ.hom.app ⊤ (P ℓ)) hP' := by
  apply (projectivizationCover (k := k) M P hP).hom_ext
  intro ℓ
  change Fin (N + 1) at ℓ
  change (projectivizationChart P ℓ).ι ≫ projectivizationMorphism (k := k) M P hP =
    (projectivizationChart P ℓ).ι ≫ projectivizationMorphism (k := k) M' (fun i => θ.hom.app ⊤ (P i)) hP'
  rw [projectivizationMorphism_restrict M P hP ℓ,
    ← AlgebraicGeometry.Scheme.homOfLE_ι V (projectivizationChart_congr_iso θ P ℓ).le, Category.assoc,
    projectivizationMorphism_restrict M' (fun i => θ.hom.app ⊤ (P i)) hP' ℓ]
  symm
  exact projectivizationChartMorphism_fromOfGlobalSections_congr (k := k)
    (projectivizationChart P ℓ) (projectivizationChart (fun i => θ.hom.app ⊤ (P i)) ℓ)
    (projectivizationChart_congr_iso θ P ℓ)
    (projectivizationRatio P ℓ) (projectivizationRatio (fun i => θ.hom.app ⊤ (P i)) ℓ)
    (projectivizationRatio_congr_iso θ P ℓ)
    (projectivizationChartEval_irrelevant_map_eq_top (k := k) P ℓ)
    (projectivizationChartEval_irrelevant_map_eq_top (k := k) (fun i => θ.hom.app ⊤ (P i)) ℓ)

/-- The nowhere-vanishing hypothesis transports along an isomorphism of line bundles. -/
theorem exists_not_isZeroAt_iso {X : AlgebraicGeometry.Scheme.{u}} {M M' : X.Modules}
    (θ : M ≅ M') {N : ℕ} (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : X, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) (v : X) :
    ∃ ℓ, ¬ IsZeroAt (θ.hom.app ⊤ (P ℓ)) v := by
  obtain ⟨ℓ, hℓ⟩ := hP v
  exact ⟨ℓ, fun h => hℓ ((isZeroAt_iso_iff θ (P ℓ) v).1 h)⟩

end
