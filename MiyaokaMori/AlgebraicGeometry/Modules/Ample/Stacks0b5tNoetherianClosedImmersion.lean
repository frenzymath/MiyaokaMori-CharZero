import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectivizationOverRingPullbackTwist
import MiyaokaMori.AlgebraicGeometry.Modules.AmpleFiniteProjectivizationImmersionOver

/-! # Closed immersion into projective space over a ring (Stacks 0B5T)

Stacks 0B5T(1)–(2) over a ring, in the form needed for Serre vanishing over a Noetherian ring:
if `f : X → Spec R` is proper and `L` is an ample line
bundle on `X`, then there are `d > 0`, `N` and a **closed immersion** `i : X ⟶ P^N_R` over `Spec R`
(`i ≫ (P^N_R → Spec R) = f`) with `i^* O(1) ≅ L^{⊗d}`.

The field case (`R = k`, `f` the structure morphism) is
`exists_closedImmersion_projectiveSpace_pullback_twist_iso`, assembled from
`IsAmple.exists_projectivizationMorphism_isImmersion`. This module is assembled from the ring version
of the projectivization machinery:
- `ProjectiveSpaceOverChartRatio`: the chart `D_+(T_j) ⊆ P^N_R`, its coordinate ratios, chart map
  and the frame `T_j` of `O(1)`;
- `ProjectivizationOverRing`: `projectivizationMorphismOver f M P hP : V ⟶ ProjectiveSpaceOver N R`,
  glued from the chart morphisms (agreement via `fromOfGlobalSections_naturality` /
  `fromOfGlobalSections_unit_scale`), `φ ≫ toSpecBase = f`, `φ⁻¹D_+(T_ℓ) = V_ℓ`, the chart-map closed
  immersion and the immersion criterion;
- `ProjectivizationOverRingPullbackTwist`: `φ^*O(1) ≅ M` with `φ^*T_ℓ ↦ P_ℓ`;
- `AffineOpenFiniteTypeGeneratorsOver`: `R`-algebra generators of affine opens;
- `AmpleFiniteProjectivizationImmersionOver`: Stacks 01VU over `R`, the immersion.

Source: Stacks 0B5T (proof of (1)), 01VU, 01VR, 01VS; Hartshorne II.7.1 and II.7.6.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Stacks 0B5T(1)–(2), 01VU/01VR/01VS over a ring.** `R` a commutative ring, `f : X → Spec R`
proper, `L` an ample line bundle on `X` (`IsAmple`: `X` quasi-compact and every point lies in an
affine nonvanishing locus `X_s`, `s ∈ Γ(X, L^{⊗m})`, `m > 0`). Then there are `d > 0`, `N`, and a
closed immersion `i : X ⟶ P^N_R`
(`ProjectiveSpaceOver N R = Proj R[T_0..T_N]`) with `i ≫ (P^N_R → Spec R) = f` and `i^*O(1) ≅ L^{⊗d}`.

Proof sketch (Stacks 01VU + 01VR + 01VS + 04XV).
1. *Finite affine cover by sections of one power* (`IsAmple.exists_finite_affine_cover`,
   base-independent): `X` is quasi-compact, so there
   are `n > 0` and finitely many sections `s_ℓ ∈ Γ(X, L^{⊗n})` whose nonvanishing loci `X_{s_ℓ}` are affine
   and cover `X` (raise the sections given by `IsAmple` to a common power `n`).
2. *Generators of the affine pieces over `R`*: `X → Spec R` is of finite type (proper), so each
   `Γ(X_{s_ℓ}, O_X)` is a finitely generated `R`-algebra (Stacks 01T1: an affine open of a scheme of finite
   type over `Spec R` has finitely generated coordinate ring; the field version is
   `exists_surjective_eval₂Hom_of_isAffineOpen`, whose proof uses only
   `LocallyOfFiniteType (X ↘ Spec k)`). Choose finitely many generators `t_{ℓ,1}, …`.
3. *Extending the generators* (Stacks 01PW, `X` quasi-compact quasi-separated — `IsAmple.quasiSeparatedSpace`):
   for a common `e ≥ 1`, each `t_{ℓ,i} · s_ℓ^e|_{X_{s_ℓ}}` extends to a global section
   `T_{ℓ,i} ∈ Γ(X, L^{⊗ne})`; `Scheme.Modules.exists_uniform_tensorPow_extension` (base-independent)
   gives exactly this.
   Put `d := ne` and let the finite family `P = (s_ℓ^e) ∪ (T_{ℓ,i}) ∪ {0}` be indexed by `Fin (N + 1)`; the
   `s_ℓ^e` have no common zero, so `P` has no common zero.
4. *The morphism to `P^N_R`* (Hartshorne II.7.1 over `R`): on `X_{s_ℓ^e} = X_{s_ℓ}` the ratios
   `P_j / s_ℓ^e ∈ Γ(X_{s_ℓ}, O_X)` define an `R`-algebra map `R[x_0..x_N]/(x_ℓ - 1) → Γ(X_{s_ℓ}, O_X)`,
   i.e. a morphism `g_ℓ : X_{s_ℓ} → D_+(T_ℓ) ⊆ P^N_R` over `Spec R`; these agree on overlaps (the ratios
   are compatible: `(P_j/s_ℓ^e) = (P_j/s_m^e)(s_m^e/s_ℓ^e)`), so they glue to `i : X → P^N_R` with
   `i ≫ (P^N_R → Spec R) = f`, and `i^*O(1) ≅ L^{⊗d}` (the pullback of `T_j` is `P_j`). Field version:
   `projectivizationMorphism`, `projectivizationMorphism_comp_over`, `projectivizationMorphism_pullback_twist`;
   the ring version replaces `Spec k` by `Spec R` and `k[x]` by `R[x]` everywhere.
5. *`i` is an immersion* (Stacks 01VS): `i⁻¹(D_+(T_ℓ)) = X_{s_ℓ}` and the chart map `g_ℓ` corresponds to the
   surjective `R`-algebra map `R[x_0..x_N]/(x_ℓ - 1) → Γ(X_{s_ℓ}, O_X)` (the generators `t_{ℓ,i}` are the
   images of `x_{(ℓ,i)}`), so each `g_ℓ` is a closed immersion into the affine chart; `i` lands in
   `⋃_ℓ D_+(T_ℓ)` for the covering indices, so `i` is an immersion (Mathlib
   `IsZariskiLocalAtTarget.of_range_subset_iSup`). Field version: `isImmersion_projectivizationMorphism_of_charts`.
6. *`i` is a closed immersion* (Stacks 04XV, Mathlib `IsClosedImmersion.iff_isProper_and_mono`): `f = i ≫ π`
   is proper and `π : P^N_R → Spec R` is separated (`ProjectiveSpaceOver.isProper_toSpecBase`), so `i` is
   proper (`IsProper.of_comp`); an immersion is a monomorphism; a proper monomorphism is a closed immersion.

**Formalization.** Steps 1–5 are `IsAmple.exists_projectivizationMorphismOver_isImmersion`, step 4's
two clauses are `projectivizationMorphismOver_comp_toSpecBase` and
`projectivizationMorphismOver_pullback_twist`, step 6 is done here.

**Edge cases.** `R = 0`: `X = ∅` (there is no scheme over the empty scheme except `∅`), `P^N_0 = ∅`, the
unique morphism is a closed immersion; the pullback iso exists since both sides are the zero module.
`X = ∅`, `R ≠ 0`: `d = 1`, `N = 0`, `i` the unique morphism from `∅`, a closed immersion. `L` trivial: then
`X` is affine (`IsAmple` with `L = O_X` and `s = 1` forces `X = X_1` affine) and `i` is a closed immersion
into some `P^N_R` through the affine chart `D_+(T_0) ≅ 𝔸^N_R`; consistent. -/
theorem AlgebraicGeometry.exists_closedImmersion_projectiveSpaceOver_pullback_twist_iso
    {R : Type u} [CommRing R] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of R)) [AlgebraicGeometry.IsProper f]
    (L : X.Modules) [L.IsLineBundle] (hL : AlgebraicGeometry.IsAmple L) :
    ∃ (d N : ℕ) (_ : 0 < d) (i : X ⟶ ProjectiveSpaceOver N R) (_ : AlgebraicGeometry.IsClosedImmersion i),
      i ≫ ProjectiveSpaceOver.toSpecBase N R = f ∧
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback i).obj (projectiveSpaceOverTwist R N 1) ≅
        AlgebraicGeometry.Scheme.Modules.tensorPow L d) := by
  have : CompactSpace X := hL.1
  obtain ⟨d, N, hd, P, hP, hi⟩ :=
    AlgebraicGeometry.IsAmple.exists_projectivizationMorphismOver_isImmersion f L hL
  let i : X ⟶ ProjectiveSpaceOver N R :=
    projectivizationMorphismOver f (AlgebraicGeometry.Scheme.Modules.tensorPow L d) P hP
  have hover : i ≫ ProjectiveSpaceOver.toSpecBase N R = f :=
    projectivizationMorphismOver_comp_toSpecBase f _ P hP
  have : AlgebraicGeometry.IsImmersion i := hi
  have : AlgebraicGeometry.IsProper (i ≫ ProjectiveSpaceOver.toSpecBase N R) := by
    rw [hover]
    infer_instance
  have : AlgebraicGeometry.IsProper (ProjectiveSpaceOver.toSpecBase N R) :=
    ProjectiveSpaceOver.isProper_toSpecBase N R
  have : AlgebraicGeometry.IsProper i :=
    AlgebraicGeometry.IsProper.of_comp i (ProjectiveSpaceOver.toSpecBase N R)
  have hci : AlgebraicGeometry.IsClosedImmersion i :=
    (AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono i).2 ⟨inferInstance, inferInstance⟩
  obtain ⟨θ, -⟩ := projectivizationMorphismOver_pullback_twist f
    (AlgebraicGeometry.Scheme.Modules.tensorPow L d) P hP
  exact ⟨d, N, hd, i, hci, hover, ⟨θ⟩⟩

end
