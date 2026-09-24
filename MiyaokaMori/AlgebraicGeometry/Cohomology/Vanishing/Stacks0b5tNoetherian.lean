import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ClosedImmersionProjectionFormula
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesFiniteTypeInstances
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ce01id
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01y6
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks0b5tNoetherianClosedImmersion
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks0b5tNoetherianProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks0b5tNoetherianProjectiveSpaceAux
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.Stacks02uv

/-! # Serre vanishing over a Noetherian ring (Stacks 0B5T(4))

Stacks 0B5T(4) over a Noetherian ring (relative Serre vanishing, affine base): `R` Noetherian,
`f : X → Spec R` proper, `L` ample on `X`, `F` coherent ⇒ `H^p(X, F ⊗ L^{⊗n}) = 0` for `p > 0`, `n ≫ 0`.

Source: Stacks 0B5T (coherent-lemma-coherent-proper-ample), part (4); EGA III 2.2.1.
The field case `R = k` is `sheafCohomology_tensor_pow_subsingleton_of_isAmple` (`Stacks0b5t.lean`): that
statement is this one with `R := k` and `f := X ↘ Spec k`. Used for Stacks 02O1 (relative Serre vanishing
over a Noetherian scheme), which reduces to this statement over the affine opens of the base.

## Proof (Stacks 0B5T, proof of (4))

The proof is the field proof of `Stacks0b5t.lean` with `k` replaced by `R` and `ProjectiveSpace N k` by
`ProjectiveSpaceOver N R` (`P^N_R = Proj R[T_0..T_N]`).
1. **Closed immersion into projective space** (`exists_closedImmersion_projectiveSpaceOver_pullback_twist_iso`):
   since `X` is proper over `Spec R` and `L` is ample, there are `d > 0`, `N`, and a closed
   immersion `i : X ⟶ P^N_R` over `Spec R` with `i^*O(1) ≅ L^{⊗d}` (Stacks 01VU/01VR give an immersion;
   proper + separated target makes it a closed immersion).
2. **Reduction to `d` residue classes.** Write `n = q + d m` with `q = n % d`, `m = n / d`. Then
   `F ⊗ L^{⊗n} ≅ (F ⊗ L^{⊗q}) ⊗ i^*O(m)` (`tensor_tensorPow_add_mul_iso_tensor_pullback_twist_over`).
3. **Closed immersions preserve cohomology and coherence.** `H^p(X, G ⊗ i^*O(m)) ≅ H^p(P^N_R, i_*(G ⊗ i^*O(m)))`
   (Stacks 02UV, `sheafCohomologyClosedImmersionAddEquiv`), and by the projection formula
   `i_*(G ⊗ i^*O(m)) ≅ i_*G ⊗ O(m)` (projection formula for closed immersions). For `G = F ⊗ L^{⊗q}`
   coherent, `i_*G` is coherent on the Noetherian scheme `P^N_R` (Stacks 01Y6, closed immersions are finite;
   `ProjectiveSpaceOver.isLocallyNoetherian'`).
4. **Serre vanishing on `P^N_R`** (`sheafCohomology_tensor_twist_subsingleton_projectiveSpaceOver`): for
   each coherent
   `G_q := i_*(F ⊗ L^{⊗q})`, `0 ≤ q < d`, and each `0 < p ≤ N`, there is `n_{q,p}` with
   `H^p(P^N_R, G_q ⊗ O(m)) = 0` for `m ≥ n_{q,p}`; for `p > N` all quasi-coherent cohomology of `P^N_R`
   vanishes (Čech bound, `sheafCohomology_projectiveSpaceOver_subsingleton_of_lt`).
5. **Uniform bound.** Let `M := max_{q < d, p ≤ N} n_{q,p}` and `n₀ := d · M`. For `n ≥ n₀` we have
   `m = n / d ≥ M`, so for every `p > 0` the group in step 3 vanishes; transporting back along the
   isomorphisms of steps 2–3 gives `H^p(X, F ⊗ L^{⊗n}) = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Coherent `⊗` line bundle is coherent (quasi-coherence: Stacks 01CE, `isQuasicoherent_tensor`; finite
type: `tensor_isFiniteType`). Same as `Stacks0bemTwist.isCoherent_tensor_of_isLineBundle` (and the private
copy in `Stacks0b5t.lean`), which cannot be imported here: `Stacks0bemTwist` depends on `Stacks02o5`, which
imports `Stacks02o1`, which imports this file. -/
private theorem isCoherent_tensor_of_isLineBundle_over {X : AlgebraicGeometry.Scheme.{u}}
    (G M : X.Modules) [G.IsCoherent] [M.IsLineBundle] :
    (AlgebraicGeometry.Scheme.Modules.tensor G M).IsCoherent := by
  have hq : G.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
  have hf : G.IsFiniteType := AlgebraicGeometry.Scheme.Modules.IsCoherent.finiteType
  exact ⟨inferInstance, inferInstance⟩

/-- **Serre vanishing over a Noetherian ring** — Stacks 0B5T(4). `R` a Noetherian ring, `f : X → Spec R`
proper, `L` an ample line bundle on `X` (`IsAmple`: `X` quasi-compact and every point lies in an affine nonvanishing locus
`X_s`, `s ∈ Γ(X, L^{⊗m})`, `m > 0`), `F` coherent. Then there is `n₀` such that for all `n ≥ n₀`
and all `p > 0` the abelian group `H^p(X, F ⊗ L^{⊗n})` is zero (`Subsingleton`).

The conclusion does not mention `f` or `R`: they only enter through the hypotheses (`X` proper over
a Noetherian ring), exactly as in Stacks 0B5T. The field case is
`sheafCohomology_tensor_pow_subsingleton_of_isAmple`, proved by the same five steps over `k`. See the module
docstring for the route.

**Edge cases.** `R = 0`: `X = ∅`, all cohomology zero, any `n₀` works. `X = ∅` (with `R ≠ 0`): same.
`p = 0` is excluded (`0 < p`). `n₀ = 0` is allowed. `F = 0`: trivial. `L = O_X`, `X = Spec R`: `H^p = 0`
for `p > 0` on an affine scheme (Stacks 01XB), consistent. -/
theorem AlgebraicGeometry.sheafCohomology_tensor_pow_subsingleton_of_isAmple_of_isProper_over_noetherianRing
    {R : CommRingCat.{u}} [IsNoetherianRing R] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec R) [AlgebraicGeometry.IsProper f]
    (L : X.Modules) [L.IsLineBundle] (hL : AlgebraicGeometry.IsAmple L)
    (F : X.Modules) [F.IsCoherent] :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p : ℕ, 0 < p →
      Subsingleton (CategoryTheory.Sheaf.H
        (AlgebraicGeometry.Scheme.Modules.tensor F
          (AlgebraicGeometry.Scheme.Modules.tensorPow L n)).toAddCommGrpSheaf p) := by
  classical
  -- Step 1: closed immersion `i : X ⟶ P^N_R` with `i^*O(1) ≅ L^{⊗d}`
  obtain ⟨d, N, hd, i, hci, -, ⟨e⟩⟩ :=
    AlgebraicGeometry.exists_closedImmersion_projectiveSpaceOver_pullback_twist_iso (R := R) f L hL
  haveI : AlgebraicGeometry.IsClosedImmersion i := hci
  haveI : AlgebraicGeometry.IsLocallyNoetherian (ProjectiveSpaceOver N R) :=
    ProjectiveSpaceOver.isLocallyNoetherian' R N
  haveI : AlgebraicGeometry.IsFinite i :=
    ((AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono i).1 hci).1
  -- the coherent sheaves `G_q := i_*(F ⊗ L^{⊗q})` on `P^N_R`
  let G : ℕ → (ProjectiveSpaceOver N R).Modules := fun q =>
    (AlgebraicGeometry.Scheme.Modules.pushforward i).obj
      (F.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow L q))
  have hG : ∀ q, (G q).IsCoherent := fun q => by
    haveI : (F.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow L q)).IsCoherent :=
      isCoherent_tensor_of_isLineBundle_over F _
    exact AlgebraicGeometry.Scheme.Modules.isCoherent_pushforward_of_isFinite i _
  -- Step 4: Serre vanishing on `P^N_R` for each `q` and each `0 < p`
  have hSerre : ∀ q p : ℕ, 0 < p → ∃ n₀ : ℕ, ∀ m ≥ n₀, Subsingleton (CategoryTheory.Sheaf.H
      ((G q).tensor (projectiveSpaceOverTwist R N m)).toAddCommGrpSheaf p) := fun q p hp =>
    haveI := hG q
    AlgebraicGeometry.sheafCohomology_tensor_twist_subsingleton_projectiveSpaceOver R N (G q) p hp
  choose! nqp hnqp using hSerre
  -- Step 5: the uniform bound
  let M : ℕ := (Finset.range d ×ˢ Finset.range (N + 1)).sup (fun qp => nqp qp.1 qp.2)
  refine ⟨d * M, fun n hn p hp => ?_⟩
  -- the twist on `P^N_R` vanishes
  have hvanish : Subsingleton (CategoryTheory.Sheaf.H
      ((G (n % d)).tensor (projectiveSpaceOverTwist R N (n / d))).toAddCommGrpSheaf p) := by
    by_cases hpN : N < p
    · haveI := hG (n % d)
      haveI : ((G (n % d)).tensor (projectiveSpaceOverTwist R N (n / d))).IsQuasicoherent :=
        (isCoherent_tensor_of_isLineBundle_over (G (n % d)) _).quasicoherent
      exact AlgebraicGeometry.sheafCohomology_projectiveSpaceOver_subsingleton_of_lt N _ p hpN
    · have hmem : (n % d, p) ∈ Finset.range d ×ˢ Finset.range (N + 1) := by
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
        exact ⟨Nat.mod_lt n hd, by omega⟩
      have hM : nqp (n % d) p ≤ M := Finset.le_sup (f := fun qp => nqp qp.1 qp.2) hmem
      have hm : M ≤ n / d := (Nat.le_div_iff_mul_le hd).2 (by rw [mul_comm]; exact hn)
      exact hnqp (n % d) p hp (n / d) (hM.trans hm)
  -- Step 3: transport along `i` (02UV) and the projection formula
  have hX' : Subsingleton (CategoryTheory.Sheaf.H
      ((F.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow L (n % d))).tensor
        ((AlgebraicGeometry.Scheme.Modules.pullback i).obj
          (projectiveSpaceOverTwist R N (n / d)))).toAddCommGrpSheaf p) := by
    haveI : Subsingleton (CategoryTheory.Sheaf.H
        ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj
          ((F.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow L (n % d))).tensor
            ((AlgebraicGeometry.Scheme.Modules.pullback i).obj
              (projectiveSpaceOverTwist R N (n / d))))).toAddCommGrpSheaf p) :=
      CategoryTheory.Sheaf.subsingleton_H_of_iso (hF := hvanish)
        ((SheafOfModules.toSheaf (ProjectiveSpaceOver N R).ringCatSheaf).mapIso
          (AlgebraicGeometry.Scheme.Modules.pushforwardTensorPullbackIso i _ _).symm) p
    exact (AlgebraicGeometry.Scheme.Modules.sheafCohomologyClosedImmersionAddEquiv i _ p).toEquiv.subsingleton
  -- Step 2: `F ⊗ L^{⊗n} ≅ (F ⊗ L^{⊗(n % d)}) ⊗ i^*O(n / d)`
  obtain ⟨t⟩ := AlgebraicGeometry.Scheme.Modules.tensor_tensorPow_add_mul_iso_tensor_pullback_twist_over
    i L e F (n % d) (n / d)
  rw [Nat.mod_add_div n d] at t
  exact CategoryTheory.Sheaf.subsingleton_H_of_iso (hF := hX')
    ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso t.symm) p

end
