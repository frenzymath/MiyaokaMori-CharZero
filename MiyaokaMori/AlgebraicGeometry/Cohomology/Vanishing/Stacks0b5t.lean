import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.IsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ClosedImmersionProjectionFormula
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesFiniteTypeInstances
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01y6
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks0b5tClosedImmersion
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks0b5tProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks0b5tTwistTransport
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.Stacks02uv
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ce01id
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # Serre vanishing (Stacks 0B5T(4))

Serre vanishing (Stacks 0B5T(4)): for a proper scheme `X` over a field, an ample invertible sheaf `L` and a
coherent sheaf `F`, `H^p(X, F ⊗ L^n) = 0` for `p > 0` and `n ≫ 0`.

Source: Stacks 0B5T(4) (used in the proof of Lazarsfeld, *Positivity in Algebraic Geometry I*, Thm 1.2.23 for
the vanishing of higher cohomology of the restrictions to `A`, `B`, `D`).

## Proof (Stacks 0B5T, proof of (4))

1. **Closed immersion into projective space** (`exists_closedImmersion_projectiveSpace_pullback_twist_iso`):
   since `X` is proper over `k` and `L` is
   ample, there are `d > 0`, `N`, and a closed immersion `i : X ⟶ P^N_k` over `k` with `i^*O(1) ≅ L^{⊗d}`
   (Stacks 01VU/01VR give an immersion; proper + separated target makes it a closed immersion).
2. **Reduction to `d` residue classes.** Write `n = q + d m` with `q = n % d`, `m = n / d`. Then
   `F ⊗ L^{⊗n} ≅ (F ⊗ L^{⊗q}) ⊗ i^*O(m)` (`Stacks0b5tTwistTransport.lean`).
3. **Closed immersions preserve cohomology and coherence.** `H^p(X, G ⊗ i^*O(m)) ≅ H^p(P^N, i_*(G ⊗ i^*O(m)))`
   (Stacks 02UV, `sheafCohomologyClosedImmersionAddEquiv`), and by the projection formula
   `i_*(G ⊗ i^*O(m)) ≅ i_*G ⊗ O(m)` (projection formula for closed immersions). For `G = F ⊗ L^{⊗q}`
   coherent, `i_*G` is coherent on the Noetherian scheme `P^N_k` (Stacks 01Y6, closed immersions are finite).
4. **Serre vanishing on `P^N_k`** (`Stacks0b5tProjectiveSpace.lean`): for each coherent `G_q := i_*(F ⊗ L^{⊗q})`,
   `0 ≤ q < d`, and each `0 < p ≤ N`, there is `n_{q,p}` with `H^p(P^N, G_q ⊗ O(m)) = 0` for `m ≥ n_{q,p}`;
   for `p > N` all quasi-coherent cohomology of `P^N` vanishes (Čech bound,
   `sheafCohomology_projectiveSpace_subsingleton_of_lt`).
5. **Uniform bound.** Let `M := max_{q < d, p ≤ N} n_{q,p}` and `n₀ := d · M`. For `n ≥ n₀` we have
   `m = n / d ≥ M`, so for every `p > 0` the group in step 3 vanishes; transporting back along the
   isomorphisms of steps 2–3 gives `H^p(X, F ⊗ L^{⊗n}) = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Coherent `⊗` line bundle is coherent (quasi-coherence: Stacks 01CE, `isQuasicoherent_tensor`; finite
type: `tensor_isFiniteType`). Same as `Stacks0bemTwist.isCoherent_tensor_of_isLineBundle`, which cannot
be imported here (it depends on `Stacks02o5`, which imports this file). -/
private theorem isCoherent_tensor_of_isLineBundle' {X : AlgebraicGeometry.Scheme.{u}}
    (G M : X.Modules) [G.IsCoherent] [M.IsLineBundle] :
    (AlgebraicGeometry.Scheme.Modules.tensor G M).IsCoherent := by
  haveI hq : G.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
  haveI hf : G.IsFiniteType := AlgebraicGeometry.Scheme.Modules.IsCoherent.finiteType
  -- the line bundle `M` is quasi-coherent and of finite type; both instances are given explicitly because
  -- instance search does not find them through the imports
  haveI hMq : M.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.IsLineBundle.isQuasicoherent M
  haveI hMf : M.IsFiniteType := AlgebraicGeometry.Scheme.Modules.IsLineBundle.isFiniteType M
  exact ⟨AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensor G M,
    AlgebraicGeometry.Scheme.Modules.tensor_isFiniteType G M⟩

theorem AlgebraicGeometry.sheafCohomology_tensor_pow_subsingleton_of_isAmple {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) (L : X.Modules) [L.IsLineBundle] (hL : AlgebraicGeometry.IsAmple L)
    (F : X.Modules) [F.IsCoherent] :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p : ℕ, 0 < p →
      Subsingleton (CategoryTheory.Sheaf.H
        (AlgebraicGeometry.Scheme.Modules.tensor F (AlgebraicGeometry.Scheme.Modules.tensorPow L n)).toAddCommGrpSheaf p) := by
  classical
  -- Step 1: closed immersion `i : X ⟶ P^N_k` with `i^*O(1) ≅ L^{⊗d}`
  obtain ⟨d, N, hd, i, hci, -, ⟨e⟩⟩ :=
    AlgebraicGeometry.exists_closedImmersion_projectiveSpace_pullback_twist_iso X hX L hL
  haveI : AlgebraicGeometry.IsClosedImmersion i := hci
  haveI : AlgebraicGeometry.IsLocallyNoetherian (ProjectiveSpace N k) :=
    ProjectiveSpace.isLocallyNoetherian k N
  haveI : AlgebraicGeometry.IsFinite i :=
    ((AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono i).1 hci).1
  -- the coherent sheaves `G_q := i_*(F ⊗ L^{⊗q})` on `P^N`
  let G : ℕ → (ProjectiveSpace N k).Modules := fun q =>
    (AlgebraicGeometry.Scheme.Modules.pushforward i).obj
      (F.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow L q))
  have hG : ∀ q, (G q).IsCoherent := fun q => by
    haveI : (F.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow L q)).IsCoherent :=
      isCoherent_tensor_of_isLineBundle' F _
    exact AlgebraicGeometry.Scheme.Modules.isCoherent_pushforward_of_isFinite i _
  -- Step 4: Serre vanishing on `P^N` for each `q` and each `0 < p`
  have hSerre : ∀ q p : ℕ, 0 < p → ∃ n₀ : ℕ, ∀ m ≥ n₀, Subsingleton (CategoryTheory.Sheaf.H
      ((G q).tensor (projectiveSpaceTwist k N m)).toAddCommGrpSheaf p) := fun q p hp =>
    haveI := hG q
    AlgebraicGeometry.sheafCohomology_tensor_twist_subsingleton_projectiveSpace N (G q) p hp
  choose! nqp hnqp using hSerre
  -- Step 5: the uniform bound
  let M : ℕ := (Finset.range d ×ˢ Finset.range (N + 1)).sup (fun qp => nqp qp.1 qp.2)
  refine ⟨d * M, fun n hn p hp => ?_⟩
  -- the twist on `P^N` vanishes
  have hvanish : Subsingleton (CategoryTheory.Sheaf.H
      ((G (n % d)).tensor (projectiveSpaceTwist k N (n / d))).toAddCommGrpSheaf p) := by
    by_cases hpN : N < p
    · haveI := hG (n % d)
      haveI : ((G (n % d)).tensor (projectiveSpaceTwist k N (n / d))).IsQuasicoherent :=
        (isCoherent_tensor_of_isLineBundle' (G (n % d)) _).quasicoherent
      exact AlgebraicGeometry.sheafCohomology_projectiveSpace_subsingleton_of_lt N _ p hpN
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
          (projectiveSpaceTwist k N (n / d)))).toAddCommGrpSheaf p) := by
    haveI : Subsingleton (CategoryTheory.Sheaf.H
        ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj
          ((F.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow L (n % d))).tensor
            ((AlgebraicGeometry.Scheme.Modules.pullback i).obj
              (projectiveSpaceTwist k N (n / d))))).toAddCommGrpSheaf p) :=
      CategoryTheory.Sheaf.subsingleton_H_of_iso (hF := hvanish)
        ((SheafOfModules.toSheaf (ProjectiveSpace N k).ringCatSheaf).mapIso
          (AlgebraicGeometry.Scheme.Modules.pushforwardTensorPullbackIso i _ _).symm) p
    exact (AlgebraicGeometry.Scheme.Modules.sheafCohomologyClosedImmersionAddEquiv i _ p).toEquiv.subsingleton
  -- Step 2: `F ⊗ L^{⊗n} ≅ (F ⊗ L^{⊗(n % d)}) ⊗ i^*O(n / d)`
  obtain ⟨t⟩ := AlgebraicGeometry.Scheme.Modules.tensor_tensorPow_add_mul_iso_tensor_pullback_twist
    i L e F (n % d) (n / d)
  rw [Nat.mod_add_div n d] at t
  exact CategoryTheory.Sheaf.subsingleton_H_of_iso (hF := hX')
    ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso t.symm) p

end
