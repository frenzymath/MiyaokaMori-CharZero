import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRatPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.ProjectionFormula
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOfClosedSubscheme
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.SnapperEqChowZeroDim
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.Stacks0bes

/-! # Snapper = Chow: reduction to integral schemes

Fix a field `k` and `d`. If the identity "`χ`-intersection number `(L_1⋯L_d·X) = deg(c_1(L_1) ∩ ⋯ ∩ c_1(L_d) ∩ [X]_d)`"
holds for all **integral** `d`-dimensional schemes `X` proper over `k` and all families of invertible
sheaves, then it holds for all `d`-dimensional locally Noetherian schemes proper over `k` (i.e. `P(k, d)`,
see `SnapperEqChowZeroDim.lean`).

Proof:
1. Let `X` be proper of dimension `d`. Stacks 0BES gives finitely many integral closed subschemes
   `e_j : Z_j → X` (`dim Z_j = d`) and multiplicities `m_j` with `[X]_d = Σ m_j [e_j(ξ_j)]` (`ξ_j` the
   generic point of `Z_j`) and `(L_1⋯L_d·X) = Σ m_j (e_j^*L_1⋯e_j^*L_d·Z_j)`.
2. Each `Z_j` is proper over `k` (`isProperOver_of_closedImmersion`), locally Noetherian, integral and
   `d`-dimensional, so by hypothesis `(e_j^*L·Z_j) = deg(c_1(e_j^*L_1) ∩ ⋯ ∩ [Z_j]_d)`.
3. `Z_j` is integral and finite-dimensional, so `[Z_j]_d` is the cycle with coefficient `1` at the generic
   point `ξ_j` (`fundamentalCycle_of_isIntegral_of_isOfFiniteType`). A closed immersion pushes forward with
   coefficient `1` (isomorphic residue fields), so `e_{j*}[Z_j]_d = [e_j(ξ_j)]`, hence
   `[X]_d = Σ m_j e_{j*}[Z_j]_d` in `CH_d(X)` (`chowPushforward` takes its positive branch on closed
   immersions, Stacks 02S2).
4. Projection formula (`chowPushforward_firstChernClass_pullback`, applied to each `c_1`, `d` times; still
   valid after `ratExtend`): `c_1(L_1) ∩ ⋯ ∩ c_1(L_d) ∩ e_{j*}[Z_j] = e_{j*}(c_1(e_j^*L_1) ∩ ⋯ ∩ c_1(e_j^*L_d) ∩ [Z_j])`.
   The order of the factors in `capProd` is given by `Finset.univ.toList`, the same for `L` and `e_j^*L`, so
   no commutativity is needed.
5. The degree is compatible with proper pushforward, and `capProd` and `degree` are linear, so the right
   side is `Σ_j m_j deg(c_1(e_j^*L_1) ∩ ⋯ ∩ [Z_j]_d)`; combine with steps 1 and 2.

Source: the reduction to irreducible components in the proof of Stacks 0BFI (using 0BES and 02SU).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.SnapperEqChowReduceToIntegral

open AlgebraicGeometry

/-! ### Transport lemmas for the index transport `ChowGroupRat.congr` (all `subst; rfl`) -/

/-- `h ▸ z` (the spelling in the target statement) is `ChowGroupRat.congr`. -/
theorem congr_eq_rec {X : Scheme.{u}} {a b : ℕ} (h : a = b) (z : ChowGroupRat X a) :
    (h ▸ z : ChowGroupRat X b) = ChowGroupRat.congr X h z := by
  subst h; rfl

theorem congr_congr {X : Scheme.{u}} {a b c : ℕ} (h1 : a = b) (h2 : b = c)
    (z : ChowGroupRat X a) :
    ChowGroupRat.congr X h2 (ChowGroupRat.congr X h1 z) = ChowGroupRat.congr X (h1.trans h2) z := by
  subst h1; subst h2; rfl

theorem congr_refl {X : Scheme.{u}} {a : ℕ} (h : a = a) (z : ChowGroupRat X a) :
    ChowGroupRat.congr X h z = z := rfl

/-- The transport commutes with the pushforward. -/
theorem congr_chowPushforwardRat {Z X : Scheme.{u}} (p : Z ⟶ X) [IsProper p] {a b : ℕ} (h : a = b)
    (β : ChowGroupRat Z a) :
    ChowGroupRat.congr X h (chowPushforwardRat p a β)
      = chowPushforwardRat p b (ChowGroupRat.congr Z h β) := by
  subst h; rfl

/-- The transport commutes with divisor operators. -/
theorem congr_ratDivisorOp {X : Scheme.{u}} (D : RatDivisorOp X) {a b : ℕ} (h : a = b)
    (γ : ChowGroupRat X (a + 1)) :
    ChowGroupRat.congr X h (D a γ) = D b (ChowGroupRat.congr X (congrArg (· + 1) h) γ) := by
  subst h; rfl

/-! ### The projection formula with ℚ-coefficients (single step and iterated) -/

/-- Single step: `p_*(c_1(p^*L) ∩ β) = c_1(L) ∩ p_* β` with ℚ-coefficients (the projection formula tensored
with ℚ). -/
theorem chowPushforwardRat_ratDivisorOpOfLineBundle_pullback {k : Type u} [Field k]
    {Z X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k))] [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (p : Z ⟶ X) [p.IsOver (Spec (CommRingCat.of k))] [IsProper p]
    (L : X.Modules) [L.IsLineBundle] (n : ℕ) (β : ChowGroupRat Z (n + 1)) :
    chowPushforwardRat p n (ratDivisorOpOfLineBundle ((Scheme.Modules.pullback p).obj L) n β)
      = ratDivisorOpOfLineBundle L n (chowPushforwardRat p (n + 1) β) := by
  revert β
  show ∀ β : TensorProduct ℤ ℚ (ChowGroup Z (n + 1)), _
  intro β
  induction β using TensorProduct.induction_on with
  | zero =>
    have e1 := LinearMap.map_zero (chowPushforwardRat p n ∘ₗ
      ratDivisorOpOfLineBundle ((Scheme.Modules.pullback p).obj L) n)
    have e2 := LinearMap.map_zero (ratDivisorOpOfLineBundle L n ∘ₗ chowPushforwardRat p (n + 1))
    simp only [LinearMap.comp_apply] at e1 e2
    exact e1.trans e2.symm
  | tmul q c =>
    change q ⊗ₜ[ℤ] (chowPushforward p n
        (firstChernClass ((Scheme.Modules.pullback p).obj L) (n + 1) c))
      = q ⊗ₜ[ℤ] (firstChernClass L (n + 1) (chowPushforward p (n + 1) c))
    rw [chowPushforward_firstChernClass_pullback (k := k) p L n c]
  | add a b ha hb =>
    have e1 := LinearMap.map_add (chowPushforwardRat p n ∘ₗ
      ratDivisorOpOfLineBundle ((Scheme.Modules.pullback p).obj L) n) a b
    have e2 := LinearMap.map_add
      (ratDivisorOpOfLineBundle L n ∘ₗ chowPushforwardRat p (n + 1)) a b
    simp only [LinearMap.comp_apply] at e1 e2
    exact e1.trans ((congrArg₂ (· + ·) ha hb).trans e2.symm)

/-- Iterated: the pushforward of successive caps with the `p^*L_i` along the list `s` equals the successive
caps with the `L_i` (same order of factors). -/
theorem chowPushforwardRat_capList_pullback {k : Type u} [Field k]
    {Z X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k))] [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (p : Z ⟶ X) [p.IsOver (Spec (CommRingCat.of k))] [IsProper p]
    {ι : Type} (L : ι → X.Modules) [∀ i, (L i).IsLineBundle] (s : List ι) :
    ∀ (d : ℕ) (β : ChowGroupRat Z (d + (s.map fun i =>
        ratDivisorOpOfLineBundle ((Scheme.Modules.pullback p).obj (L i))).length)),
      chowPushforwardRat p d
          (RatDivisorOp.capList
            (s.map fun i => ratDivisorOpOfLineBundle ((Scheme.Modules.pullback p).obj (L i))) d β)
        = RatDivisorOp.capList (s.map fun i => ratDivisorOpOfLineBundle (L i)) d
            (ChowGroupRat.congr X (by simp) (chowPushforwardRat p _ β)) := by
  induction s with
  | nil =>
    intro d β
    rfl
  | cons i t ih =>
    intro d β
    have ih' := ih d
      (ratDivisorOpOfLineBundle ((Scheme.Modules.pullback p).obj (L i))
        (d + (t.map fun i =>
          ratDivisorOpOfLineBundle ((Scheme.Modules.pullback p).obj (L i))).length) β)
    rw [chowPushforwardRat_ratDivisorOpOfLineBundle_pullback (k := k) p (L i),
      congr_ratDivisorOp] at ih'
    exact ih'

/-- The `capProd` form of the projection formula: `p_*(∏ c_1(p^*L_i) ∩ β) = ∏ c_1(L_i) ∩ p_* β` (both with
the factor order `Finset.univ.toList`). -/
theorem chowPushforwardRat_capProd_pullback {k : Type u} [Field k]
    {Z X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k))] [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (p : Z ⟶ X) [p.IsOver (Spec (CommRingCat.of k))] [IsProper p]
    {ι : Type} [Fintype ι] [DecidableEq ι] (L : ι → X.Modules) [∀ i, (L i).IsLineBundle]
    (β : ChowGroupRat Z (0 + Fintype.card ι)) :
    chowPushforwardRat p 0
        (RatDivisorOp.capProd
          (fun i => ratDivisorOpOfLineBundle ((Scheme.Modules.pullback p).obj (L i))) 0 β)
      = RatDivisorOp.capProd (fun i => ratDivisorOpOfLineBundle (L i)) 0
          (chowPushforwardRat p _ β) := by
  unfold RatDivisorOp.capProd
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    chowPushforwardRat_capList_pullback (k := k) p L (Finset.univ : Finset ι).toList 0,
    ← congr_chowPushforwardRat, congr_congr]

/-- Degree and `capProd` along the pushforward by a proper `k`-morphism:
`deg_X(∏ c_1(L_i) ∩ p_* α) = deg_Z(∏ c_1(p^*L_i) ∩ α)`. -/
theorem degree_capProd_chowPushforwardRat {k : Type u} [Field k]
    {Z X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k))] [X.Over (Spec (CommRingCat.of k))]
    (hZ : IsProperOver k Z) (hX : IsProperOver k X)
    (p : Z ⟶ X) [p.IsOver (Spec (CommRingCat.of k))] [IsProper p]
    {d : ℕ} (L : Fin d → X.Modules) [∀ i, (L i).IsLineBundle] (α : ChowGroupRat Z d) :
    ChowGroupRat.degree X hX
        (RatDivisorOp.capProd (fun i => ratDivisorOpOfLineBundle (L i)) 0
          ((by simp : d = 0 + Fintype.card (Fin d)) ▸ chowPushforwardRat p d α))
      = ChowGroupRat.degree Z hZ
          (RatDivisorOp.capProd
            (fun i => ratDivisorOpOfLineBundle ((Scheme.Modules.pullback p).obj (L i))) 0
            ((by simp : d = 0 + Fintype.card (Fin d)) ▸ α)) := by
  have : IsProper (Z ↘ Spec (CommRingCat.of k)) := hZ
  have : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
  rw [congr_eq_rec, congr_eq_rec, congr_chowPushforwardRat,
    ← chowPushforwardRat_capProd_pullback (k := k) p L,
    ChowGroupRat.degree_chowPushforwardRat hZ hX p]

/-! ### Integer coefficients: pushforward of the fundamental cycle of an integral scheme along a closed immersion -/

open Classical in
/-- For `Z` integral, proper over `k`, of dimension `d`, and `e : Z → X` a closed immersion, `e_*[Z]_d` is
the cycle with coefficient `1` at the image point `e(ξ_Z)` (`[Z]_d = [ξ_Z]`; a closed immersion pushes
forward with the original coefficient at image points, `properPushforward_closedImmersion_apply`, and `0`
outside the image). -/
theorem properPushforward_fundamentalCycle_apply {k : Type u} [Field k]
    {Z X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k))] (hZ : IsProperOver k Z)
    (e : Z ⟶ X) [IsClosedImmersion e] [IsIntegral Z] [IsLocallyNoetherian Z]
    {d : ℕ} (hdZ : Z.dimension = d) (x : X) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward e (Z.fundamentalCycle d) x
      = if x = e.base (genericPoint Z) then 1 else 0 := by
  have : IsProper (Z ↘ Spec (CommRingCat.of k)) := hZ
  have : IsOfFiniteType (Z ↘ Spec (CommRingCat.of k)) := {}
  have hfc := Z.fundamentalCycle_of_isIntegral_of_isOfFiniteType (k := k)
  rw [hdZ] at hfc
  by_cases hx : x ∈ Set.range e.base
  · obtain ⟨y, rfl⟩ := hx
    rw [MiyaokaMori.FirstChernCapPointGeneric.properPushforward_closedImmersion_apply,
      congrFun hfc y]
    simp only [e.isClosedEmbedding.injective.eq_iff]
  · rw [MiyaokaMori.ClosedImmersionPushforward.properPushforward_apply_of_notMem_range e _ hx,
      if_neg]
    rintro rfl
    exact hx ⟨_, rfl⟩

open Classical in
/-- In the Chow group: `[X]_d = Σ_j m_j e_{j*}[Z_j]_d`, given the cycle-level 0BES decomposition
`[X]_d = Σ_j m_j [e_j(ξ_j)]`. -/
theorem fundamentalChowClass_eq_sum_chowPushforward {k : Type u} [Field k]
    (X : Scheme.{u}) [IsLocallyNoetherian X] {d : ℕ}
    {ι : Type} [Fintype ι] (m : ι → ℕ) (Z : ι → Scheme.{u})
    [∀ j, (Z j).Over (Spec (CommRingCat.of k))] (hZ : ∀ j, IsProperOver k (Z j))
    (e : ∀ j, Z j ⟶ X) [∀ j, IsClosedImmersion (e j)] [∀ j, IsIntegral (Z j)]
    [∀ j, IsLocallyNoetherian (Z j)] (hdZ : ∀ j, (Z j).dimension = d)
    (hcycle : ∀ x : X, X.fundamentalCycle d x
      = ∑ j, (m j : ℤ) * (if x = (e j).base (genericPoint (Z j)) then 1 else 0)) :
    X.fundamentalChowClass d
      = ∑ j, (m j : ℤ) • chowPushforward (e j) d ((Z j).fundamentalChowClass d) := by
  classical
  have hdesc : ∀ j, PushforwardDescends (e j) d := fun j =>
    pushforwardDescends_of_isClosedImmersion (e j) d
  unfold Scheme.fundamentalChowClass
  rw [Finset.sum_congr rfl (fun j _ => by
    rw [chowPushforward_mk (e j) d (hdesc j), ← map_zsmul ChowGroup.mk]), ← map_sum]
  congr 1
  apply Subtype.ext
  apply DFunLike.ext
  intro x
  rw [hcycle x, AddSubmonoidClass.coe_finsetSum, Function.locallyFinsuppWithin.coe_sum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [AddSubgroupClass.coe_zsmul, Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
    smul_eq_mul]
  congr 1
  exact (properPushforward_fundamentalCycle_apply (k := k) (hZ j) (e j) (hdZ j) x).symm

end MiyaokaMori.SnapperEqChowReduceToIntegral

open MiyaokaMori.SnapperEqChowReduceToIntegral in
set_option linter.style.haveILetI false in
/-- **Reduction to integral schemes**: if Snapper = Chow holds for all integral `d`-dimensional schemes
projective over `k`, then `SnapperEqChowInDim k d`. The hypothesis and conclusion are stated for schemes
**projective** over `k`; the projectivity of each `d`-dimensional integral closed subscheme `Z_j` follows
from that of `X` by `IsProjectiveOver.of_isClosedImmersion`, so no Chow's lemma is needed.

Proof, following the five steps of the module docstring: the 0BES decomposition
(`snapperIntersection_eq_sum_components`) → each `Z_j` proper, projective, locally Noetherian
(`LocallyOfFiniteType.isLocallyNoetherian`) → the hypothesis `h` →
`[X]_d = Σ m_j e_{j*}[Z_j]_d` (`fundamentalChowClass_eq_sum_chowPushforward`) → the ℚ-projection formula
`d` times (`chowPushforwardRat_capProd_pullback`) → compatibility of the degree with the pushforward
(`degree_capProd_chowPushforwardRat`). -/
theorem AlgebraicGeometry.snapperEqChowInDim_of_integral (k : Type u) [Field k] (d : ℕ)
    (h : ∀ (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
      (hX : IsProperOver k X) (_ : IsProjectiveOver k X)
      [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsIntegral X]
      (hd : X.dimension = d) (L : Fin d → X.Modules) [∀ i, (L i).IsLineBundle],
      AlgebraicGeometry.SnapperEqChowFor X hX hd L) :
    AlgebraicGeometry.SnapperEqChowInDim k d := by
  intro X _ hX hXproj _ hd L _
  obtain ⟨ι, _, m, Z, e, he, hZint, hdZ, hcycle, hsnap⟩ :=
    AlgebraicGeometry.snapperIntersection_eq_sum_components X hX hd L
  letI : ∀ j, (Z j).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) := fun j =>
    ⟨e j ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have : ∀ j, (e j).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := fun j => ⟨rfl⟩
  have hZ : ∀ j, IsProperOver k (Z j) := fun j => isProperOver_of_closedImmersion hX (e j)
  have : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hX
  have hZLN : ∀ j, AlgebraicGeometry.IsLocallyNoetherian (Z j) := fun j =>
    have : AlgebraicGeometry.IsProper ((Z j) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hZ j
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      ((Z j) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have hZproj : ∀ j, IsProjectiveOver k (Z j) := fun j =>
    IsProjectiveOver.of_isClosedImmersion (e j) hXproj
  unfold AlgebraicGeometry.SnapperEqChowFor
  rw [hsnap, fundamentalChowClass_eq_sum_chowPushforward (k := k) X m Z hZ e hdZ hcycle]
  have hof : ((1 : ℚ) ⊗ₜ[ℤ] (∑ j, (m j : ℤ) •
        AlgebraicGeometry.chowPushforward (e j) d ((Z j).fundamentalChowClass d)) :
        AlgebraicGeometry.ChowGroupRat X d)
      = ∑ j, (m j : ℤ) • (AlgebraicGeometry.chowPushforwardRat (e j) d
          ((1 : ℚ) ⊗ₜ[ℤ] (Z j).fundamentalChowClass d)) := by
    change AlgebraicGeometry.ChowGroupRat.of _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul]
    rfl
  rw [hof, congr_eq_rec, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, map_zsmul, map_zsmul, zsmul_eq_mul, Int.cast_natCast]
  congr 1
  refine (h (Z j) (hZ j) (hZproj j) (hdZ j) fun i =>
    (AlgebraicGeometry.Scheme.Modules.pullback (e j)).obj (L i)).trans ?_
  rw [← degree_capProd_chowPushforwardRat (k := k) (hZ j) hX (e j) L
    ((1 : ℚ) ⊗ₜ[ℤ] (Z j).fundamentalChowClass d), congr_eq_rec]


end
