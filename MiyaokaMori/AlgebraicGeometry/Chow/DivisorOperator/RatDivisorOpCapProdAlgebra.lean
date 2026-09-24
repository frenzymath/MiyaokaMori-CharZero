import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.ChowGroupRatCongr
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforwardScheme
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.CapListPerm
import MiyaokaMori.AlgebraicGeometry.Chow.CapTrivialBundleZero
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.ProjectionFormula
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOpSpanCommute
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassTensor

/-! # Chow-side algebra for the projective step of Snapper = Chow

Helper lemmas for the projective step of `SnapperEqChowProjectiveStep.lean` (Stacks 0BFI, second half), all pure
algebra on `RatDivisorOp.capProd` (no new geometric content):

* `RatDivisorOp.capProd_succ`: peel off the factor of index `0` of a `Fin (d+1)`-indexed cap product
  (it is applied first); this is the commutativity of cap products in the form actually needed
  (`capList_perm` along the permutation `univ ~ 0 :: univ.map succ`).
* `ratDivisorOpOfLineBundle_tensor` / `_unit` / `_congr`: the ℚ-divisor operator of a line bundle is
  additive under `⊗`, vanishes on `O_X` and only depends on the isomorphism class.
* `RatDivisorOp.capProd_chowPushforwardRat`: the projection formula
  (`chowPushforward_firstChernClass_pullback`) iterated over a cap product.

Index bookkeeping: `Fintype.card (Fin d)` is not definitionally `d`, so the dimension indices are
moved with `ChowGroupRat.congr`; all such moves are proved by `subst; rfl`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ## `ChowGroupRat.congr` bookkeeping -/

/-- Composition of two index transports. -/
theorem ChowGroupRat.congr_trans {p q r : ℕ} (h : p = q) (h' : q = r) (α : ChowGroupRat X p) :
    ChowGroupRat.congr X h' (ChowGroupRat.congr X h α) = ChowGroupRat.congr X (h.trans h') α := by
  subst h; subst h'; rfl

theorem ChowGroupRat.congr_self {p : ℕ} (h : p = p) (α : ChowGroupRat X p) :
    ChowGroupRat.congr X h α = α := rfl

/-- An operator commutes with the index cast. -/
theorem RatDivisorOp.apply_congr (D : RatDivisorOp X) {p q : ℕ} (h : p = q)
    (h1 : p + 1 = q + 1) (α : ChowGroupRat X (p + 1)) :
    D q (ChowGroupRat.congr X h1 α) = ChowGroupRat.congr X h (D p α) := by
  subst h; rfl

/-- `chowPushforwardRat` commutes with the index cast. -/
theorem chowPushforwardRat_congr_index {Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] {p q : ℕ} (h : p = q)
    (α : ChowGroupRat X p) :
    chowPushforwardRat f q (ChowGroupRat.congr X h α)
      = ChowGroupRat.congr Y h (chowPushforwardRat f p α) := by
  subst h; rfl

theorem RatDivisorOp.capList_cons_apply (E : RatDivisorOp X) (l : List (RatDivisorOp X)) (n : ℕ)
    (α : ChowGroupRat X (n + (E :: l).length)) :
    RatDivisorOp.capList (E :: l) n α = RatDivisorOp.capList l n (E (n + l.length) α) := rfl

/-! ## Peeling off the first factor -/

/-- The set of ℚ-divisor operators spanned by line-bundle operators (as in `capProd_comm`). -/
abbrev RatDivisorOp.lineBundleSpan (X : Scheme.{u}) : Submodule ℚ (RatDivisorOp X) :=
  Submodule.span ℚ {D' : RatDivisorOp X |
    ∃ (L : X.Modules) (_ : L.IsLineBundle), D' = ratDivisorOpOfLineBundle L}

theorem ratDivisorOpOfLineBundle_mem_lineBundleSpan (L : X.Modules) [L.IsLineBundle] :
    ratDivisorOpOfLineBundle L ∈ RatDivisorOp.lineBundleSpan X :=
  Submodule.subset_span ⟨L, inferInstance, rfl⟩

/-- The universe of `Fin (d+1)` is a permutation of `0 :: (succ '' univ)`, as lists. -/
theorem Fin.univ_toList_perm_cons_succ (d : ℕ) :
    ((Finset.univ : Finset (Fin (d + 1))).toList).Perm
      (0 :: ((Finset.univ : Finset (Fin d)).toList.map Fin.succ)) := by
  rw [Fin.univ_succ]
  refine (Finset.toList_cons _).trans (List.Perm.cons _ ?_)
  rw [← Multiset.coe_eq_coe, Finset.coe_toList, Finset.map_val, ← Finset.coe_toList,
    Multiset.map_coe]
  rfl

/-- **Peeling off the factor of index 0.** For pairwise commuting operators (all in the ℚ-span of
line-bundle operators), the cap product over `Fin (d+1)` is: apply `D 0` first, then the cap product
over `Fin d` of the remaining factors. -/
theorem RatDivisorOp.capProd_succ {k : Type u} [Field k] [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    {d : ℕ} (D : Fin (d + 1) → RatDivisorOp X) (hD : ∀ j, D j ∈ RatDivisorOp.lineBundleSpan X)
    (n : ℕ) (h : n + d + 1 = n + Fintype.card (Fin (d + 1)))
    (h' : n + d = n + Fintype.card (Fin d)) (α : ChowGroupRat X (n + d + 1)) :
    RatDivisorOp.capProd D n (ChowGroupRat.congr X h α)
      = RatDivisorOp.capProd (D ∘ Fin.succ) n (ChowGroupRat.congr X h' (D 0 (n + d) α)) := by
  classical
  set l' : List (RatDivisorOp X) := (Finset.univ : Finset (Fin d)).toList.map (D ∘ Fin.succ)
    with hl'
  have hperm : ((Finset.univ : Finset (Fin (d + 1))).toList.map D).Perm (D 0 :: l') := by
    have := (Fin.univ_toList_perm_cons_succ d).map D
    rw [List.map_cons, List.map_map] at this
    exact this
  have hc : ∀ A ∈ (Finset.univ : Finset (Fin (d + 1))).toList.map D,
      ∀ B ∈ (Finset.univ : Finset (Fin (d + 1))).toList.map D, ∀ m : ℕ,
        (A m).comp (B (m + 1)) = (B m).comp (A (m + 1)) := by
    intro A hA B hB m
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hA
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hB
    exact RatDivisorOp.comp_comm_of_mem_span (k := k) _ _ (hD a) (hD b) m
  have hlen : l'.length = Fintype.card (Fin d) := by simp [hl']
  unfold RatDivisorOp.capProd
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    RatDivisorOp.capList_perm hperm hc n, LinearMap.comp_apply,
    ChowGroupRat.congr_trans, ChowGroupRat.congr_trans]
  rw [RatDivisorOp.capList_cons_apply,
    RatDivisorOp.apply_congr (D 0) (by rw [hlen]; exact h') _ α, ChowGroupRat.congr_trans]

/-! ## The line-bundle operator: additivity, unit, isomorphism invariance -/

theorem _root_.AddMonoidHom.ratExtend_add {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    (f g : M →+ N) : (f + g).ratExtend = f.ratExtend + g.ratExtend := by
  unfold AddMonoidHom.ratExtend
  have : (f + g).toIntLinearMap = f.toIntLinearMap + g.toIntLinearMap := LinearMap.ext fun _ => rfl
  rw [this, LinearMap.baseChange_add]

theorem _root_.AddMonoidHom.ratExtend_zero {M N : Type u} [AddCommGroup M] [AddCommGroup N] :
    (0 : M →+ N).ratExtend = 0 := by
  unfold AddMonoidHom.ratExtend
  have : (0 : M →+ N).toIntLinearMap = 0 := LinearMap.ext fun _ => rfl
  rw [this, LinearMap.baseChange_zero]

theorem _root_.AddMonoidHom.ratExtend_tmul {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    (f : M →+ N) (q : ℚ) (m : M) : f.ratExtend (q ⊗ₜ[ℤ] m) = q ⊗ₜ[ℤ] f m := rfl

/-- `c_1(L ⊗ M) = c_1(L) + c_1(M)` as ℚ-divisor operators. -/
theorem ratDivisorOpOfLineBundle_tensor {k : Type u} [Field k] [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (L M : X.Modules) [L.IsLineBundle] [M.IsLineBundle] [(Scheme.Modules.tensor L M).IsLineBundle] :
    ratDivisorOpOfLineBundle (Scheme.Modules.tensor L M)
      = ratDivisorOpOfLineBundle L + ratDivisorOpOfLineBundle M := by
  funext d
  show (firstChernClass (Scheme.Modules.tensor L M) (d + 1)).ratExtend
    = (firstChernClass L (d + 1)).ratExtend + (firstChernClass M (d + 1)).ratExtend
  rw [firstChernClass_tensor (k := k) L M (d + 1), AddMonoidHom.ratExtend_add]

/-- `c_1(O_X) = 0` as a ℚ-divisor operator. -/
theorem ratDivisorOpOfLineBundle_unit :
    ratDivisorOpOfLineBundle (SheafOfModules.unit X.ringCatSheaf : X.Modules) = 0 := by
  funext d
  show (firstChernClass (SheafOfModules.unit X.ringCatSheaf : X.Modules) (d + 1)).ratExtend = 0
  rw [firstChernClass_one X d, AddMonoidHom.ratExtend_zero]

/-- The ℚ-divisor operator only depends on the isomorphism class. -/
theorem ratDivisorOpOfLineBundle_congr (L L' : X.Modules) [L.IsLineBundle] [L'.IsLineBundle]
    (e : L ≅ L') : ratDivisorOpOfLineBundle L = ratDivisorOpOfLineBundle L' := by
  funext d
  show (firstChernClass L (d + 1)).ratExtend = (firstChernClass L' (d + 1)).ratExtend
  rw [firstChernClass_congr L L' e d]

/-! ## Projection formula for cap products -/

section Projection

variable {Y : Scheme.{u}} {k : Type u} [Field k]
  [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
  (p : X ⟶ Y) [p.IsOver (Spec (CommRingCat.of k))] [IsProper p]

include k p

/-- Projection formula, one operator, ℚ-coefficients:
`c_1(L) ∩ p_*(−) = p_*(c_1(p^*L) ∩ −)`. -/
theorem ratDivisorOpOfLineBundle_apply_chowPushforwardRat (L : Y.Modules) [L.IsLineBundle] (m : ℕ)
    (α : ChowGroupRat X (m + 1)) :
    ratDivisorOpOfLineBundle L m (chowPushforwardRat p (m + 1) α)
      = chowPushforwardRat p m (ratDivisorOpOfLineBundle ((Scheme.Modules.pullback p).obj L) m α) := by
  have h : ((firstChernClass L (m + 1)).comp (chowPushforward p (m + 1))).ratExtend
      = ((chowPushforward p m).comp
          (firstChernClass ((Scheme.Modules.pullback p).obj L) (m + 1))).ratExtend := by
    congr 1
    exact AddMonoidHom.ext fun β => (chowPushforward_firstChernClass_pullback (k := k) p L m β).symm
  rw [AddMonoidHom.ratExtend_comp, AddMonoidHom.ratExtend_comp] at h
  exact LinearMap.congr_fun h α

/-- Projection formula iterated along a list of line bundles. -/
theorem RatDivisorOp.capList_map_chowPushforwardRat {ι : Type*} (L : ι → Y.Modules)
    [∀ i, (L i).IsLineBundle] :
    ∀ (l : List ι) (n : ℕ) (α : ChowGroupRat X (n + l.length))
      (h : n + l.length = n + (l.map fun i => ratDivisorOpOfLineBundle (L i)).length)
      (h' : n + l.length
        = n + (l.map fun i => ratDivisorOpOfLineBundle ((Scheme.Modules.pullback p).obj (L i))).length),
      RatDivisorOp.capList (l.map fun i => ratDivisorOpOfLineBundle (L i)) n
          (ChowGroupRat.congr Y h (chowPushforwardRat p (n + l.length) α))
        = chowPushforwardRat p n
          (RatDivisorOp.capList (l.map fun i => ratDivisorOpOfLineBundle ((Scheme.Modules.pullback p).obj (L i))) n
            (ChowGroupRat.congr X h' α))
  | [], n, α, h, h' => rfl
  | i :: l, n, α, h, h' => by
    have hl : n + l.length = n + (l.map fun i => ratDivisorOpOfLineBundle (L i)).length := by simp
    have hl' : n + l.length = n + (l.map fun i =>
        ratDivisorOpOfLineBundle ((Scheme.Modules.pullback p).obj (L i))).length := by simp
    show RatDivisorOp.capList (l.map fun i => ratDivisorOpOfLineBundle (L i)) n
        (ratDivisorOpOfLineBundle (L i) (n + (l.map fun i => ratDivisorOpOfLineBundle (L i)).length)
          (ChowGroupRat.congr Y h (chowPushforwardRat p (n + l.length + 1) α)))
      = chowPushforwardRat p n
        (RatDivisorOp.capList (l.map fun i => ratDivisorOpOfLineBundle ((Scheme.Modules.pullback p).obj (L i))) n
          (ratDivisorOpOfLineBundle ((Scheme.Modules.pullback p).obj (L i))
            (n + (l.map fun i => ratDivisorOpOfLineBundle ((Scheme.Modules.pullback p).obj (L i))).length)
            (ChowGroupRat.congr X h' α)))
    rw [RatDivisorOp.apply_congr (ratDivisorOpOfLineBundle (L i)) hl h
        (chowPushforwardRat p (n + l.length + 1) α),
      RatDivisorOp.apply_congr (ratDivisorOpOfLineBundle ((Scheme.Modules.pullback p).obj (L i))) hl' h' α,
      ratDivisorOpOfLineBundle_apply_chowPushforwardRat (k := k) p (L i) (n + l.length) α,
      RatDivisorOp.capList_map_chowPushforwardRat L l n _ hl hl']

/-- **Projection formula for cap products**:
`(∏ c_1(L_i)) ∩ p_* α = p_* ((∏ c_1(p^* L_i)) ∩ α)`. -/
theorem RatDivisorOp.capProd_chowPushforwardRat {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ι → Y.Modules) [∀ i, (L i).IsLineBundle] (n : ℕ) (α : ChowGroupRat X (n + Fintype.card ι)) :
    RatDivisorOp.capProd (fun i => ratDivisorOpOfLineBundle (L i)) n
        (chowPushforwardRat p (n + Fintype.card ι) α)
      = chowPushforwardRat p n
        (RatDivisorOp.capProd (fun i => ratDivisorOpOfLineBundle ((Scheme.Modules.pullback p).obj (L i))) n α) := by
  unfold RatDivisorOp.capProd
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  have hlen : n + Fintype.card ι = n + (Finset.univ : Finset ι).toList.length := by simp
  have key := RatDivisorOp.capList_map_chowPushforwardRat (k := k) p L (Finset.univ : Finset ι).toList n
    (ChowGroupRat.congr X hlen α) (by simp) (by simp)
  rw [chowPushforwardRat_congr_index p hlen α, ChowGroupRat.congr_trans, ChowGroupRat.congr_trans] at key
  exact key

end Projection

end AlgebraicGeometry

end
