import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassMk
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suPointClosure

/-! # Commutativity of caps on the fundamental class of an integral scheme (Stacks 02TH)

Stacks 02TH: for `X` integral of dimension `n`, `L`, `N` invertible and `s`, `t` nonzero meromorphic
sections, `c_1(N) ∩ div_L(s) = c_1(L) ∩ div_N(t)` in `CH_{n-2}(X)`. Since `div_L(s)` represents
`c_1(L) ∩ [X]`, this is written as `c_1(L) ∩ c_1(N) ∩ [X] = c_1(N) ∩ c_1(L) ∩ [X]` (the core case of the
commutativity of caps, on the fundamental class of an integral scheme; the proof uses the key
formula, Stacks 0AYC). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `X.dimension = n + 2 > 0` forces the topological Krull dimension to be finite (the fallback value
at `⊤` is `0`). -/
private theorem topologicalKrullDim_ne_top_of_dimension {X : AlgebraicGeometry.Scheme.{u}} {n : ℕ}
    (hX : X.dimension = n + 2) : topologicalKrullDim X ≠ ⊤ := by
  intro h
  unfold AlgebraicGeometry.Scheme.dimension at hX
  rw [h] at hX
  have : (WithBot.unbotD 0 (⊤ : WithBot ℕ∞)).toNat = 0 := by
    show (⊤ : ℕ∞).toNat = 0
    exact ENat.toNat_top
  omega

private theorem topologicalKrullDim_ne_bot {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] : topologicalKrullDim X ≠ ⊥ := by
  unfold topologicalKrullDim
  have : Nonempty (IrreducibleCloseds X) :=
    ⟨⟨Set.univ, (IrreducibleSpace.isIrreducible_univ X), isClosed_univ⟩⟩
  exact Order.krullDim_ne_bot_iff.mpr inferInstance

/-- The height of the generic point equals the dimension. -/
private theorem height_genericPoint_of_dimension {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] {n : ℕ} (hX : X.dimension = n + 2) :
    Order.height (genericPoint X) = ((n + 2 : ℕ) : ℕ∞) := by
  have hk : Order.krullDim X = topologicalKrullDim X :=
    (Order.krullDim_eq_of_orderIso
      (@irreducibleSetEquivPoints X _ _ _ : IrreducibleCloseds X ≃o X)).symm
  have h1 : ((Order.height (⊤ : X) : ℕ∞) : WithBot ℕ∞) = Order.krullDim X :=
    Order.height_top_eq_krullDim
  rw [hk, X.dimension_spec topologicalKrullDim_ne_bot (topologicalKrullDim_ne_top_of_dimension hX),
    hX] at h1
  have h2 : Order.height (⊤ : X) = ((n + 2 : ℕ) : ℕ∞) := WithBot.coe_injective h1
  exact h2

/-- `c_1(N) ∩ [X]` (the cycle-level linear extension) is the single-point contribution of the generic
point. -/
private theorem firstChernCapCycleAux_fundamentalCycle {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    (N : X.Modules) [N.IsLineBundle] {n : ℕ} (hX : X.dimension = n + 2) :
    AlgebraicGeometry.firstChernCapCycleAux N (n + 2) (X.fundamentalCycle (n + 2)) =
      AlgebraicGeometry.firstChernCapPoint N (genericPoint X) := by
  classical
  have hfund : ∀ x : X, X.fundamentalCycle (n + 2) x = if x = genericPoint X then 1 else 0 := by
    intro x
    have h := congrFun (X.fundamentalCycle_of_isIntegral (topologicalKrullDim_ne_top_of_dimension hX)) x
    rw [hX] at h
    rw [h]
  ext z
  show (∑ᶠ w : X, AlgebraicGeometry.firstChernCapTerm N (n + 2) (X.fundamentalCycle (n + 2)) z w) = _
  rw [finsum_eq_single _ (genericPoint X)]
  · unfold AlgebraicGeometry.firstChernCapTerm
    rw [if_pos (height_genericPoint_of_dimension hX), hfund, if_pos rfl, one_mul]
  · intro w hw
    unfold AlgebraicGeometry.firstChernCapTerm
    rw [hfund, if_neg hw, zero_mul, ite_self]

/-- **Stacks 02TH**: `c_1(L) ∩ (c_1(N) ∩ [X]) = c_1(N) ∩ (c_1(L) ∩ [X])` for an integral scheme `X` of
dimension `n + 2`. No quasi-compactness is needed, since `ratEquivZero` allows the locally finite sums
of Stacks 02RW and the key formula `keyFormula_ratEquivZero` holds in that generality. -/
theorem AlgebraicGeometry.firstChernClass_comm_fundamentalClass {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    (L N : X.Modules) [L.IsLineBundle] [N.IsLineBundle]
    (n : ℕ) (hX : X.dimension = n + 2) :
    AlgebraicGeometry.firstChernClass L (n + 1)
        (AlgebraicGeometry.firstChernClass N (n + 2) (X.fundamentalChowClass (n + 2)))
      = AlgebraicGeometry.firstChernClass N (n + 1)
        (AlgebraicGeometry.firstChernClass L (n + 2) (X.fundamentalChowClass (n + 2))) := by
  have hXk := AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) X
  -- c_1(M) ∩ [X] = [capPoint M η] (M = L, N)
  have hmem : ∀ (M : X.Modules) [M.IsLineBundle],
      AlgebraicGeometry.firstChernCapPoint M (genericPoint X) ∈
        AlgebraicGeometry.cycleSubgroup X (n + 1) := by
    intro M _
    rw [← firstChernCapCycleAux_fundamentalCycle M hX]
    exact AlgebraicGeometry.firstChernCapCycleAux_mem hXk M (n + 2) _
  have hstep : ∀ (M : X.Modules) [M.IsLineBundle],
      AlgebraicGeometry.firstChernClass M (n + 2) (X.fundamentalChowClass (n + 2)) =
        AlgebraicGeometry.ChowGroup.mk
          ⟨AlgebraicGeometry.firstChernCapPoint M (genericPoint X), hmem M⟩ := by
    intro M _
    refine (AlgebraicGeometry.firstChernClass_mk (k := k) M (Nat.succ_pos _) _ _).trans ?_
    show AlgebraicGeometry.ChowGroup.mk
      (⟨AlgebraicGeometry.firstChernCapCycleAux M (n + 2) (X.fundamentalCycle (n + 2)), _⟩ :
        ↥(AlgebraicGeometry.cycleSubgroup X (n + 1))) = _
    congr 1
    exact Subtype.ext (firstChernCapCycleAux_fundamentalCycle M hX)
  rw [hstep N, hstep L, AlgebraicGeometry.firstChernClass_mk (k := k) L (Nat.succ_pos _),
    AlgebraicGeometry.firstChernClass_mk (k := k) N (Nat.succ_pos _)]
  -- move both sides to `X' := X.pointClosure η` by 02SU (cycle level) and use the key formula on `X'`
  have hη := height_genericPoint_of_dimension hX
  have hLN : AlgebraicGeometry.IsLocallyNoetherian (X.pointClosure (genericPoint X)) :=
    AlgebraicGeometry.Scheme.isLocallyNoetherian_pointClosure _
  let _ : (X.pointClosure (genericPoint X)).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨X.pointClosureι (genericPoint X) ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have hLFT : AlgebraicGeometry.LocallyOfFiniteType
      ((X.pointClosure (genericPoint X)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    inferInstanceAs (AlgebraicGeometry.LocallyOfFiniteType
      (X.pointClosureι (genericPoint X) ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
  have hover : (X.pointClosureι (genericPoint X)).IsOver
      (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
  have hdim : topologicalKrullDim (X.pointClosure (genericPoint X)) =
      ((n + 1 + 1 : ℕ) : WithBot ℕ∞) :=
    AlgebraicGeometry.Scheme.topologicalKrullDim_pointClosure _ hη
  -- a rational section of `ι^*M` and its divisor
  have hcap : ∀ (M : X.Modules) [M.IsLineBundle],
      ∃ s : ((AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι (genericPoint X))).obj M).stalk
          (genericPoint (X.pointClosure (genericPoint X))), s ≠ 0 ∧
        AlgebraicGeometry.firstChernCapPoint M (genericPoint X) =
          AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι (genericPoint X))
            (((AlgebraicGeometry.Scheme.Modules.pullback
              (X.pointClosureι (genericPoint X))).obj M).rationalSectionDivisor s) := by
    intro M _
    exact ⟨Classical.epsilon fun t => t ≠ 0, Classical.epsilon_spec
      (AlgebraicGeometry.Scheme.Modules.exists_stalk_genericPoint_ne_zero _), rfl⟩
  have hdivmem : ∀ (M' : (X.pointClosure (genericPoint X)).Modules) [M'.IsLineBundle]
      (s : M'.stalk (genericPoint (X.pointClosure (genericPoint X)))),
      M'.rationalSectionDivisor s ∈
        AlgebraicGeometry.cycleSubgroup (X.pointClosure (genericPoint X)) (n + 1) := by
    intro M' _ s z hz
    exact AlgebraicGeometry.Scheme.height_eq_of_coheight_eq_one
      ((X.pointClosure (genericPoint X)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) hdim
      (AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor_support M' s z hz)
  obtain ⟨sL, hsL, hcapL⟩ := hcap L
  obtain ⟨sN, hsN, hcapN⟩ := hcap N
  rw [hcapL, hcapN]
  -- here `p = ι_η` is the closed immersion of a point closure, so the special case of 02SU for point
  -- closures (`Stacks02suPointClosure.lean`) suffices
  have hWk := AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k)
    (X.pointClosure (genericPoint X))
  have h1 := AlgebraicGeometry.chowPushforward_firstChernCapCycle_pullback_pointClosureι hXk
    (genericPoint X) hWk L n
    (((AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι (genericPoint X))).obj
      N).rationalSectionDivisor sN)
  have h2 := AlgebraicGeometry.chowPushforward_firstChernCapCycle_pullback_pointClosureι hXk
    (genericPoint X) hWk N n
    (((AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι (genericPoint X))).obj
      L).rationalSectionDivisor sL)
  have hkey := AlgebraicGeometry.keyFormula_ratEquivZero k
    ((X.pointClosure (genericPoint X)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    ((AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι (genericPoint X))).obj L)
    ((AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι (genericPoint X))).obj N) n
    (AlgebraicGeometry.Scheme.dimension_pointClosure _ hη) sL sN hsL hsN
  exact h1.symm.trans ((congrArg _ hkey.symm).trans h2)

end
