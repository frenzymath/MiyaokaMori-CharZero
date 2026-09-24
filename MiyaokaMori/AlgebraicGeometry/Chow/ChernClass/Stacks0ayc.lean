import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapCycle
import MiyaokaMori.RingTheory.KeyLemma.TameSymbol
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrimeDivisor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Morphisms.FiniteCodimOnePointsOutsideOpen
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleFrame
import MiyaokaMori.RingTheory.KeyLemma.Stacks0eax
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0a21
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.LocallyFiniteCycleSum
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.RationalEquivalenceX
import MiyaokaMori.RingTheory.KeyLemma.TameSymbolUnitTwist
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.KeyFormulaCapPointLemmas
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.KeyFormulaNonGeneratingLocusLocallyFinite
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupXLemmas

/-! # The key formula of Chow theory (Stacks 0AYC)

The key formula (Stacks 0AYC): `X` integral, locally of finite type over a field `K` (Stacks has `X`
locally of finite type over `S`; here `S = Spec K`), of dimension `n`; `L`, `N` invertible; `s`, `t` nonzero
meromorphic sections. For the codimension-one integral closed subschemes `Z_i` containing the zeros and
poles of `s`, `t` (generic points `ξ_i`, `B_i = O_{X,ξ_i}`, `s = f_i s_i`, `t = g_i t_i` with `s_i`, `t_i`
local generators), the cycle
`Σ (Z_i→X)_*(ord_{B_i}(f_i)·div_{N|Z_i}(t_i|Z_i) − ord_{B_i}(g_i)·div_{L|Z_i}(s_i|Z_i))` equals
`Σ (Z_i→X)_* div(∂_{B_i}(f_i, g_i))`, where `∂` is the tame symbol; in particular the former is rationally
equivalent to `0`.

Source: Stacks 0AYC (with 02Q1 tame symbol, 0EAX).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- A meromorphic section is an element of the stalk of the line bundle at the generic point; its divisor is
   `rationalSectionDivisor`. Since `π : X → Spec K` is locally of finite type, the local rings of `X` are
   Nagata rings (Stacks 0335, 032U) with finite normalization, so the normalization-based definition of the
   tame symbol agrees with Stacks' (`hfin`). -/

/-- The union of the supports of two cycles is a locally finite family of points. -/
theorem AlgebraicGeometry.locallyFinitePoints_support_union {X : AlgebraicGeometry.Scheme.{u}}
    (α β : AlgebraicGeometry.AlgebraicCycle X ℤ) :
    AlgebraicGeometry.LocallyFinitePoints
      (fun j : ↥(Function.support (α : X → ℤ) ∪ Function.support (β : X → ℤ)) => (j : X)) := by
  intro x
  obtain ⟨t₁, ht₁, hfin₁⟩ := α.locallyFiniteSupport x
  obtain ⟨t₂, ht₂, hfin₂⟩ := β.locallyFiniteSupport x
  refine ⟨interior (t₁ ∩ t₂), isOpen_interior,
    mem_interior_iff_mem_nhds.mpr (Filter.inter_mem ht₁ ht₂), ?_⟩
  have hsub : {j : ↥(Function.support (α : X → ℤ) ∪ Function.support (β : X → ℤ)) |
        (j : X) ∈ interior (t₁ ∩ t₂)} ⊆
      Subtype.val ⁻¹' ((t₁ ∩ Function.support (α : X → ℤ)) ∪ (t₂ ∩ Function.support (β : X → ℤ))) := by
    rintro ⟨j, hj⟩ hjt
    have hjt' := interior_subset hjt
    rcases hj with hj | hj
    · exact Or.inl ⟨hjt'.1, hj⟩
    · exact Or.inr ⟨hjt'.2, hj⟩
  exact ((hfin₁.union hfin₂).preimage Subtype.val_injective.injOn).subset hsub

/-- **The key formula (Stacks 0AYC)**: `c_1(L) ∩ div_N(t) − c_1(N) ∩ div_L(s)` is rationally equivalent to
zero. No quasi-compactness is assumed: in Stacks the `Z_i` form a **locally finite** family ("Let
`Z_i ⊂ X`, `i ∈ I` be a locally finite set of irreducible closed subsets of codimension 1 ..."), and
`ratEquivZero` is the locally finite sum of Stacks 02RW, so the statement has the full strength of Stacks:
`X` integral, locally Noetherian, locally of finite type over a field `K`.

Proof route: (1) 02SH: changing the section of `capPoint` only changes it by a principal cycle on `W_w`
(`rationalSectionDivisor_smul`); (2) the difference of the two sides is
`Σ_{ht w = n+1} ι_{w*} div(∂_{B_w}(f_w, g_w))`; coefficientwise this reduces to the two-dimensional
Noetherian local domain `A = O_{X,ξ}` at a codimension-two point `ξ`, where the coefficient is
`Σ_{ht q = 1} ord_{A/q} ∂_{A_q}(f, g)`; (3) 0EAX (`Ring.tameSymbol_milnorGersten_lowDegree`). The sum in
step (2) is a locally finite sum, handled by `AlgebraicGeometry.ratEquivZero_of_locallyFinite_sum`.

The proof body is `keyFormula_ratEquivZero_generating` (`KeyFormulaNonGeneratingLocusLocallyFinite.lean`),
whose index set is the non-generating locus of `s`, `t` (the support-indexed version is false at non-normal
codimension-one points). -/
theorem AlgebraicGeometry.keyFormula_ratEquivZero {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    (K : Type u) [Field K] (π : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of K))
    [AlgebraicGeometry.LocallyOfFiniteType π]
    (L N : X.Modules) [L.IsLineBundle] [N.IsLineBundle] (n : ℕ) (hX : X.dimension = n + 2)
    (s : L.stalk (genericPoint X)) (t : N.stalk (genericPoint X)) (hs : s ≠ 0) (ht : t ≠ 0) :
    AlgebraicGeometry.firstChernCapCycle ⟨K, inferInstance, π, inferInstance⟩ N (n + 1)
        (L.rationalSectionDivisor s)
      = AlgebraicGeometry.firstChernCapCycle ⟨K, inferInstance, π, inferInstance⟩ L (n + 1)
          (N.rationalSectionDivisor t) := by
  exact AlgebraicGeometry.keyFormula_ratEquivZero_generating K π L N n hX s t hs ht

end
