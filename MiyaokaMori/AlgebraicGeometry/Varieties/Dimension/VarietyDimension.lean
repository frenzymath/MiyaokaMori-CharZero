import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.DimensionFiniteness
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension

/-! # Dimension of a variety

The dimension `dim X = n` of a variety, a natural number (the main theorem requires `n ≥ 1`).

**One definition of dimension.** `Variety.dim X` is an `abbrev` of `X.carrier.dimension`
(`AlgebraicGeometry.Scheme.dimension`, `SchemeDimension.lean`). The name `Variety.dim` is the one
used in the statements of the main results. For a variety the truncation
hypotheses of `Scheme.dimension_spec` hold automatically (integral ⇒ nonempty ⇒ `≠ ⊥`; finite type over a
field ⇒ finite dimension ⇒ `≠ ⊤`, `Variety.topologicalKrullDim_eq_trdeg`), so `Variety.dim_spec` and
`Variety.dim_eq_iff` are unconditional: every comparison of `X.dim : ℕ` with `topologicalKrullDim X.carrier`
goes through them.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `dim X`, the dimension of a variety: the (one) scheme dimension of its underlying scheme. -/
noncomputable abbrev Variety.dim {k : Type u} [Field k] (X : Variety k) : ℕ :=
  X.carrier.dimension

/-- An alias of `Variety.dim` (also available for `SmoothProjectiveVariety` through `extends`). -/

noncomputable abbrev Variety.dimension {k : Type u} [Field k] (X : Variety k) : ℕ :=
  X.carrier.dimension

/-- The Krull dimension of a variety is not `⊥`: the underlying scheme is integral, hence irreducible
and nonempty. -/
theorem Variety.topologicalKrullDim_ne_bot {k : Type u} [Field k] (X : Variety k) :
    topologicalKrullDim X.carrier.carrier ≠ ⊥ := by
  have hnonempty : Nonempty (TopologicalSpace.IrreducibleCloseds X.carrier.carrier) := by
    letI : IrreducibleSpace X.carrier.carrier :=
      AlgebraicGeometry.irreducibleSpace_of_isIntegral X.carrier
    exact ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩⟩
  rw [topologicalKrullDim]
  exact Order.krullDim_ne_bot_iff.mpr hnonempty

/-- The Krull dimension of a variety is finite. -/
theorem Variety.topologicalKrullDim_ne_top {k : Type u} [Field k] (X : Variety k) :
    topologicalKrullDim X.carrier.carrier ≠ ⊤ :=
  (Variety.topologicalKrullDim_eq_trdeg X).2

/-- For a variety the truncation `ℕ`-valued dimension is faithful, unconditionally. -/
theorem Variety.dim_spec {k : Type u} [Field k] (X : Variety k) :
    topologicalKrullDim X.carrier.carrier = (X.dim : WithBot ℕ∞) :=
  X.carrier.dimension_spec X.topologicalKrullDim_ne_bot X.topologicalKrullDim_ne_top

/-- The single coercion lemma for `X.dim = n` versus `topologicalKrullDim X.carrier = n`. -/
theorem Variety.dim_eq_iff {k : Type u} [Field k] (X : Variety k) (n : ℕ) :
    X.dim = n ↔ topologicalKrullDim X.carrier.carrier = (n : WithBot ℕ∞) :=
  X.carrier.dimension_eq_iff X.topologicalKrullDim_ne_bot X.topologicalKrullDim_ne_top n

theorem Variety.one_le_dim_of_nontrivial {k : Type u} [Field k] (X : Variety k)
    (h : ¬ Subsingleton X.carrier.carrier) : 1 ≤ X.dim := by
  letI : IrreducibleSpace X.carrier.carrier :=
    AlgebraicGeometry.irreducibleSpace_of_isIntegral X.carrier
  obtain ⟨x, y, hxy⟩ : ∃ x y : X.carrier.carrier, x ≠ y :=
    nontrivial_iff.mp ((not_subsingleton_iff_nontrivial.mp h))
  obtain hxy' | hyx' := (t0Space_iff_or_notMem_closure X.carrier.carrier).mp inferInstance hxy
  · let a : TopologicalSpace.IrreducibleCloseds X.carrier.carrier :=
      ⟨closure ({y} : Set X.carrier.carrier), isIrreducible_singleton.closure, isClosed_closure⟩
    let b : TopologicalSpace.IrreducibleCloseds X.carrier.carrier :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
    have hab : a < b := by
      rw [lt_iff_le_and_ne]
      constructor
      · exact SetLike.coe_subset_coe.mp (Set.subset_univ _)
      · intro hab
        have heq : closure ({y} : Set X.carrier.carrier) = Set.univ :=
          congrArg SetLike.coe hab
        exact hxy' (heq ▸ Set.mem_univ x)
    have hone : (1 : WithBot ℕ∞) ≤ topologicalKrullDim X.carrier.carrier := by
      rw [topologicalKrullDim]
      exact Order.one_le_krullDim_iff.mpr ⟨a, b, hab⟩
    have hone' : (1 : WithBot ℕ∞) ≤ (X.dim : WithBot ℕ∞) := by
      rw [← Variety.dim_spec X]
      exact hone
    exact_mod_cast hone'
  · let a : TopologicalSpace.IrreducibleCloseds X.carrier.carrier :=
      ⟨closure ({x} : Set X.carrier.carrier), isIrreducible_singleton.closure, isClosed_closure⟩
    let b : TopologicalSpace.IrreducibleCloseds X.carrier.carrier :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
    have hab : a < b := by
      rw [lt_iff_le_and_ne]
      constructor
      · exact SetLike.coe_subset_coe.mp (Set.subset_univ _)
      · intro hab
        have heq : closure ({x} : Set X.carrier.carrier) = Set.univ :=
          congrArg SetLike.coe hab
        exact hyx' (heq ▸ Set.mem_univ y)
    have hone : (1 : WithBot ℕ∞) ≤ topologicalKrullDim X.carrier.carrier := by
      rw [topologicalKrullDim]
      exact Order.one_le_krullDim_iff.mpr ⟨a, b, hab⟩
    have hone' : (1 : WithBot ℕ∞) ≤ (X.dim : WithBot ℕ∞) := by
      rw [← Variety.dim_spec X]
      exact hone
    exact_mod_cast hone'

/-- `Variety.dim` is an abbreviation of `Scheme.dimension`; this is `rfl`. -/

theorem Variety.dim_eq_scheme_dimension {k : Type u} [Field k] (X : Variety k) :
    X.dim = X.carrier.dimension :=
  rfl

end
