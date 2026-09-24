import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.LocalDimensionMaxComponents
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.OmegaQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentials
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentialsLocallyFree
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyLocalDimensionEqDim
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.LocalDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks00t77
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeOfFreeAffineSections
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.StandardSmoothChartLocalDimension

/-! # The rank of `Ω_{X/k}` of a smooth scheme (Stacks 02G1 over a field)

Stacks 02G1 (the case of a field): if `X` is smooth over `k`, the rank of `Ω_{X/k}` at `x` equals
the local dimension `dim_x X` of `X` at `x` (in general `rank_x Ω_{X/S} = dim_x X_{f(x)}`).
This is the rank of `Ω_X` used in §1 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The proof does not follow the "relative global complete intersection" route of Stacks
   (00SP / 00T7(7)); instead it uses "standard smooth = étale over a polynomial ring" together
   with the going-down height formula (`EtaleOverMvPolynomialKrullDimEq`,
   `StandardSmoothChartLocalDimension`).
   Take a standard smooth chart `V` at `x` (of relative dimension `n`):
   · on the `Ω` side, `Γ(V, Ω) ≅ Ω[Γ(X,V)/k]` is free of rank `n` (Mathlib), and the pointwise rank
     lemma gives `rankAtStalk = n`;
   · on the dimension side, `IsAffineOpen.localDimension_eq_of_isStandardSmoothOfRelativeDimension`
     gives `dim_x X = n`.
   Note that `X` need not be connected and `n` may differ between charts, so both sides must be
   pointwise. -/

/-- General form: if `f : X ⟶ Spec k` is smooth, the rank of `Ω_f` at `x` equals the local
dimension of `X` at `x`. -/
theorem AlgebraicGeometry.Smooth.rankAtStalk_omega_eq_localDimension {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth f] (x : X) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk (AlgebraicGeometry.Omega f) x
      = localDimension X x := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := AlgebraicGeometry.Smooth.exists_isStandardSmooth f x
  have hUtop : U = ⊤ := by
    apply le_antisymm le_top
    intro y _
    have hy : y = f x := Subsingleton.elim _ _
    rw [hy]
    exact e hx
  subst U
  let _ : Field Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤) :=
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  obtain ⟨n, hn⟩ : ∃ n, (f.appLE ⊤ V e).hom.IsStandardSmoothOfRelativeDimension n := by
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := hf
    let _ := (f.appLE ⊤ V e).hom.toAlgebra
    exact ⟨_, ⟨_, _, _, ‹_›, P, rfl⟩⟩
  rw [hV.localDimension_eq_of_isStandardSmoothOfRelativeDimension _ hn x hx]
  have := AlgebraicGeometry.Omega_isQuasicoherent f
  let := (f.appLE ⊤ V e).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension n
      Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤) Γ(X, V) := hn
  have : Algebra.IsStandardSmooth Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤) Γ(X, V) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : Nontrivial Γ(X, V) := by
    have : Nonempty V := ⟨⟨x, hx⟩⟩
    have : Nonempty (V : AlgebraicGeometry.Scheme) := ‹_›
    exact (AlgebraicGeometry.Scheme.component_nontrivial X V)
  refine AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_free_affine_sections_at _ n x hV hx
    (Module.Free.of_equiv (AlgebraicGeometry.Omega_appIso f hU hV e).symm)
    (Module.Finite.equiv (AlgebraicGeometry.Omega_appIso f hU hV e).symm) ?_
  rw [(AlgebraicGeometry.Omega_appIso f hU hV e).finrank_eq]
  exact Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n)

theorem AlgebraicGeometry.rankAtStalk_omega_eq_localDimension_of_smooth {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.Smooth (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))] (x : X) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk
        (AlgebraicGeometry.Omega (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) x
      = localDimension X x :=
  AlgebraicGeometry.Smooth.rankAtStalk_omega_eq_localDimension _ x

end
