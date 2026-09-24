import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeOfFreeAffineSections
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.OmegaQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentials
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank

/-! # Relative differentials of a smooth morphism are locally free

The sheaf of relative differentials `Ω_{X/S}` of a smooth morphism `f : X → S` is locally free;
when `f` is smooth of relative dimension `n` its rank at every point is `n` (only the direction
"smooth ⇒ locally free" is taken). Used in §1 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.isLocallyFree_omega_of_smooth {X S : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ S) [AlgebraicGeometry.Smooth f] :
    (AlgebraicGeometry.Omega f).IsLocallyFree := by
  have := AlgebraicGeometry.Omega_isQuasicoherent f
  refine AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_free_affine_sections _ fun x => ?_
  obtain ⟨V, hV, U, hU, hx, e, hf⟩ := AlgebraicGeometry.Smooth.exists_isStandardSmooth f x
  refine ⟨U, hU, hx, ?_⟩
  let := (f.appLE V U e).hom.toAlgebra
  have : Algebra.IsStandardSmooth Γ(S, V) Γ(X, U) := hf
  exact ⟨Module.Free.of_equiv (AlgebraicGeometry.Omega_appIso f hV hU e).symm,
    Module.Finite.equiv (AlgebraicGeometry.Omega_appIso f hV hU e).symm⟩

theorem AlgebraicGeometry.rankAtStalk_omega_of_smoothOfRelativeDimension
    {X S : AlgebraicGeometry.Scheme.{u}} (n : ℕ) (f : X ⟶ S)
    [AlgebraicGeometry.SmoothOfRelativeDimension n f] (x : X) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk (AlgebraicGeometry.Omega f) x = n := by
  have := AlgebraicGeometry.Omega_isQuasicoherent f
  refine AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_free_affine_sections _ n (fun y => ?_) x
  obtain ⟨V, hV, U, hU, hy, e, hf⟩ :=
    AlgebraicGeometry.SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := n) (f := f) y
  refine ⟨U, hU, hy, ?_⟩
  let := (f.appLE V U e).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension n Γ(S, V) Γ(X, U) := hf
  have : Algebra.IsStandardSmooth Γ(S, V) Γ(X, U) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : Nontrivial Γ(X, U) := by
    have : Nonempty U := ⟨⟨y, hy⟩⟩
    have : Nonempty (U : AlgebraicGeometry.Scheme) := ‹_›
    exact (AlgebraicGeometry.Scheme.component_nontrivial X U)
  refine ⟨Module.Free.of_equiv (AlgebraicGeometry.Omega_appIso f hV hU e).symm,
    Module.Finite.equiv (AlgebraicGeometry.Omega_appIso f hV hU e).symm, ?_⟩
  rw [(AlgebraicGeometry.Omega_appIso f hV hU e).finrank_eq]
  exact Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n)

end
