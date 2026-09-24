import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks01ffInduction

/-! # Cohomology commutes with filtered colimits on quasi-separated spaces (Stacks 01FF)

Stacks 01FF: on a topological space with a basis of quasi-compact opens in which the intersection of two
quasi-compact opens is quasi-compact, for a quasi-compact open `U` and a filtered system `F_i`, the map
`colim_i H^q(U, F_i) → H^q(U, colim F_i)` is an isomorphism (stated here for `U = X` with `X`
quasi-compact, for abelian sheaves).

Source: Stacks 01FF (cohomology-lemma-quasi-separated-cohomology-colimit); Hartshorne III.2.9 (the
Noetherian version).

The proof is the induction on `q` of Stacks 01FF, written out in `Stacks01ffInduction.lean`
(`Stacks01ff.stmt_all`). It uses three ingredients:
* `TopCat.Sheaf.sections_colimit_bijective_of_isCompact` (Stacks 009F (4) + 0069 (3); the case `q = 0`);
* `CategoryTheory.Functor.exists_mono_injective_diagram` (functorial injective embedding of a diagram);
* `TopCat.Sheaf.H_colimit_subsingleton_of_injective` (`H^{q+1}(X, colim I_j) = 0` for injective `I_j`).
The long exact sequences, exactness of filtered colimits (AB5) and `H^{q+1}(I) = 0` for injective `I` come
from Mathlib (`Abelian.Ext.covariant_sequence_exact₁/₃`, `IsGrothendieckAbelian`,
`Abelian.Ext.subsingleton_of_injective`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 01FF (the case `U = X`, abelian sheaves): `X` quasi-compact with a basis of quasi-compact
opens and quasi-separated (`QuasiSeparatedSpace`). For a filtered diagram `F : J ⥤ Ab(X)`, the canonical
map `colim_j H^q(X, F_j) → H^q(X, colim F)` (`e ↦ e ∘ ι_j`) is bijective, written by the elementwise
description of filtered colimits as "surjective" and "the kernel dies after some `j → k`". -/

theorem TopCat.Sheaf.H_colimit_bijective {X : TopCat.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (hB : TopologicalSpace.Opens.IsBasis {U : TopologicalSpace.Opens X | IsCompact (U : Set X)})
    {J : Type u} [CategoryTheory.SmallCategory J] [CategoryTheory.IsFiltered J]
    (F : J ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ) :
    (∀ x : CategoryTheory.Sheaf.H (CategoryTheory.Limits.colimit F) q,
      ∃ (j : J) (e : CategoryTheory.Sheaf.H (F.obj j) q),
        e.comp (CategoryTheory.Abelian.Ext.mk₀ (CategoryTheory.Limits.colimit.ι F j)) (add_zero q) = x) ∧
    (∀ (j : J) (e : CategoryTheory.Sheaf.H (F.obj j) q),
      e.comp (CategoryTheory.Abelian.Ext.mk₀ (CategoryTheory.Limits.colimit.ι F j)) (add_zero q) = 0 →
        ∃ (k : J) (a : j ⟶ k),
          e.comp (CategoryTheory.Abelian.Ext.mk₀ (F.map a)) (add_zero q) = 0) :=
  Stacks01ff.stmt_all hB q F

end
