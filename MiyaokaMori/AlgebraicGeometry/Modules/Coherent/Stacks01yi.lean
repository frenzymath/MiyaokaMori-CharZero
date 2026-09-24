import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentDevissageSupportSubset

/-! # Dévissage of coherent sheaves (Stacks 01YI)

Stacks 01YI: let `X` be Noetherian and `P` a property of coherent sheaves such that (1) in a short
exact sequence, if two terms have `P` then so does the third; (2) for every point `ξ` (the generic
point of the integral closed subscheme `Z = closure{ξ}`) there is a coherent sheaf `G` with
`Supp G = Z`, `G_ξ` killed by `m_ξ`, `dim_{κ(ξ)} G_ξ = 1` (written `length = 1`) and `P(G)`. Then `P`
holds for all coherent sheaves (with the extra hypothesis that zero objects have `P`).

Source: Stacks 01YI (`coherent-lemma-property`).

`coherent_devissage` is the special case `T = Set.univ` of
`AlgebraicGeometry.Scheme.Modules.coherent_devissage_of_support_subset`
(`CoherentDevissageSupportSubset`): Stacks 01YI run inside `Supp F ⊆ T`. The Stacks proof of 01YI
never leaves `Supp F`, so the two statements have literally the same proof; the restricted form is the
one Stacks 0BEN needs, so it is the primary statement and this module only specializes it. The
hypotheses match one for one: `hzero` (zero objects have `P`) gives the restricted `hzero` (coherent
zero objects have `P`) by forgetting coherence; `h23` (two out of three for all coherent short exact
sequences) gives the restricted `h23` by discarding the three `Supp ⊆ univ` hypotheses; `hgen` (a
generator at every point) gives the restricted `hgen` (a generator at every point of `T`);
`Supp F ⊆ univ` is trivial.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 01YI (dévissage of coherent sheaves): `X` Noetherian, `P` satisfying (1) two out of three in
short exact sequences and (2) for every point `ξ` (the generic point of `Z = closure{ξ}`) a coherent
`G` with `Supp G = Z`, `G_ξ` killed by `m_ξ`, `length G_ξ = 1` (i.e. `dim_{κ(ξ)} G_ξ = 1`) and `P G`.
The extra hypothesis `hzero` (zero objects have `P`) follows from (1), (2) when `X` is nonempty and is
independent only for `X = ∅`. -/
theorem AlgebraicGeometry.Scheme.Modules.coherent_devissage {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian X] (P : X.Modules → Prop)
    (hzero : ∀ F : X.Modules, CategoryTheory.Limits.IsZero F → P F)
    (h23 : ∀ S : CategoryTheory.ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      (P S.X₁ → P S.X₂ → P S.X₃) ∧ (P S.X₁ → P S.X₃ → P S.X₂) ∧ (P S.X₂ → P S.X₃ → P S.X₁))
    (hgen : ∀ ξ : X, ∃ G : X.Modules, G.IsCoherent ∧ G.support = closure {ξ} ∧
      IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ≤
        Module.annihilator (X.presheaf.stalk ξ) (G.stalk ξ) ∧
      Module.length (X.presheaf.stalk ξ) (G.stalk ξ) = 1 ∧ P G)
    (F : X.Modules) [F.IsCoherent] : P F :=
  AlgebraicGeometry.Scheme.Modules.coherent_devissage_of_support_subset Set.univ P
    (fun F _ hF => hzero F hF)
    (fun S hS h₁ h₂ h₃ _ _ _ => h23 S hS h₁ h₂ h₃)
    (fun ξ _ => hgen ξ)
    F (Set.subset_univ _)

end
