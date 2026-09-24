import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesIsoTransport
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.DeterminantLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.DetWedgeMapAux
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkCriteria
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAdditiveShortExact

/-! # The determinant of a short exact sequence of vector bundles

For a short exact sequence of vector bundles on a variety, `det G ≃ det F ⊗ det H`.

Source: Stacks 0FJB (the general form of the algebraic core); used in the paper for the degree of
an extension.

## Structure

The main theorem `VectorBundle.det_of_shortExact` is **assembled** from four named declarations:

| declaration | content |
|---|---|
| `VectorBundle.rank_add_of_shortExact` | `G.rank = F.rank + H.rank` |
| `VectorBundle.exists_detWedgeMap` | step 2: the wedge map is well defined (descent along `Λ^b G ↠ Λ^b H`) |
| `VectorBundle.isIso_detWedgeMap` | step 3: the map is an isomorphism (checked on stalks) |
| `Scheme.Modules.exteriorPowerMul` | the wedge multiplication `Λ^a E ⊗ Λ^b E ⟶ Λ^{a+b} E` on sheaves |

The scheme-level general form of steps 2 and 3 is in `DetWedgeMapAux`: transport `S` along `eF`, `eG`,
`eH` to `0 → F → G → H → 0` (`ShortComplex.shortExact_of_iso`) and use `exists_stalk_basis_fin`
(`ModulesStalkCriteria`) for `Fin rank` bases of `F_x` and `H_x`. The proof uses neither a local
splitting of the sequence nor the exactness of the stalk functor: exactness on stalks is obtained
directly by taking germs in the section-level statement `sections_of_exact_mono`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Additivity of the rank: `G.rank = F.rank + H.rank`.

Proof: `AlgebraicGeometry.Scheme.Modules.rankAtStalk_add_of_shortExact` (pointwise additivity of the
rank) gives `∀ x, rankAtStalk S.X₂ x = rankAtStalk S.X₁ x + rankAtStalk S.X₃ x`; its hypotheses
`[S.X₁.IsLocallyFree] [S.X₁.IsFiniteType] [S.X₃.IsLocallyFree] [S.X₃.IsFiniteType]` are transported
along `eF`, `eH` (`Scheme.Modules.isLocallyFree_of_iso`, `isFiniteType_of_iso`). Transport the three
`rankAtStalk` back to the three vector bundles along `eF`, `eG`, `eH` (`rankAtStalk_of_iso`) and
replace them by the constant ranks via `rankAtStalk_eq`. **This step needs the base to be nonempty**:
to pass from a pointwise equality to an equality of constants one needs a point; a `Variety` is
`IsIntegral`, hence irreducible and in particular nonempty
(`AlgebraicGeometry.irreducibleSpace_of_isIntegral`). -/
theorem AlgebraicGeometry.VectorBundle.rank_add_of_shortExact {k : Type u} [Field k] {V : Variety k}
    {S : CategoryTheory.ShortComplex V.toScheme.Modules} (hS : S.ShortExact)
    (F G H : AlgebraicGeometry.VectorBundle V) (eF : F.toModules ≅ S.X₁)
    (eG : G.toModules ≅ S.X₂) (eH : H.toModules ≅ S.X₃) :
    G.rank = F.rank + H.rank := by
  have : S.X₁.IsLocallyFree :=
    AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_iso eF F.locallyFree
  have : S.X₁.IsFiniteType :=
    AlgebraicGeometry.Scheme.Modules.isFiniteType_of_iso eF F.isFiniteType
  have : S.X₃.IsLocallyFree :=
    AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_iso eH H.locallyFree
  have : S.X₃.IsFiniteType :=
    AlgebraicGeometry.Scheme.Modules.isFiniteType_of_iso eH H.isFiniteType
  have : IrreducibleSpace V.carrier.carrier :=
    AlgebraicGeometry.irreducibleSpace_of_isIntegral V.carrier
  obtain ⟨x⟩ : Nonempty V.carrier.carrier := inferInstance
  have h := AlgebraicGeometry.Scheme.Modules.rankAtStalk_add_of_shortExact hS x
  rw [← AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_iso eG x,
    ← AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_iso eF x,
    ← AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_iso eH x,
    G.rankAtStalk_eq x, F.rankAtStalk_eq x, H.rankAtStalk_eq x] at h
  exact h

namespace AlgebraicGeometry.VectorBundle

variable {k : Type u} [Field k] {V : Variety k}
  {S : CategoryTheory.ShortComplex V.toScheme.Modules} (hS : S.ShortExact)
  (F G H : AlgebraicGeometry.VectorBundle V) (eF : F.toModules ≅ S.X₁)
  (eG : G.toModules ≅ S.X₂) (eH : H.toModules ≅ S.X₃)

/-- The transported composite vanishes: `(eF.hom ≫ S.f ≫ eG.inv) ≫ (eG.hom ≫ S.g ≫ eH.inv) = 0`. -/
theorem transported_comp_eq_zero :
    (eF.hom ≫ S.f ≫ eG.inv) ≫ (eG.hom ≫ S.g ≫ eH.inv) = 0 := by
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc S.f, S.zero,
    zero_comp, comp_zero]

include hS in
/-- Transporting `S` along `eF`, `eG`, `eH` to `0 → F → G → H → 0` keeps it short exact
(`ShortComplex.shortExact_of_iso`). -/
theorem transported_shortExact :
    (CategoryTheory.ShortComplex.mk (eF.hom ≫ S.f ≫ eG.inv) (eG.hom ≫ S.g ≫ eH.inv)
      (transported_comp_eq_zero F G H eF eG eH)).ShortExact :=
  CategoryTheory.ShortComplex.shortExact_of_iso
    (CategoryTheory.ShortComplex.isoMk eF.symm eG.symm eH.symm (by simp) (by simp)) hS

/-- The stalk of a vector bundle at every point has a basis indexed by `Fin rank`
(`ModulesStalkCriteria`). -/
theorem exists_stalk_basis (E : AlgebraicGeometry.VectorBundle V) (x : V.toScheme) :
    Nonempty (Module.Basis (Fin E.rank) (V.toScheme.presheaf.stalk x) (E.toModules.presheaf.stalk x)) :=
  MiyaokaMori.ModulesStalkCriteria.exists_stalk_basis_fin E.toModules E.rank E.rankAtStalk_eq x

end AlgebraicGeometry.VectorBundle

/-- Step 2 (**well-definedness** of the wedge map): there is a morphism of sheaves

`μ : Λ^a F ⊗ Λ^b H ⟶ Λ^{a+b} G` (`a = F.rank`, `b = H.rank`)

whose composite with "first map the second factor down along `G ↠ H`" equals "first push the first
factor up along `F ↪ G`, then use the wedge multiplication on `G`", i.e.

`(e_1∧…∧e_a) ⊗ (h_1∧…∧h_b) ↦ i(e_1)∧…∧i(e_a)∧h̃_1∧…∧h̃_b`.

Source: the proof of Stacks 0FJB.

**Proof** (`exists_detWedgeMap_aux` in `DetWedgeMapAux`). Write `i = eF.hom ≫ S.f ≫ eG.inv : F → G`,
`p = eG.hom ≫ S.g ≫ eH.inv : G → H`, `a = F.rank`, `b = H.rank`; `0 → F →i G →p H → 0` is short exact
(transported along isomorphisms).

1. `X.Modules` is abelian. `q := 1 ⊗ Λ^b p` is an epimorphism: it suffices to be surjective on stalks
   (`ModulesStalkCriteria`), and on stalks `q_x` is conjugate to `1 ⊗ ⋀^b p_x` (`ExteriorTensorStalk`),
   `p_x` is surjective, exterior powers preserve surjections and the tensor product is right exact.
2. `ker q ≫ c = 0` (`c := (Λ^a i ⊗ 1) ≫ mul`), checked on stalks: the sequence of stalks is exact, `i_x`
   injective, `p_x` surjective with a section (`H_x` is free), so this reduces to the algebraic fact
   `mul_map_eq_zero_of_map_eq_zero` of `DetWedgeAlgebra` for free modules (the explicit form of
   `Λ^{a+1} F_x = 0`: split the basis vectors `e_S` of `⋀^b G_x` into those containing a factor from
   `i(F_x)` and the one consisting of exactly the last `b` vectors).
3. `μ := Abelian.epiDesc q c`, so `q ≫ μ = c`. -/
theorem AlgebraicGeometry.VectorBundle.exists_detWedgeMap {k : Type u} [Field k] {V : Variety k}
    {S : CategoryTheory.ShortComplex V.toScheme.Modules} (hS : S.ShortExact)
    (F G H : AlgebraicGeometry.VectorBundle V) (eF : F.toModules ≅ S.X₁)
    (eG : G.toModules ≅ S.X₂) (eH : H.toModules ≅ S.X₃) :
    ∃ μ : AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.exteriorPower F.toModules F.rank)
        (AlgebraicGeometry.Scheme.Modules.exteriorPower H.toModules H.rank) ⟶
      AlgebraicGeometry.Scheme.Modules.exteriorPower G.toModules (F.rank + H.rank),
      AlgebraicGeometry.Scheme.Modules.tensorMap (CategoryTheory.CategoryStruct.id _)
            (AlgebraicGeometry.Scheme.Modules.exteriorMap
              (eG.hom ≫ S.g ≫ eH.inv) H.rank) ≫ μ =
        AlgebraicGeometry.Scheme.Modules.tensorMap
              (AlgebraicGeometry.Scheme.Modules.exteriorMap
                (eF.hom ≫ S.f ≫ eG.inv) F.rank) (CategoryTheory.CategoryStruct.id _) ≫
          AlgebraicGeometry.Scheme.Modules.exteriorPowerMul G.toModules F.rank H.rank :=
  MiyaokaMori.DetWedgeMapAux.exists_detWedgeMap_aux _ _ _
    (AlgebraicGeometry.VectorBundle.transported_shortExact hS F G H eF eG eH)
    (AlgebraicGeometry.VectorBundle.exists_stalk_basis F)
    (AlgebraicGeometry.VectorBundle.exists_stalk_basis H)

/-- Step 3 (**isomorphism, checked on stalks**): a `μ` satisfying the equation of step 2 is an
isomorphism.

Source: Stacks 0FJB.

**Proof** (`isIso_detWedgeMap_aux` in `DetWedgeMapAux`). A morphism of sheaves is an isomorphism iff it
is bijective on stalks (`AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective`). At a point `x`, the
conjugation formulas of `ExteriorTensorStalk` turn `μ_x` into a module-level
`μ' : ⋀^a F_x ⊗ ⋀^b H_x → ⋀^{a+b} G_x`, and the equation of step 2 gives
`μ' ∘ (1 ⊗ ⋀^b p_x) = mul ∘ (⋀^a i_x ⊗ 1)`. `F_x`, `H_x` are free (`exists_stalk_basis`), the sequence of
stalks is exact and split, so `bijective_of_comp_eq` of `DetWedgeAlgebra` identifies `μ'` with
`Module.exteriorPowerDetEquivOfBasis`, hence `μ'` is bijective. -/
theorem AlgebraicGeometry.VectorBundle.isIso_detWedgeMap {k : Type u} [Field k] {V : Variety k}
    {S : CategoryTheory.ShortComplex V.toScheme.Modules} (hS : S.ShortExact)
    (F G H : AlgebraicGeometry.VectorBundle V) (eF : F.toModules ≅ S.X₁)
    (eG : G.toModules ≅ S.X₂) (eH : H.toModules ≅ S.X₃)
    (μ : AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.exteriorPower F.toModules F.rank)
        (AlgebraicGeometry.Scheme.Modules.exteriorPower H.toModules H.rank) ⟶
      AlgebraicGeometry.Scheme.Modules.exteriorPower G.toModules (F.rank + H.rank))
    (hμ : AlgebraicGeometry.Scheme.Modules.tensorMap (CategoryTheory.CategoryStruct.id _)
            (AlgebraicGeometry.Scheme.Modules.exteriorMap
              (eG.hom ≫ S.g ≫ eH.inv) H.rank) ≫ μ =
        AlgebraicGeometry.Scheme.Modules.tensorMap
              (AlgebraicGeometry.Scheme.Modules.exteriorMap
                (eF.hom ≫ S.f ≫ eG.inv) F.rank) (CategoryTheory.CategoryStruct.id _) ≫
          AlgebraicGeometry.Scheme.Modules.exteriorPowerMul G.toModules F.rank H.rank) :
    CategoryTheory.IsIso μ :=
  MiyaokaMori.DetWedgeMapAux.isIso_detWedgeMap_aux _ _ _
    (AlgebraicGeometry.VectorBundle.transported_shortExact hS F G H eF eG eH)
    (AlgebraicGeometry.VectorBundle.exists_stalk_basis F)
    (AlgebraicGeometry.VectorBundle.exists_stalk_basis H) μ hμ

/-- The determinant of a short exact sequence of vector bundles `0 → F → G → H → 0`:
`det G ≅ det F ⊗ det H`.

Source: Stacks 0FJB (sheaf version of the standard argument).

**Proof.** Write `a = F.rank`, `b = H.rank`. Note that `AlgebraicGeometry.VectorBundle` carries a
**global constant** rank `rank : ℕ` with `rankAtStalk_eq : ∀ x, rankAtStalk toModules x = rank`, so
"rank" below always means this constant, not a locally constant rank; a `Variety` is `IsIntegral`, in
particular nonempty, so pointwise rank equalities imply equalities of the constants.

1. **Additivity of the rank**: `VectorBundle.rank_add_of_shortExact` gives `G.rank = a + b`. By
   definition `det` is the top exterior power `Λ^{rank}` (`DeterminantLineBundle`).
2. **The global map `det F ⊗ det H → det G`**: `VectorBundle.exists_detWedgeMap`. Locally it is
   `(e_1∧…∧e_a) ⊗ (h_1∧…∧h_b) ↦ i(e_1)∧…∧i(e_a)∧h̃_1∧…∧h̃_b`, where `h̃_j` lifts `h_j` to `G`;
   well-definedness comes from `Λ^{a+1}F = 0`. It uses the wedge multiplication
   `Scheme.Modules.exteriorPowerMul` on sheaves.
3. **Isomorphism, checked on stalks**: `VectorBundle.isIso_detWedgeMap`; on stalks this reduces to the
   free-module version `Module.exteriorPowerDetEquivOfBasis`.

The proof body only assembles: compose the `μ` of (2) with the `IsIso` of (3), and use (1) to replace
the exponent `G.rank` by `a + b`. -/
theorem VectorBundle.det_of_shortExact {k : Type u} [Field k] {V : Variety k}
    {S : CategoryTheory.ShortComplex V.toScheme.Modules} (hS : S.ShortExact)
    (F G H : AlgebraicGeometry.VectorBundle V) (eF : F.toModules ≅ S.X₁) (eG : G.toModules ≅ S.X₂)
    (eH : H.toModules ≅ S.X₃) :
    Nonempty ((AlgebraicGeometry.VectorBundle.det G).toModules ≅
      AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.VectorBundle.det F).toModules
        (AlgebraicGeometry.VectorBundle.det H).toModules) := by
  obtain ⟨μ, hμ⟩ := AlgebraicGeometry.VectorBundle.exists_detWedgeMap hS F G H eF eG eH
  have := AlgebraicGeometry.VectorBundle.isIso_detWedgeMap hS F G H eF eG eH μ hμ
  have hdet : (AlgebraicGeometry.VectorBundle.det G).toModules =
      AlgebraicGeometry.Scheme.Modules.exteriorPower G.toModules (F.rank + H.rank) := by
    show AlgebraicGeometry.Scheme.Modules.exteriorPower G.toModules G.rank = _
    rw [AlgebraicGeometry.VectorBundle.rank_add_of_shortExact hS F G H eF eG eH]
  exact ⟨CategoryTheory.eqToIso hdet ≪≫ (CategoryTheory.asIso μ).symm⟩

end
