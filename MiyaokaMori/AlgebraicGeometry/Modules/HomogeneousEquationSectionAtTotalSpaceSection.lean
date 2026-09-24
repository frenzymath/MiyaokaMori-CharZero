import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.HomogeneousEquationAsSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.Stacks02or
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousLocalFormula
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.HomogeneousEquationSectionAtTotalSpaceSectionLemmas
import MiyaokaMori.Paper.S2WeightedJets.Cone.HomogeneousEquationSectionAtTotalSpaceSectionTupleSection

/-! # Vanishing of a homogeneous equation along the section given by a tuple

Statement: `N+1` global sections `f` of a line bundle `A` give a section `σ_f` of the total space of
`A^{⊕(N+1)}`. The zero scheme of the equation section defined by a homogeneous polynomial `F` of
degree `e` in the tautological coordinates of the total space contains `σ_f` if and only if the
homogeneous evaluation of `F` at `f` vanishes.

Proof:
1. `IdealSheafData.map_bot`, `le_map_iff_comap_le`, `le_bot_iff` rewrite "the ideal sheaf of the
   equation is `≤ ker σ_f`" to "the comap of the ideal sheaf along `σ_f` is `⊥`"; `zeroScheme_pullback`
   (Stacks 02OR) rewrites this to "the ideal sheaf of zeros of the pulled-back section `σ_f^*(F(τ))`
   is `⊥`", and `idealSheafOfSection_eq_bot_iff` to `σ_f^*(F(τ)) = 0`.
2. `evalHomogeneousAtSections_pullback` (with `g = σ_f`; `Tot` is a `k`-scheme via `π`, and `σ_f`
   is a `k`-morphism because `σ_f ≫ π = 𝟙`): via `pullbackTensorPowIso`,
   `σ_f^*(F(τ)) = F(σ_f^*τ_0, …, σ_f^*τ_N)`.
3. `evalHomogeneousAtSections_mapIso` along the canonical isomorphism `Φ : σ_f^*π^*A ≅ A`
   (`tupleTotSection.pullbackIso`): `F(σ_f^*τ)` corresponds to `F(Φ(σ_f^*τ_0), …)`, and
   `Φ(σ_f^*τ_i) = f_i` (coordinate pullback of the tuple section). Isomorphisms preserve and reflect
   zero (`Modules.iso_hom_app_top_eq_zero_iff_hes`), giving the equivalence.

Reference: Stacks 02OR.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A homogeneous equation vanishes along the total space section given by a tuple if and only if
its homogeneous evaluation at the tuple is zero. -/
theorem homogeneousEquationSection_le_ker_totalSpaceSection_iff
    {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (A : C.Modules) [A.IsLineBundle] (N : ℕ)
    {e : ℕ} (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous e)
    (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.idealSheafOfSection _
        (homogeneousEquationSection (k := k) A N F hF) ≤
        AlgebraicGeometry.Scheme.Hom.ker
          (AlgebraicGeometry.Scheme.totalSpaceSectionEquiv
            (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
            (∑ i : Fin (N + 1),
              ((CategoryTheory.Limits.biproduct.ι
                (fun _ : Fin (N + 1) ↦ A) i).val.app (Opposite.op ⊤)).hom (f i))).1 ↔
      evalHomogeneousAtSections A F hF f = 0 := by
  change AlgebraicGeometry.Scheme.idealSheafOfSection _ (homogeneousEquationSection (k := k) A N F hF) ≤
    AlgebraicGeometry.Scheme.Hom.ker (AlgebraicGeometry.Scheme.tupleTotSection A N f).1 ↔ _
  letI : (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).left.Over
      (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom ≫
      (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : (AlgebraicGeometry.Scheme.tupleTotSection A N f).1.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨by
      change (AlgebraicGeometry.Scheme.tupleTotSection A N f).1 ≫
        ((AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom ≫
        (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) = _
      rw [← CategoryTheory.Category.assoc, (AlgebraicGeometry.Scheme.tupleTotSection A N f).2,
        CategoryTheory.Category.id_comp]⟩
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.map_bot,
    AlgebraicGeometry.Scheme.IdealSheafData.le_map_iff_comap_le, le_bot_iff,
    ← AlgebraicGeometry.Scheme.zeroScheme_pullback,
    AlgebraicGeometry.Scheme.idealSheafOfSection_eq_bot_iff]
  rw [← AlgebraicGeometry.Scheme.Modules.iso_hom_app_top_eq_zero_iff_hes
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso (AlgebraicGeometry.Scheme.tupleTotSection A N f).1
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom).obj A) e)]
  unfold homogeneousEquationSection
  rw [evalHomogeneousAtSections_pullback (k := k) (AlgebraicGeometry.Scheme.tupleTotSection A N f).1 _ F hF]
  have key := AlgebraicGeometry.Scheme.Modules.iso_hom_app_top_eq_zero_iff_hes
    (AlgebraicGeometry.Scheme.Modules.tensorPowMapIso
      (AlgebraicGeometry.Scheme.tupleTotSection.pullbackIso A N f) e)
    (evalHomogeneousAtSections _ F hF (fun i => sectionPullbackAlong
      (AlgebraicGeometry.Scheme.tupleTotSection A N f).1 (AlgebraicGeometry.Scheme.tautologicalCoordinate A N i)))
  rw [evalHomogeneousAtSections_mapIso] at key
  refine Iff.trans key.symm ?_
  have hcoord := AlgebraicGeometry.Scheme.tupleTotSection_coordinate_pullback A N f
  simp only [hcoord]
  exact Iff.rfl

end
