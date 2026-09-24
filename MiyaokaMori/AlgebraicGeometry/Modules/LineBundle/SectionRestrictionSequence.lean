import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorRightInvertibleEquivalence
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierOfSection
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesMonoidalPreadditive
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleSectionMultiplication
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SectionRestrictionSequenceBase
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionRestrictionSequenceUnitCompat

/-! # The restriction sequence of a regular section

The short exact restriction sequence given by a regular section: for line bundles `N`, `L` and an
everywhere regular global section `s` of `L ⊗ N^{-1}` with `D = Z(s)`,
`0 → N →(·s) L →(restriction) i_*(L|_D) → 0` is short exact; the two maps are multiplication by `s`
(`LineBundle.mulBySection`) and the unit `L → i_*i^*L` of the pullback–pushforward adjunction.

Proof. Write `M := L ⊗ N^{-1}`, `σ := σ_s : O_X → M`, `ι : Z(s) → X`.
1. Base case `N = O_X` (`SectionRestrictionSequenceBase.shortExact_homOfTopSection_unit`):
   `0 → O_X →σ M →η_M ι_*ι^*M → 0` is short exact.
2. Tensor with the line bundle `N` (an equivalence, `isEquivalence_tensorRight_of_isLineBundle`, transported
   through the braiding): `0 → N ⊗ O_X →(N ◁ σ) N ⊗ M →(N ◁ η_M) N ⊗ ι_*ι^*M → 0` is short exact.
3. By definition `mulBySection N L s = ρ_N⁻¹ ≫ (N ◁ σ) ≫ Φ` with `Φ : N ⊗ M ≅ L` the iso built from the
   monoidal structure and the contraction `N ⊗ N^∨ ≅ O_X`.
4. `ψ : N ⊗ ι_*ι^*M ≅ ι_*ι^*L` is the projection formula (Stacks 01E8) followed by `ι_*` of
   `ι^*N ⊗ ι^*M ≅ ι^*(N ⊗ M) ≅ ι^*L`; the identity `(N ◁ η_M) ≫ ψ = Φ ≫ η_L`
   (`whiskerLeft_unit_comp_projectionFormulaHom` + naturality of `η`) makes `(ρ_N, Φ, ψ)` an isomorphism
   of short complexes from the sequence of step 2 to `(mulBySection N L s, η_L)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory in
/-- The isomorphism `Φ : N ⊗ (L ⊗ N^{-1}) ≅ L` whose `hom` is the tail of `LineBundle.mulBySection`. -/
noncomputable def LineBundle.mulBySectionTailIso {k : Type u} [Field k] {X : Variety k} (N L : LineBundle X) :
    N.toModules ⊗ (L.tensor (N.zpow (-1))).toModules ≅ L.toModules :=
  MonoidalCategory.whiskerLeftIso N.toModules
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L.toModules (N.zpow (-1)).toModules ≪≫
        MonoidalCategory.whiskerLeftIso L.toModules N.zpowNegOneIso) ≪≫
    (α_ N.toModules L.toModules (AlgebraicGeometry.Scheme.Modules.dual N.toModules)).symm ≪≫
    MonoidalCategory.whiskerRightIso (β_ N.toModules L.toModules)
      (AlgebraicGeometry.Scheme.Modules.dual N.toModules) ≪≫
    α_ L.toModules N.toModules (AlgebraicGeometry.Scheme.Modules.dual N.toModules) ≪≫
    MonoidalCategory.whiskerLeftIso L.toModules N.contraction ≪≫
    ρ_ L.toModules

open scoped CategoryTheory.MonoidalCategory in
/-- `mulBySection N L s = ρ_N⁻¹ ≫ (N ◁ σ_s) ≫ Φ`. -/
theorem LineBundle.mulBySection_eq {k : Type u} [Field k] {X : Variety k} (N L : LineBundle X)
    (s : ((L.tensor (N.zpow (-1))).toModules.val.obj (Opposite.op ⊤) : Type u)) :
    LineBundle.mulBySection N L s =
      (ρ_ N.toModules).inv ≫
        (N.toModules ◁ (show 𝟙_ X.toScheme.Modules ⟶ (L.tensor (N.zpow (-1))).toModules from
          AlgebraicGeometry.Scheme.Modules.homOfTopSection _ s)) ≫
        (LineBundle.mulBySectionTailIso N L).hom := by
  unfold LineBundle.mulBySection
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rfl

open AlgebraicGeometry in

theorem shortExact_of_regular_section {k : Type u} [Field k] {X : Variety k}
    (N L : LineBundle X)
    (s : ((L.tensor (N.zpow (-1))).toModules.val.obj (Opposite.op ⊤) : Type u))
    /- `s` is regular (a non-zero-divisor): on every open, `r ↦ r·s|_U` is injective (Mathlib's `IsRegular`
       is defined only for monoid elements and cannot be used for elements of the stalks of a module). -/
    (hs : ∀ U : X.toScheme.Opens, Function.Injective (fun r : Γ(X.toScheme, U) =>
        r • (((L.tensor (N.zpow (-1))).toModules.presheaf.map
          (CategoryTheory.homOfLE (le_top : U ≤ ⊤)).op).hom s : Γ((L.tensor (N.zpow (-1))).toModules, U)))) :
    let ι := (AlgebraicGeometry.Scheme.idealSheafOfSection
      (L.tensor (N.zpow (-1))).toModules s).subschemeι
    /- The maps: on the left multiplication by `s` (`LineBundle.mulBySection`), on the right the restriction
       `L → ι_*ι^*L` (the unit of the pullback–pushforward adjunction); that the composite is zero is part
       of the conclusion. -/
    ∃ w : LineBundle.mulBySection N L s ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app L.toModules = 0,
      (CategoryTheory.ShortComplex.mk (LineBundle.mulBySection N L s)
        ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app L.toModules) w).ShortExact := by
  intro ι
  open scoped CategoryTheory.MonoidalCategory in
  -- notation
  let M : X.toScheme.Modules := (L.tensor (N.zpow (-1))).toModules
  let σ : 𝟙_ X.toScheme.Modules ⟶ M := AlgebraicGeometry.Scheme.Modules.homOfTopSection M s
  let adj := AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι
  let Φ := LineBundle.mulBySectionTailIso N L
  -- Step 1: the base case
  have hI := AlgebraicGeometry.Scheme.idealSheafOfSection_isZeroIdeal M s
  have hbase := AlgebraicGeometry.Scheme.Modules.SectionRestrictionSequenceAux.shortExact_homOfTopSection_unit
    M (AlgebraicGeometry.Scheme.idealSheafOfSection M s) s hI hs
  have hzero₁ : σ ≫ adj.unit.app M = 0 :=
    AlgebraicGeometry.Scheme.Modules.SectionRestrictionSequenceAux.homOfTopSection_comp_unit_app
      M (AlgebraicGeometry.Scheme.idealSheafOfSection M s) s hI
  -- Step 2: tensor with N
  have := AlgebraicGeometry.Scheme.Modules.monoidalPreadditive X.toScheme
  have hzero₂ : (N.toModules ◁ σ) ≫ (N.toModules ◁ adj.unit.app M) = 0 := by
    rw [← MonoidalCategory.whiskerLeft_comp, hzero₁, MonoidalPreadditive.whiskerLeft_zero]
  have hS₂ : (ShortComplex.mk (N.toModules ◁ σ) (N.toModules ◁ adj.unit.app M) hzero₂).ShortExact := by
    have : (CategoryTheory.MonoidalCategory.tensorRight N.toModules).IsEquivalence :=
      AlgebraicGeometry.Scheme.Modules.isEquivalence_tensorRight_of_isLineBundle N.toModules
    have : CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.Discrete PEmpty.{1})
        (CategoryTheory.MonoidalCategory.tensorRight N.toModules) := inferInstance
    have : (CategoryTheory.MonoidalCategory.tensorRight N.toModules).PreservesZeroMorphisms :=
      inferInstance
    have hS₁ := hbase.map_of_exact (CategoryTheory.MonoidalCategory.tensorRight N.toModules)
    refine ShortComplex.shortExact_of_iso ?_ hS₁
    exact ShortComplex.isoMk (β_ _ N.toModules) (β_ _ N.toModules) (β_ _ N.toModules)
      (BraidedCategory.braiding_naturality_left _ _).symm
      (BraidedCategory.braiding_naturality_left _ _).symm
  -- Step 4: ψ
  let ψ : N.toModules ⊗ (AlgebraicGeometry.Scheme.Modules.pushforward ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj M) ≅
      (AlgebraicGeometry.Scheme.Modules.pushforward ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj L.toModules) :=
    AlgebraicGeometry.Scheme.Modules.projectionFormulaIso ι N.toModules _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.pushforward ι).mapIso
        ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso ι N.toModules M).symm ≪≫
          (AlgebraicGeometry.Scheme.Modules.pullback ι).mapIso Φ)
  have hψ : (N.toModules ◁ adj.unit.app M) ≫ ψ.hom = Φ.hom ≫ adj.unit.app L.toModules := by
    have h1 := AlgebraicGeometry.Scheme.Modules.SectionRestrictionSequenceAux.whiskerLeft_unit_comp_projectionFormulaHom
      ι N.toModules M
    have h2 : AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom ι N.toModules M =
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso ι N.toModules M).hom := rfl
    have h3 := adj.unit_naturality Φ.hom
    simp only [ψ, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      AlgebraicGeometry.Scheme.Modules.projectionFormulaIso, asIso_hom]
    rw [← Category.assoc, h1, Category.assoc, ← Functor.map_comp, h2, Iso.hom_inv_id_assoc]
    exact h3
  -- Step 3 + assembly
  have hΦ := LineBundle.mulBySection_eq N L s
  have w : LineBundle.mulBySection N L s ≫ adj.unit.app L.toModules = 0 := by
    rw [hΦ, Category.assoc, Category.assoc, ← hψ, ← Category.assoc (N.toModules ◁ σ), hzero₂,
      zero_comp, comp_zero]
  refine ⟨w, ShortComplex.shortExact_of_iso (ShortComplex.isoMk (ρ_ N.toModules) Φ ψ ?_ ?_) hS₂⟩
  · show (ρ_ N.toModules).hom ≫ LineBundle.mulBySection N L s = (N.toModules ◁ σ) ≫ Φ.hom
    rw [hΦ, Iso.hom_inv_id_assoc]
  · show Φ.hom ≫ adj.unit.app L.toModules = (N.toModules ◁ adj.unit.app M) ≫ ψ.hom
    exact hψ.symm

end
