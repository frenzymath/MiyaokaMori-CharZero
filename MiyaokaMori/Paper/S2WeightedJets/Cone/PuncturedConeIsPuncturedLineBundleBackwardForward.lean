import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleContract
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleContractInjective
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleForwardBackwardJunctionAlpha
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleForwardBackwardJunctionBeta
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleForwardBackwardSectionAPI

/-! # `β ≫ α = 𝟙`

The second of the two inverse identities: the morphisms `β : Tot(L)^× → Z^×` and `α : Z^× → Tot(L)^×`
satisfying the two characterising properties compose to the identity of `Tot(L)^×`
(eq. (2.1) of the paper: "the two constructions are inverse").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `contractSections_injective` in the section API. -/
theorem conePuncturedLineBundle.contractSections'_injective {k : Type u} [Field k]
    {C X : AlgebraicGeometry.Scheme.{u}} [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (A : C.Modules) [A.IsLineBundle] {S : AlgebraicGeometry.Scheme.{u}}
    (f : S ⟶ CategoryTheory.Limits.pullback (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (w w' : (((AlgebraicGeometry.Scheme.Modules.pullback f).obj (conePuncturedLineBundle e A)).val.obj
      (Opposite.op ⊤) : Type u))
    (h : ∀ i : Fin (N + 1),
      conePuncturedLineBundle.contractSections' e A f w (sectionPullbackAlong f (conePuncturedLineBundle.coordinate C e i)) =
        conePuncturedLineBundle.contractSections' e A f w' (sectionPullbackAlong f (conePuncturedLineBundle.coordinate C e i))) :
    w = w' :=
  conePuncturedLineBundle.contractSections_injective e A (CategoryTheory.Over.mk f) w w' h

/-- `β ≫ α = 𝟙`: a `C ×_k X`-morphism from `Tot(L)^×` to itself is determined by a section of `π^*L`, the
section is determined by its pairings with the `q_i`, and the two characterising properties bring the
pairings back to the tautological section (eq. (2.1) of the paper).

Proof: `ι := (totalSpacePunctured L).ι` is a monomorphism, so it suffices that `(β ≫ α) ≫ ι = ι`. Both
sides are morphisms `Over.mk π ⟶ totalSpace L` over `C ×_k X` (`β ≫ α ≫ π = β ≫ g = π`), so by
injectivity of `totalSpaceHomEquiv` it suffices to compare the corresponding sections:
1. the section corresponding to `β ≫ α ≫ ι` is `β^*(w_α)` (`totalSpaceHomEquiv_naturality`, with
   `pullbackComp`/`pullbackCongr` transporting `(β ≫ g)^*` to `π^*`), and the section corresponding
   to `ι` is `w_taut` (by definition);
2. by `contractSections_injective`, for every `i`,
   `⟨β^*w_α, π^*q_i⟩ = β^*⟨w_α, g^*q_i⟩` (`contractSections_pullback`) `= β^*z_i` (second clause of `hα`)
   `= ⟨w_taut, π^*q_i⟩` (second clause of `hβ`). Hence `β^*w_α = w_taut`.

Implementation: `totalSpaceHomEquiv'_injective` (a morphism on `Over.mk π` is determined by its section);
step 1 is `totalSpaceHomEquiv'_congr` + `totalSpaceHomEquiv'_comp` (`…ForwardBackwardSectionAPI`);
step 2 is `contractSections'_injective` (this module), `IsTotalSpaceToConeHom.exists_val`
(`…JunctionBeta`), `contractSections'_congr`, `contractSections'_pullback` and
`IsConeToTotalSpaceHom.exists_val` (`…JunctionAlpha`). -/

theorem isTotalSpaceToConeHom_comp_isConeToTotalSpaceHom {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j)
    (α : (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme ⟶ (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).toScheme)
    (β : (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).toScheme ⟶ (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme)
    (hα : IsConeToTotalSpaceHom e E A hdeg α) (hβ : IsTotalSpaceToConeHom e E A hdeg β) :
    β ≫ α = CategoryTheory.CategoryStruct.id _ := by
  obtain ⟨hα1, hα2⟩ := IsConeToTotalSpaceHom.exists_val e E A hdeg hα
  obtain ⟨hβ1, hβ2⟩ := IsTotalSpaceToConeHom.exists_val e E A hdeg hβ
  rw [← CategoryTheory.cancel_mono (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι, CategoryTheory.Category.id_comp, CategoryTheory.Category.assoc]
  -- the `Over`-compatibility proofs
  have wι : (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι ≫ (AlgebraicGeometry.Scheme.totalSpace (conePuncturedLineBundle e A)).hom = (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) := (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase_eq (conePuncturedLineBundle e A)).symm
  have wα : (α ≫ (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι) ≫ (AlgebraicGeometry.Scheme.totalSpace (conePuncturedLineBundle e A)).hom = (puncturedConeToProduct e E A hdeg) :=
    (CategoryTheory.Category.assoc _ _ _).trans ((congrArg (fun x => α ≫ x) wι).trans hα1)
  have w0 : (β ≫ α ≫ (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι) ≫ (AlgebraicGeometry.Scheme.totalSpace (conePuncturedLineBundle e A)).hom = β ≫ (puncturedConeToProduct e E A hdeg) :=
    (CategoryTheory.Category.assoc _ _ _).trans (congrArg (fun x => β ≫ x) wα)
  have w1 : (β ≫ α ≫ (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι) ≫ (AlgebraicGeometry.Scheme.totalSpace (conePuncturedLineBundle e A)).hom = (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) := w0.trans hβ1
  -- C ×ₖ X-morphisms Over.mk π ⟶ Tot(L) are determined by their sections
  refine AlgebraicGeometry.Scheme.totalSpaceHomEquiv'_injective (conePuncturedLineBundle e A) (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) _ _ w1 wι ?_
  -- step 1 (naturality): the section of β ≫ α ≫ ι is the transported β-pullback of w_α
  refine ((AlgebraicGeometry.Scheme.totalSpaceHomEquiv'_congr (conePuncturedLineBundle e A) hβ1 (β ≫ α ≫ (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι) w0 w1).trans
    (congrArg (AlgebraicGeometry.Scheme.Modules.transportSection hβ1 (conePuncturedLineBundle e A)) (AlgebraicGeometry.Scheme.totalSpaceHomEquiv'_comp (conePuncturedLineBundle e A) (puncturedConeToProduct e E A hdeg) β (α ≫ (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι) wα w0))).trans ?_
  -- step 2: both sections have the same pairings with the coordinates q_i (`contractSections_injective`)
  refine conePuncturedLineBundle.contractSections'_injective e A (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) _ _ (fun i => ?_)
  refine Eq.trans ?_ ((hβ2 i).trans (congrArg (fun w => conePuncturedLineBundle.contractSections' e A (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) w (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) (conePuncturedLineBundle.coordinate C e i)))
    (AlgebraicGeometry.Scheme.totalSpacePunctured.tautologicalSection_eq' (conePuncturedLineBundle e A))))
  refine (congrArg (fun q => conePuncturedLineBundle.contractSections' e A (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) (AlgebraicGeometry.Scheme.Modules.transportSection hβ1 (conePuncturedLineBundle e A) (AlgebraicGeometry.Scheme.Modules.pullbackSection β (puncturedConeToProduct e E A hdeg) (conePuncturedLineBundle e A) (AlgebraicGeometry.Scheme.totalSpaceHomEquiv' (conePuncturedLineBundle e A) (puncturedConeToProduct e E A hdeg) (α ≫ (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι) wα))) q)
    (AlgebraicGeometry.Scheme.Modules.transportSection_pullbackSection_sectionPullbackAlong β (puncturedConeToProduct e E A hdeg) (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) hβ1 ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj (e.oX 1)) (conePuncturedLineBundle.coordinate C e i)).symm).trans ?_
  refine (conePuncturedLineBundle.contractSections'_congr e A hβ1 _ _).trans ?_
  refine (congrArg (AlgebraicGeometry.Scheme.Modules.transportSection hβ1 ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A))
    (conePuncturedLineBundle.contractSections'_pullback e A (puncturedConeToProduct e E A hdeg) β (AlgebraicGeometry.Scheme.totalSpaceHomEquiv' (conePuncturedLineBundle e A) (puncturedConeToProduct e E A hdeg) (α ≫ (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι) wα)
      (sectionPullbackAlong (puncturedConeToProduct e E A hdeg) (conePuncturedLineBundle.coordinate C e i))).symm).trans ?_
  exact congrArg (fun x => AlgebraicGeometry.Scheme.Modules.transportSection hβ1 ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A) (AlgebraicGeometry.Scheme.Modules.pullbackSection β (puncturedConeToProduct e E A hdeg) ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A) x)) (hα2 i)

end
