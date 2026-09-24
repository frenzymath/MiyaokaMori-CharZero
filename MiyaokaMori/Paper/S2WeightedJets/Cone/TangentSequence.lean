import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.TangentBundle
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundle
import MiyaokaMori.AlgebraicGeometry.Modules.EulerSectionNowhereVanishing
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousAtSections
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.HomogeneousCoordinateSections
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.HomogeneousCoordinateTupleIsOver
import MiyaokaMori.Paper.S2WeightedJets.Cone.HomogeneousIdealGenerators
import MiyaokaMori.Paper.S2WeightedJets.Cone.HyperplaneBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesFiniteTypeInstances
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackRank
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbedding
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackShortExactLocallyFree
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeOpen
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeToProduct
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeToProductSmooth
import MiyaokaMori.AlgebraicGeometry.Modules.RelativeTangentProductProjection
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeTangentPullbackIso
import MiyaokaMori.AlgebraicGeometry.Morphisms.RelativeTangentSequenceSmooth
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedLineBundleIsLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSection
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSectionInPunctured
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSectionToProduct
import MiyaokaMori.CategoryTheory.ShortExactTransport
import MiyaokaMori.Paper.S2WeightedJets.Cone.TautologicalBundleOnVariety
import MiyaokaMori.AlgebraicGeometry.Modules.TotLinePunctured
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineCone

/-! # The tangent sequence

The tangent sequence `0 → O_C → E → f^*T_X → 0`, `E = s^*T_{𝒵/C}` (eq. (2.2) of the
paper): `𝒵^× → C ×_k X` is the punctured total space of `L = pr₁^*A ⊗ pr₂^*O_X(-1)`; pull back the
exact sequence of relative tangent sheaves of `𝒵^× → C × X → C` along `s`; the first term
`s^*T_{𝒵^×/(C×X)}` is trivialized to `O_C` by the infinitesimal scalar action (Euler vector field)
at `s`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Given isomorphisms at the three terms of a short complex, transport a short exact sequence to the
three prescribed objects (an existential wrapper of `shortExact_transport_of_iso`). -/
theorem shortExact_exists_of_endpoint_isos {𝒞 : Type u} [Category 𝒞] [HasZeroMorphisms 𝒞]
    (S : CategoryTheory.ShortComplex 𝒞) (hS : S.ShortExact) {A B D : 𝒞}
    (a₁ : S.X₁ ≅ A) (a₂ : S.X₂ ≅ B) (a₃ : S.X₃ ≅ D) :
    ∃ (i : A ⟶ B) (π : B ⟶ D) (hz : i ≫ π = 0),
      (CategoryTheory.ShortComplex.mk i π hz).ShortExact := by
  refine ⟨a₁.inv ≫ S.f ≫ a₂.hom, a₂.inv ≫ S.g ≫ a₃.hom, ?_, ?_⟩
  · simp only [Category.assoc, Iso.hom_inv_id_assoc, S.zero_assoc, zero_comp, comp_zero]
  · refine shortExact_transport_of_iso a₁ a₂ a₃ ?_ ?_ hS
    · show a₁.hom ≫ (a₁.inv ≫ S.f ≫ a₂.hom) = S.f ≫ a₂.hom
      simp only [Iso.hom_inv_id_assoc]
    · show a₂.hom ≫ (a₂.inv ≫ S.g ≫ a₃.hom) = S.g ≫ a₃.hom
      simp only [Iso.hom_inv_id_assoc]

/-!
The geometric work in the tangent-sequence argument is the identification of the
three terms after pulling back the relative tangent sequence from the punctured
cone to the seed section.  We keep that identification in one explicit bridge:
a short exact sequence on `C` whose three terms are isomorphic to `O_C`,
`E = s^*T_{Z/C}` and `f^*T_X`; the main theorem below only transports short
exactness across the three endpoint isomorphisms.

Route (eq. (2.2) of the paper):
* `W := Z^×` (punctured cone), `ι : W → Z`, `p : Z → C`; the seed section `s` factors as `s' ≫ ι`
  (`seedSection_mem_punctured`);
* `q := puncturedConeToProduct : W → C ×ₖ X`, with `q ≫ pr₁ = ι ≫ p` (by construction) and
  `s' ≫ q = (𝟙, f)` (`seedSection_comp_puncturedConeToProduct`; needs `f` over `k`, which follows from
  `hcoord` by `IsHomogeneousCoordinateTuple.isOver`), hence `s' ≫ q ≫ pr₂ = f`;
* `q` and `pr₁` are smooth (`puncturedConeToProduct_smoothOfRelativeDimension`; base change of `X → Spec k`),
  so `0 → T_q → T_{q ≫ pr₁} → q^*T_{pr₁} → 0` is short exact on `W` (`relativeTangent_shortExact`);
* first term: `W ≅ Tot(L)^×` over `C ×ₖ X` (`puncturedConeIsoPuncturedTotalSpace`), and the Euler vector
  field trivialises `T_{Tot(L)^×/(C×X)}` (`eulerVectorField_trivializes_punctured`); transported along the
  isomorphism (`relativeTangent_pullback_of_isIso`, `pullbackUnitIso`) this gives `T_q ≅ O_W`;
* middle term: `T_{q ≫ pr₁} = T_{ι ≫ p} ≅ ι^*T_p` (`relativeTangent_restrict_open`, Stacks 01US);
* third term: `T_{pr₁} ≅ pr₂^*T_X` (`relativeTangent_prod_fst`), so `q^*T_{pr₁} ≅ q^*pr₂^*T_X`, locally free
  of finite type;
* pull back along `s'` (`pullback_shortExact_of_locallyFree`), and identify the three terms:
  `s'^*O_W ≅ O_C`, `s'^*ι^*T_p ≅ (s' ≫ ι)^*T_p = s^*T_p = E`, `s'^*q^*pr₂^*T_X ≅ f^*T_X`
  (`pullbackComp`, `pullbackCongr`).
-/
theorem cone_tangent_endpoint_bridge {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {X : SmoothProjectiveVariety k} {N δ : ℕ}
    (e : ProjectiveEmbedding k X.toScheme N) (E : EmbeddingEquations k e δ)
    (hdeg : ∀ j, 0 < E.deg j) (f : C.toScheme ⟶ X.toScheme)
    (coord : Fin (N + 1) → ((seedLineBundle e f).val.obj (Opposite.op ⊤) : Type u))
    (hcoord : IsHomogeneousCoordinateTuple e f coord)
    (hvanish : ∀ j, evalHomogeneousAtSections (seedLineBundle e f) (E.F j)
      (E.homogeneous j) coord = 0) :
    let Z := twistedAffineCone (seedLineBundle e f) N E.deg E.F E.homogeneous
    let s := seedSection (seedLineBundle e f) N coord E.deg E.F E.homogeneous hvanish
    ∃ S : CategoryTheory.ShortComplex C.toScheme.Modules, S.ShortExact ∧
      Nonempty (S.X₁ ≅ (show C.toScheme.Modules from
        SheafOfModules.unit C.toScheme.ringCatSheaf)) ∧
      Nonempty (S.X₂ ≅ coneTangentBundle Z.hom s.1 s.2) ∧
      Nonempty (S.X₃ ≅
        (AlgebraicGeometry.Scheme.Modules.pullback f).obj (tangentBundle X).toModules) := by
  intro Z s
  -- notation
  let A : C.toScheme.Modules := seedLineBundle e f
  let W : Z.left.Opens := puncturedCone A N E.deg hdeg E.F E.homogeneous
  let q : W.toScheme ⟶ CategoryTheory.Limits.pullback
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    puncturedConeToProduct e E A hdeg
  let pr₁ := CategoryTheory.Limits.pullback.fst
    (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  let pr₂ := CategoryTheory.Limits.pullback.snd
    (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  -- the seed section lands in the punctured cone, and `s' ≫ q = (𝟙, f)`
  have hf : f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    IsHomogeneousCoordinateTuple.isOver e f coord hcoord
  obtain ⟨s', hs'⟩ := seedSection_mem_punctured e E f coord hcoord hdeg hvanish
  have hsq : s' ≫ q = CategoryTheory.Limits.pullback.lift (𝟙 C.toScheme) f (by simp) :=
    seedSection_comp_puncturedConeToProduct e E hdeg f coord hcoord hvanish s' hs'
  have hq₁ : q ≫ pr₁ = W.ι ≫ Z.hom := by
    show CategoryTheory.Limits.pullback.lift _ _ _ ≫ CategoryTheory.Limits.pullback.fst _ _ = _
    rw [CategoryTheory.Limits.pullback.lift_fst]
    rfl
  have hf₂ : s' ≫ q ≫ pr₂ = f := by
    rw [← Category.assoc, hsq, CategoryTheory.Limits.pullback.lift_snd]
  -- smoothness of the two legs `W → C ×ₖ X → C`
  have : AlgebraicGeometry.Smooth (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    X.smooth
  have : AlgebraicGeometry.SmoothOfRelativeDimension 1 q :=
    puncturedConeToProduct_smoothOfRelativeDimension e E A hdeg
  have : AlgebraicGeometry.Smooth q := AlgebraicGeometry.SmoothOfRelativeDimension.smooth 1 q
  obtain ⟨i₀, π₀, hz₀, hS₀⟩ := AlgebraicGeometry.relativeTangent_shortExact q pr₁
  -- first term: Euler trivialisation transported along `W ≅ Tot(L)^×`
  obtain ⟨φ, hφ⟩ := puncturedConeIsoPuncturedTotalSpace e E A hdeg
  obtain ⟨eu⟩ := eulerVectorField_trivializes_punctured (conePuncturedLineBundle e A)
  obtain ⟨tφ⟩ := AlgebraicGeometry.relativeTangent_pullback_of_isIso φ.hom
    ((AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι ≫
      (AlgebraicGeometry.Scheme.totalSpace (conePuncturedLineBundle e A)).hom)
  let b₁ : AlgebraicGeometry.relativeTangent q ≅
      (show W.toScheme.Modules from SheafOfModules.unit W.toScheme.ringCatSheaf) :=
    AlgebraicGeometry.relativeTangent_congr hφ.symm ≪≫ tφ.symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback φ.hom).mapIso eu.symm ≪≫
      AlgebraicGeometry.Scheme.Modules.pullbackUnitIso φ.hom
  -- middle term: `T_{q ≫ pr₁} = T_{ι ≫ p} ≅ ι^*T_p`
  obtain ⟨tι⟩ := AlgebraicGeometry.relativeTangent_restrict_open W Z.hom
  let b₂ : AlgebraicGeometry.relativeTangent (q ≫ pr₁) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback W.ι).obj (AlgebraicGeometry.relativeTangent Z.hom) :=
    AlgebraicGeometry.relativeTangent_congr hq₁ ≪≫ tι.symm
  -- third term: `q^*T_{pr₁} ≅ q^*pr₂^*T_X`
  obtain ⟨tp⟩ := relativeTangent_prod_fst C X
  let b₃ : (AlgebraicGeometry.Scheme.Modules.pullback q).obj (AlgebraicGeometry.relativeTangent pr₁) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback q).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback pr₂).obj (tangentBundle X).toModules) :=
    (AlgebraicGeometry.Scheme.Modules.pullback q).mapIso tp
  -- the sequence on `W` with the three terms replaced
  obtain ⟨i₁, π₁, hz₁, hS₁⟩ := shortExact_exists_of_endpoint_isos _ hS₀ b₁ b₂ b₃
  let S₁ : CategoryTheory.ShortComplex W.toScheme.Modules := CategoryTheory.ShortComplex.mk i₁ π₁ hz₁
  have : ((AlgebraicGeometry.Scheme.Modules.pullback pr₂).obj (tangentBundle X).toModules).IsLocallyFree :=
    (AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback pr₂ (tangentBundle X).toModules).1
  have : S₁.X₃.IsLocallyFree :=
    (AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback q
      ((AlgebraicGeometry.Scheme.Modules.pullback pr₂).obj (tangentBundle X).toModules)).1
  have : S₁.X₃.IsFiniteType := inferInstance
  -- pull back along `s'`
  have hS₂ := AlgebraicGeometry.Scheme.Modules.pullback_shortExact_of_locallyFree s' hS₁
  refine ⟨S₁.map (AlgebraicGeometry.Scheme.Modules.pullback s'), hS₂,
    ⟨AlgebraicGeometry.Scheme.Modules.pullbackUnitIso s'⟩, ⟨?_⟩, ⟨?_⟩⟩
  · -- `s'^*ι^*T_p ≅ (s' ≫ ι)^*T_p = s^*T_p`
    exact (AlgebraicGeometry.Scheme.Modules.pullbackComp s' W.ι).app _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr hs').app _
  · -- `s'^*q^*pr₂^*T_X ≅ (s' ≫ q ≫ pr₂)^*T_X = f^*T_X`
    exact (AlgebraicGeometry.Scheme.Modules.pullbackComp s' q).app _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp (s' ≫ q) pr₂).app _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr (by rw [Category.assoc]; exact hf₂)).app _

theorem cone_tangent_shortExact {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    {X : SmoothProjectiveVariety k} {N δ : ℕ}
    (e : ProjectiveEmbedding k X.toScheme N) (E : EmbeddingEquations k e δ)
    (hdeg : ∀ j, 0 < E.deg j) (f : C.toScheme ⟶ X.toScheme)
    (coord : Fin (N + 1) → ((seedLineBundle e f).val.obj (Opposite.op ⊤) : Type u))
    (hcoord : IsHomogeneousCoordinateTuple e f coord)
    (hvanish : ∀ j, evalHomogeneousAtSections (seedLineBundle e f) (E.F j) (E.homogeneous j) coord = 0) :
    let Z := twistedAffineCone (seedLineBundle e f) N E.deg E.F E.homogeneous
    let s := seedSection (seedLineBundle e f) N coord E.deg E.F E.homogeneous hvanish
    ∃ (i : (show C.toScheme.Modules from SheafOfModules.unit C.toScheme.ringCatSheaf) ⟶
        coneTangentBundle Z.hom s.1 s.2)
      (π : coneTangentBundle Z.hom s.1 s.2 ⟶
        (AlgebraicGeometry.Scheme.Modules.pullback f).obj (tangentBundle X).toModules)
      (hz : i ≫ π = 0),
      (CategoryTheory.ShortComplex.mk i π hz).ShortExact := by
  intro Z s
  obtain ⟨S, hS, ⟨a₁⟩, ⟨a₂⟩, ⟨a₃⟩⟩ := cone_tangent_endpoint_bridge e E hdeg f coord hcoord hvanish
  exact shortExact_exists_of_endpoint_isos S hS a₁ a₂ a₃

end
