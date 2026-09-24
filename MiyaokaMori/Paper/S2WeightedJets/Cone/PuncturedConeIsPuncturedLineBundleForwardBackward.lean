import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleContract
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleForwardBackwardJunctionAlpha
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleForwardBackwardJunctionBeta
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleForwardBackwardSectionAPI
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleForwardBackwardJunctionCoord

/-! # `α ≫ β = 𝟙`

The first of the two inverse identities: the morphisms `α : Z^× → Tot(L)^×` and `β : Tot(L)^× → Z^×`
satisfying the two characterising properties compose to the identity of `Z^×`
(eq. (2.1) of the paper: "the two constructions are inverse").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `α ≫ β = 𝟙`: a morphism from `Z^×` to itself is determined by its coordinates in `Tot(A^{⊕(N+1)})`, and the
two characterising properties bring the coordinates back to `z_i` (eq. (2.1) of the paper).

Proof: let `j := (puncturedCone …).ι ≫ subschemeι : Z^× → Tot(A^{⊕(N+1)})`, an open immersion followed by a
closed immersion, hence a monomorphism; so it suffices that `(α ≫ β) ≫ j = 𝟙 ≫ j`. Both sides are morphisms
`Over.mk t ⟶ totalSpace (pow A (N+1))` over `C` (`β ≫ t = β ≫ g ≫ pr₁ = π ≫ pr₁`,
`α ≫ π ≫ pr₁ = g ≫ pr₁ = t`, `comp_fst`), so by `totalSpaceHom_ext_of_coordinates` it suffices to compare the
`i`-th coordinates:
1. the `i`-th coordinate of `α ≫ β ≫ j` is `α^*` of the `i`-th coordinate of `β ≫ j`
   (`totalSpaceHomEquiv_naturality_coordinate`), which is `α^*(β^* z_i)` (definition of `coord`, transport of
   `coordOverProduct`);
2. by the second clause of `hβ`, `β^*z_i` (transported to `Γ(T×, π^*pr₁^*A)`) is `⟨w_taut, π^*q_i⟩`;
3. `α^*⟨w_taut, π^*q_i⟩ = ⟨α^*w_taut, α^*π^*q_i⟩` (`contractSections_pullback`), and `α^*w_taut = w_α`: `w_taut`
   corresponds to `ι : Over.mk π ⟶ totalSpace L`, precomposition with `α` gives `Over.homMk (α ≫ ι)` (whose
   `hom` is `g`), which corresponds to `w_α` by `totalSpaceHomEquiv_naturality`; `α ≫ π = g` gives
   `α^*π^*q_i = g^*q_i` (`pullbackComp` + `pullbackCongr`);
4. by the second clause of `hα`, `⟨w_α, g^*q_i⟩ = z_i`. Hence the `i`-th coordinate of `α ≫ β ≫ j` is `z_i`, the
   `i`-th coordinate of `j`.

Implementation: the monomorphism `j` uses the `Mono` instances of `IsClosedImmersion`/`IsOpenImmersion`; all
transports at the level of coordinates go through the section API of `…ForwardBackwardSectionAPI`
(`transportSection`/`pullbackSection`/`uncompSection`/`coordinateOf`/`contractSections'`); steps 1–4 are
`coordinateOf_congr` + `coordinateOf_comp`, `IsTotalSpaceToConeHom.exists_val` (`…JunctionBeta`),
`contractSections'_pullback` + `contractSections'_congr` + `totalSpaceHomEquiv'_comp`, and
`IsConeToTotalSpaceHom.exists_val` (`…JunctionAlpha`); the transport between coordinates over `C` and over
`C ×_k X` (including the associativity coherence of `pullbackComp`, from Mathlib's
`pseudofunctor_associativity`) is `coordinate_comp_eq_of_pullback_pullback_eq'`, and the unfolding of
`coordOverProduct` is `coordOverProduct_eq` (`…JunctionCoord`). -/
theorem isConeToTotalSpaceHom_comp_isTotalSpaceToConeHom {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j)
    (α : (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme ⟶ (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).toScheme)
    (β : (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).toScheme ⟶ (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme)
    (hα : IsConeToTotalSpaceHom e E A hdeg α) (hβ : IsTotalSpaceToConeHom e E A hdeg β) :
    α ≫ β = CategoryTheory.CategoryStruct.id _ := by
  obtain ⟨hα1, hα2⟩ := IsConeToTotalSpaceHom.exists_val e E A hdeg hα
  obtain ⟨hβ1, hβ2⟩ := IsTotalSpaceToConeHom.exists_val e E A hdeg hβ
  -- j := ι_{Z^×} ≫ subschemeι : Z^× → Tot(A^{⊕(N+1)}) is a monomorphism
  have h1 : CategoryTheory.Mono (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
    (homogeneousEquationSection A N (E.F j) (E.homogeneous j))).subschemeι := inferInstance
  -- (instance resolution alone fails here: in the composite the domain of `subschemeι` is spelled
  -- `(twistedAffineCone …).left`, which reducible unification does not unfold to `I.subscheme`)
  have hmono : CategoryTheory.Mono ((puncturedCone A N E.deg hdeg E.F E.homogeneous).ι ≫
    (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _ (homogeneousEquationSection A N (E.F j) (E.homogeneous j))).subschemeι) :=
    CategoryTheory.mono_comp' inferInstance h1
  rw [← CategoryTheory.cancel_mono ((puncturedCone A N E.deg hdeg E.F E.homogeneous).ι ≫ (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _ (homogeneousEquationSection A N (E.F j) (E.homogeneous j))).subschemeι), CategoryTheory.Category.id_comp]
  -- (α ≫ β) ≫ t = t
  have hφt : (α ≫ β) ≫ (puncturedConeToProduct.base e E A hdeg) = (puncturedConeToProduct.base e E A hdeg) := by
    rw [CategoryTheory.Category.assoc, ← puncturedConeToProduct.comp_fst e E A hdeg,
      ← CategoryTheory.Category.assoc β (puncturedConeToProduct e E A hdeg), hβ1, ← CategoryTheory.Category.assoc α (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)), hα1]
  have wj : ((puncturedCone A N E.deg hdeg E.F E.homogeneous).ι ≫ (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _ (homogeneousEquationSection A N (E.F j) (E.homogeneous j))).subschemeι) ≫ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom = (puncturedConeToProduct.base e E A hdeg) :=
    (puncturedConeToProduct.toTot_w e E A hdeg).trans (CategoryTheory.Over.mk_hom_eq _)
  have w0 : ((α ≫ β) ≫ ((puncturedCone A N E.deg hdeg E.F E.homogeneous).ι ≫ (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _ (homogeneousEquationSection A N (E.F j) (E.homogeneous j))).subschemeι)) ≫ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom = (α ≫ β) ≫ (puncturedConeToProduct.base e E A hdeg) :=
    (CategoryTheory.Category.assoc _ _ _).trans (congrArg (fun x => (α ≫ β) ≫ x) wj)
  have w1 : ((α ≫ β) ≫ ((puncturedCone A N E.deg hdeg E.F E.homogeneous).ι ≫ (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _ (homogeneousEquationSection A N (E.F j) (E.homogeneous j))).subschemeι)) ≫ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom = (puncturedConeToProduct.base e E A hdeg) := w0.trans hφt
  -- C-morphisms Over.mk t ⟶ Tot(A^{⊕(N+1)}) are determined by their coordinates
  refine AlgebraicGeometry.Scheme.ext_of_coordinateOf A (N + 1) (puncturedConeToProduct.base e E A hdeg) _ _ w1 wj (fun ℓ => ?_)
  -- the ℓ-th coordinate of (α ≫ β) ≫ j is the transported (α ≫ β)^* z_ℓ
  refine ((AlgebraicGeometry.Scheme.coordinateOf_congr A (N + 1) hφt ((α ≫ β) ≫ ((puncturedCone A N E.deg hdeg E.F E.homogeneous).ι ≫ (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _ (homogeneousEquationSection A N (E.F j) (E.homogeneous j))).subschemeι)) w0 w1 ℓ).trans
    (congrArg (AlgebraicGeometry.Scheme.Modules.transportSection hφt A) (AlgebraicGeometry.Scheme.coordinateOf_comp A (N + 1) (puncturedConeToProduct.base e E A hdeg) (α ≫ β) ((puncturedCone A N E.deg hdeg E.F E.homogeneous).ι ≫ (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _ (homogeneousEquationSection A N (E.F j) (E.homogeneous j))).subschemeι) wj w0 ℓ))).trans ?_
  refine Eq.trans ?_ (puncturedConeToProduct.coord_eq' e E A hdeg ℓ)
  refine (congrArg (fun z => AlgebraicGeometry.Scheme.Modules.transportSection hφt A (AlgebraicGeometry.Scheme.Modules.pullbackSection (α ≫ β) (puncturedConeToProduct.base e E A hdeg) A z)) (puncturedConeToProduct.coord_eq' e E A hdeg ℓ).symm).trans ?_
  -- core transport: reduce to the C ×ₖ X-level identity Φ_α(Φ_β(z_ℓ)) = z_ℓ
  refine AlgebraicGeometry.Scheme.Modules.coordinate_comp_eq_of_pullback_pullback_eq' (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) A (puncturedConeToProduct e E A hdeg) (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) α β hα1 hβ1
    (puncturedConeToProduct.base e E A hdeg) (puncturedConeToProduct.comp_fst e E A hdeg) (puncturedConeToProduct.coord e E A hdeg ℓ) ?_ hφt
  refine ((congrArg (fun z => AlgebraicGeometry.Scheme.Modules.transportSection hα1 ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A) (AlgebraicGeometry.Scheme.Modules.pullbackSection α (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A) (AlgebraicGeometry.Scheme.Modules.transportSection hβ1 ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A) (AlgebraicGeometry.Scheme.Modules.pullbackSection β (puncturedConeToProduct e E A hdeg) ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A) z))))
    (puncturedConeToProduct.coordOverProduct_eq e E A hdeg ℓ)).symm).trans
    (Eq.trans ?_ (puncturedConeToProduct.coordOverProduct_eq e E A hdeg ℓ))
  -- Φ_β(z_ℓ) = ⟨w_taut, π^*q_ℓ⟩ (hβ), then α^* commutes with the pairing (`contractSections_pullback`)
  refine (congrArg (fun x => AlgebraicGeometry.Scheme.Modules.transportSection hα1 ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A) (AlgebraicGeometry.Scheme.Modules.pullbackSection α (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A) x)) (hβ2 ℓ)).trans ?_
  refine (congrArg (AlgebraicGeometry.Scheme.Modules.transportSection hα1 ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A))
    (conePuncturedLineBundle.contractSections'_pullback e A (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) α (AlgebraicGeometry.Scheme.totalSpacePunctured.tautologicalSection (conePuncturedLineBundle e A)) (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) (conePuncturedLineBundle.coordinate C e ℓ)))).trans ?_
  refine (conePuncturedLineBundle.contractSections'_congr e A hα1 _ _).symm.trans ?_
  -- α^* w_taut = w_α (naturality) and α^*(π^* q_ℓ) = g^* q_ℓ
  have wι : (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι ≫ (AlgebraicGeometry.Scheme.totalSpace (conePuncturedLineBundle e A)).hom = (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) := (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase_eq (conePuncturedLineBundle e A)).symm
  have w00 : (α ≫ (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι) ≫ (AlgebraicGeometry.Scheme.totalSpace (conePuncturedLineBundle e A)).hom = α ≫ (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) :=
    (CategoryTheory.Category.assoc _ _ _).trans (congrArg (fun x => α ≫ x) wι)
  have wα : (α ≫ (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι) ≫ (AlgebraicGeometry.Scheme.totalSpace (conePuncturedLineBundle e A)).hom = (puncturedConeToProduct e E A hdeg) := w00.trans hα1
  have hw : AlgebraicGeometry.Scheme.Modules.transportSection hα1 (conePuncturedLineBundle e A) (AlgebraicGeometry.Scheme.Modules.pullbackSection α (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) (conePuncturedLineBundle e A) (AlgebraicGeometry.Scheme.totalSpacePunctured.tautologicalSection (conePuncturedLineBundle e A))) = AlgebraicGeometry.Scheme.totalSpaceHomEquiv' (conePuncturedLineBundle e A) (puncturedConeToProduct e E A hdeg) (α ≫ (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι) wα :=
    ((congrArg (fun x => AlgebraicGeometry.Scheme.Modules.transportSection hα1 (conePuncturedLineBundle e A) (AlgebraicGeometry.Scheme.Modules.pullbackSection α (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) (conePuncturedLineBundle e A) x))
      (AlgebraicGeometry.Scheme.totalSpacePunctured.tautologicalSection_eq' (conePuncturedLineBundle e A))).trans
      (congrArg (AlgebraicGeometry.Scheme.Modules.transportSection hα1 (conePuncturedLineBundle e A)) (AlgebraicGeometry.Scheme.totalSpaceHomEquiv'_comp (conePuncturedLineBundle e A) (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) α (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι wι w00).symm)).trans
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv'_congr (conePuncturedLineBundle e A) hα1 (α ≫ (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι) w00 wα).symm
  have hq := AlgebraicGeometry.Scheme.Modules.transportSection_pullbackSection_sectionPullbackAlong α (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) (puncturedConeToProduct e E A hdeg) hα1 ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj (e.oX 1)) (conePuncturedLineBundle.coordinate C e ℓ)
  exact (congr_arg₂ (fun w q => conePuncturedLineBundle.contractSections' e A (puncturedConeToProduct e E A hdeg) w q) hw hq).trans (hα2 ℓ)

end
