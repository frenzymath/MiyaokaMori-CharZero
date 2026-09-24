import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLift
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecStructureIso
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldEqResidueFieldAtGenericPoint
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedAlgebraTotal
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetChart
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetLocalCoordinates
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetRescalingAction
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetThickening
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetThickeningSections
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetTransition
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalProperty
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetFunctor
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetRepresentableBy
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetScheme
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.Paper.S2WeightedJets.Jets.UnbasedRelativeJetScheme
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedGradedAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Ygg.WeightedProjectivization
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetOverRho
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.CoefficientSections
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.FrameChangeNormalization
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedAlgebraTotalProjection
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetChartTrivialization
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhood
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodToTotalSpace
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleFrame
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.NormalizedTupleNowhereZero
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftPrecomp
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymPowLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineCoefficientMap
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.TruncatedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectiveRationalPoints
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetThickeningSectionsCoeff
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback
import MiyaokaMori.Paper.S2WeightedJets.Jets.OfBasedJetChartSections
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetRescalingChart
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecOfAlgebraMapSections
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.IsLineBundleZpow
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleSectionGenericGermZero
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualSectionRestrictHom
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierCanonicalSection
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FrameLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetWeightComponentEqCoefficientFrameHomMul
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetWeightComponentEqCoefficientGeneratesAtAux

/-! # The two coefficient encodings of a based jet agree

A based jet `ȷ` has two encodings of its coefficients.
* Jet side: `J.weightComponent m : ρ^*S_m → (L^∨)^{⊗m}`, obtained by pulling the weight-`m` jet coordinate functions
  back along the morphism `φ_J : Tot(L) → J_κ^s(𝒵/C)` given by the universal frame and taking the `m`-th graded
  component (through `symPartToMonoidalPow`).
* Cone side: `J.coefficient ℓ m`, obtained from the cone coordinate by `xiCoefficientThickening`
  (`relativeSpec.structureIso⁻¹`, then `biproduct.π_m`, then `pieceIso`).

The comparison theorem `BasedJet.weightComponent_jetCoordinate` says: for an affine open `U ⊆ C`, a function
`b ∈ Γ(𝒵, π⁻¹U)` on the cone and `q : Fin κ`, the value of `weightComponent (q+1)` (transposed along the adjunction
to `S_{q+1} → ρ_*(L^∨)^{⊗(q+1)}`) on the jet coordinate `d_q b` (the generator `coeffClass (q+1) b` of the chart
ring `J_κ(B_U, ε_U)`, which lies in the weight-`(q+1)` piece) equals
`J.pieceSection U (q+1) b := pieceIso(π_{q+1}(structureIso⁻¹(J^♯ b)))`, the `(q+1)`-th `ξ`-coefficient of `J^♯ b`
extracted by the same chain as on the cone side. For `b = x_ℓ^a` (the `ℓ`-th cone coordinate in a frame `a` of `A`)
the piece section is `J.coefficient ℓ (q+1) / ρ^*a`; `exists_pieceSection_generatesAt` states this step in the form
"they vanish simultaneously".

Also in this file: the value of `ofBasedJet` on jet coordinates (`ofBasedJet_appLE_coeffClass`, upstream), the
coefficient description of the universal frame (`universalFrame_coeff`), the weight of the jet coordinates
(`exists_part_eq_jetCoordinate`), and the consequences for the lift data: `weightComponent_generates_at`,
`weightComponent_generates_of_nowhereZero`, `genericWeightComponent_generates_of_ne_zero`. The construction data
`totOver`, `totOverField`, `universalFrameAlg`, `universalFrame`, `jetPoint`, `weightComponent` of the
projectivization live here to avoid an import cycle.

Proof outline.
0. Weight conventions: the generator `d_q b` (`q : Fin κ`) of `BasedJetAlgebra` is the coefficient of order `q+1` of
   the universal jet, and `lift` takes the coefficient of order `q+1` of `ψ(b)`; the coaction `t ↦ λ ⊗ t` of the
   rescaling makes `d_q b` a `λ^{q+1}`-eigensection, i.e. an element of `S_{q+1} = ker(weightDefect (q+1))`.
   `universalFrameAlg` sends the `q`-th piece `c` to `(c·ξ^q)·t^q` through
   `piece q →(pieceIso) (L^∨)^{⊗q} →(monoidalPowIsoTensorPower) → (tensorPowerToSymPart = symPowπ) Sym^q`;
   `weightComponent` takes `totalProj m` followed by `symPartToMonoidalPow = (symPowπ)⁻¹` (the inverse of the
   quotient map, not a symmetrization; no `m!` appears, so the argument is characteristic-free);
   `xiCoefficientThickening` uses `structureIso⁻¹ ≫ π_q ≫ pieceIso ≫ monoidalPowIsoTensorPower`, literally the first
   three steps of `universalFrameAlg`. The weights and orientations of the two encodings agree.
1. `ofBasedJet_appLE_coeffClass`: on `W.hom⁻¹U`, `ofBasedJet` is `toSpecΓ ≫ Spec.map(ofBasedJetSections) ≫` chart,
   and `chartSections` is the inverse of the chart open immersion on global sections; they cancel and
   `ofBasedJetSections(coeffClass (q+1) b) = TruncatedJetRing.coeff (q+1) (sectionsHom⁻¹(φ^♯ b))`, which is the
   definition of `jetThickening.coeff`.
2. `universalFrame_coeff`: `universalFrame = relativeSpecHomEquiv.symm ⟨universalFrameAlg, _⟩`, so the algebra map of
   `u` is `universalFrameAlg`; decompose `c = Σ_q ι_q π_q c`, use `universalFrameAlg(ι_q c_q) = pr^♯(c_q ξ^q)·t^q`,
   and take the `t^n`-coefficient with `coeff_add` and `coeff_proj_mul_parameter_pow`; only the term `q = n` survives.
3. `exists_part_eq_jetCoordinate`: the rescaling action corresponds to `ρ_λ ≫` universal jet; by step 1
   `act^♯(d_q b) = λ^{q+1}·pr₂^♯(d_q b)`, so `weightDefect (q+1)` vanishes on it and the kernel gives `x`.
4. `weightComponent_jetCoordinate`: `homEquiv` cancels `homEquiv.symm`; by step 1 (with `W = Tot(L)`, `φ = u ≫ J`)
   `φ_J^♯(d_q b) = coeff_{q+1}(u^♯(J^♯ b))`, by step 2 this is
   `structureHom(totalIncl (q+1)(symPowπ(powIso(pieceIso(π_{q+1}(structureIso⁻¹ g))))))`; then
   `structureIso⁻¹ ∘ structureHom = id`, `totalProj ∘ totalIncl = id` and
   `symPartToMonoidalPow ∘ tensorPowerToSymPart = powIso⁻¹` leave `pieceSection`.
5. `exists_pieceSection_generatesAt`: see its docstring (frame `a`, `b = x_ℓ^a`; in a frame, `totalSpaceHomEquiv`
   of the cone coordinate is `J^♯ x_ℓ^a · (p ≫ ρ)^*a`; the projection-formula isomorphism is compatible with
   tensoring with generating sections; `IsZeroAt` is invariant under isomorphisms).
6. `monoidalPow_isLineBundle`: induction on `m`. `epi_of_generatesAt`: `N` is a line bundle, `N_y` is free of rank
   one, the image of `Ψ_y` contains an element outside `𝔪N_y`, so `Ψ_y` is surjective by Nakayama and the
   (finitely generated) cokernel vanishes near `y`. `not_isZeroAt_genericPoint`: at the generic point `𝔪 = 0`, so
   `IsZeroAt` means the germ is `0`; a line bundle on an integral scheme is torsion-free.
7. `weightComponent_generates_at` chains 5, `preimage_eq_chartOpen`, 3, 4, 6; the generic-point version adds
   `not_isZeroAt_genericPoint` and `precompΨ_generates_at`.

Source: §2 of the paper (the graded coordinate algebra of jets and its weights) and the proof of
Lemma 3.1 (coefficients read off in a frame).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
  {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {ρ : FiniteCover k C}
  {L : LineBundle ρ.source.toVariety} {κ : ℕ}



/- Construction (the frame-free formulation of the proof of Lemma 3.1 of the paper):
   (1) on `Tot(L)` the line bundle `L` is canonically "framed" by the tautological section: the universal frame
       `u : Tot(L) ×_k D_κ → C̃_(κ)(L)` is given, through the universal property of the relative Spec, by the algebra
       map `⊕_{q≤κ} L^{-q} → O_Tot[t]/(t^{κ+1})`, `c ↦ (c·ξ^q) t^q`;
   (2) `u ≫ J` is a based jet on `Tot(L)` (viewed as a `C`-scheme through `Tot(L) → C̃ → C`); the representability
       data of the relative jet scheme (`ofBasedJet`) gives a `C`-morphism `φ_J : Tot(L) → J_κ^s(𝒵/C)`, which is
       `G_m`-equivariant;
   (3) the functions of weight `m` (the `m`-th piece of `jetAlgebra`, `ker(weightDefect m) ⊆ π_*O_J`) pull back along
       `φ_J` to `(ρ∘p)_*O_Tot = ρ_*(⊕ Sym^n L^∨)`; taking the `m`-th graded component gives `Ψ_m : ρ^*S_m → (L^∨)^{⊗m}`;
   (4) the universal property of the relative Proj gives `τ : C̃ → Proj_C S = Y_κ^GG`, with line bundle `L^∨`. -/

/-- `W = (Tot(L) → C̃ → C)`, as a `C`-scheme. -/

noncomputable def BasedJet.totOver (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) :
    CategoryTheory.Over C.toScheme :=
  CategoryTheory.Over.mk ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫ ρ.hom)

/-- The `k`-structure of `Tot(L)`: the same one as in `relativeJetFunctor` (`W.hom ≫ (C ↘ Spec k)`); used only through
`letI`. -/

@[reducible] noncomputable def BasedJet.totOverField (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) :
    (BasedJet.totOver ρ L).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  ⟨(BasedJet.totOver ρ L).hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩

/-! ## The `ξ`-monomial and `ξ`-coefficient morphisms and their basic lemmas

The piece "`c ↦ c·ξ^q`" of the `q`-th component of `universalFrameAlg` and the piece "take the `m`-th `ξ`-coefficient"
of `weightComponent` get names of their own; the comparison theorems below are then three equations about these two
morphisms. The data agree literally with the original bodies (`frameHom_eq`, `symCoeffHom_eq` are `rfl`). -/

/-- `c ↦ c·ξ^n`: `(L^∨)^{⊗n} →(powIso)` tensor power `→(tensorPowerToSymPart) Sym^n →(totalIncl) ⊕ Sym
→(structureHom) p_*O_{Tot(L)}`. -/
noncomputable def BasedJet.frameHom (L : LineBundle ρ.source.toVariety) (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) n ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf) :=
  (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules) n).hom ≫
    AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules n ≫
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl n ≫
    AlgebraicGeometry.Scheme.relativeSpec.structureHom
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total

/-- Take the `m`-th `ξ`-coefficient: `p_*O_{Tot(L)} →(structureIso⁻¹) ⊕ Sym →(totalProj m) Sym^m
→(symPartToMonoidalPow) (L^∨)^{⊗m}`. -/
noncomputable def BasedJet.symCoeffHom (L : LineBundle ρ.source.toVariety) (m : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf) ⟶
      AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m :=
  (AlgebraicGeometry.Scheme.relativeSpec.structureIso
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).inv ≫
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalProj m ≫
    AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m

/-- On the weight-`0` piece, "`c ↦ c·ξ^0`" is the structure map `p^♯`: `(pieceIso 0).hom ≫ frameHom 0 = unitToPushforwardObjUnit p`.
    Proof: `pieceIso L 0 = Iso.refl`; `powIso_zero_comp_tensorPowerToSymPart_zero` (`χ_0 = S.one`, module `FrameHomMul`);
    `S.one ≫ totalIncl 0 = S.total.one` by definition; `relativeSpec.one_comp_structureHom_eq_unitToPushforwardObjUnit`.
    Used for the unit clause of `universalFrameAlg_isAlgebraMap` and for `jetConstantTerm_universalFrame`. -/
theorem BasedJet.pieceIso_zero_comp_frameHom_zero (L : LineBundle ρ.source.toVariety) :
    (truncatedJetAlgebra.pieceIso L 0).hom ≫ BasedJet.frameHom L 0 =
      SheafOfModules.unitToPushforwardObjUnit
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.toRingCatSheafHom := by
  -- the right-hand side of the statement is well-typed only after unfolding `totalSpace` (`rw` fails on such goals),
  -- so we use `have`s with explicit types and `Eq.trans` throughout
  have h1 : (truncatedJetAlgebra.pieceIso L 0).hom ≫ BasedJet.frameHom L 0 = BasedJet.frameHom L 0 :=
    CategoryTheory.Category.id_comp _
  have h2 : BasedJet.frameHom L 0 =
      ((AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules) 0).hom ≫
        AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules 0) ≫
      ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl 0 ≫
        AlgebraicGeometry.Scheme.relativeSpec.structureHom
          (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total) :=
    (CategoryTheory.Category.assoc _ _ _).symm
  have h3 : ((AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules) 0).hom ≫
        AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules 0) ≫
      ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl 0 ≫
        AlgebraicGeometry.Scheme.relativeSpec.structureHom
          (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total) =
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).one ≫
      ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl 0 ≫
        AlgebraicGeometry.Scheme.relativeSpec.structureHom
          (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total) :=
    congrArg (fun g => g ≫ ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl 0 ≫
        AlgebraicGeometry.Scheme.relativeSpec.structureHom
          (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total))
      (AlgebraicGeometry.Scheme.totalSpace.powIso_zero_comp_tensorPowerToSymPart_zero L.toModules)
  have h4 : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).one ≫
      ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl 0 ≫
        AlgebraicGeometry.Scheme.relativeSpec.structureHom
          (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total) =
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total.one ≫
        AlgebraicGeometry.Scheme.relativeSpec.structureHom
          (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total :=
    (CategoryTheory.Category.assoc _ _ _).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans
    (AlgebraicGeometry.Scheme.relativeSpec.one_comp_structureHom_eq_unitToPushforwardObjUnit
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total))))


/-- **Leaf.** On a line bundle, "tensor power → `Sym^q` → tensor power" is the inverse of `powIso`:
`tensorPowerToSymPart ≫ symPartToMonoidalPow = powIso⁻¹`.

    Proof: the bodies of both morphisms are `unfold symGradedAlgebra; split`; when `L^∨` is quasi-coherent (previous
    leaf; `L^∨` is a line bundle by `SheafOfModules.IsLineBundle.dual`) both land in the first branch,
    `tensorPowerToSymPart = powIso.inv ≫ symPowπ` and `symPartToMonoidalPow = inv symPowπ`, so the composite is
    `powIso.inv ≫ symPowπ ≫ inv symPowπ = powIso.inv` (`IsIso.hom_inv_id`).
    Technically: first `have hq := isQuasicoherent_of_isLineBundle (dual L)`, then
    `unfold totalSpace.tensorPowerToSymPart Modules.symPartToMonoidalPow` and enter the first branch with `split` (or
    `simp only [dif_pos hq]`); `symGradedAlgebra` is a `dite` and the type of `part q` depends on the branch, so if
    necessary `generalize`/`rw [dif_pos hq]` on the whole `symGradedAlgebra V`.
    Without quasi-coherence the trivial branch for `q ≥ 1` would compare `0 ≫ 0` and the equation would be false, so
    the previous leaf is necessary. -/
theorem AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart_symPartToMonoidalPow
    {Y : AlgebraicGeometry.Scheme.{u}} (N : Y.Modules) [N.IsLineBundle]
    [(AlgebraicGeometry.Scheme.Modules.dual N).IsLineBundle] (q : ℕ) :
    AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart N q ≫
        AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow (AlgebraicGeometry.Scheme.Modules.dual N) q =
      (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual N) q).inv := by
  -- both bodies take the quasi-coherent branch directly by `rw [dif_pos _]`; here the type-transport proof of the
  -- branch is abstracted into a variable and `symGradedAlgebra _ = symGradedAlgebraOfQC _ hq` is `subst`ituted.
  have hq : (AlgebraicGeometry.Scheme.Modules.dual N).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLineBundle _
  have casesOn_const : ∀ {P : Prop} {T : Type u} (d : Decidable P) (f : ¬P → T) (g : P → T) (hp : P),
      Decidable.casesOn (motive := fun _ => T) d f g = g hp := by
    intro P T d f g hp
    cases d with
    | isFalse h => exact absurd hp h
    | isTrue h => rfl
  unfold AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart
    AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow
  rw [CategoryTheory.Category.assoc]
  refine (congrArg (fun t => (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
    (AlgebraicGeometry.Scheme.Modules.dual N) q).inv ≫ t) ?_).trans (CategoryTheory.Category.comp_id _)
  generalize_proofs _ _ pf3 pf4 pf5 pf6
  have hS : AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual N) =
      AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC (AlgebraicGeometry.Scheme.Modules.dual N) hq := by
    delta AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
    exact dif_pos hq
  change (pf4 pf3).mpr (AlgebraicGeometry.Scheme.Modules.symPowπ (AlgebraicGeometry.Scheme.Modules.dual N) q) ≫
    (pf5 pf3).mpr (@CategoryTheory.inv _ _ _ _
      (AlgebraicGeometry.Scheme.Modules.symPowπ (AlgebraicGeometry.Scheme.Modules.dual N) q) (pf6 pf3)) = 𝟙 _
  generalize AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual N) = S
    at hS pf4 pf5 ⊢
  subst hS
  exact CategoryTheory.IsIso.hom_inv_id
    (AlgebraicGeometry.Scheme.Modules.symPowπ (AlgebraicGeometry.Scheme.Modules.dual N) q)

/-- Variable-level categorical lemma: four segments against three, the two middle pairs cancel. -/
theorem BasedJet.comp_cancel_aux {𝒞 : Type*} [CategoryTheory.Category 𝒞] {A B D E F B' : 𝒞}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) (d' : F ⟶ E) (e : E ⟶ D) (g : D ⟶ B') (a' : B ⟶ B')
    (h1 : d ≫ d' = CategoryTheory.CategoryStruct.id _) (h2 : c ≫ e = CategoryTheory.CategoryStruct.id _)
    (h3 : b ≫ g = a') : (a ≫ b ≫ c ≫ d) ≫ (d' ≫ e ≫ g) = a ≫ a' := by
  subst h3
  simp only [CategoryTheory.Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h2]

theorem BasedJet.comp_cancel_zero_aux {𝒞 : Type*} [CategoryTheory.Category 𝒞]
    [CategoryTheory.Limits.HasZeroMorphisms 𝒞] {A B D E F D' B' : 𝒞}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) (d' : F ⟶ E) (e : E ⟶ D') (g : D' ⟶ B')
    (h1 : d ≫ d' = CategoryTheory.CategoryStruct.id _) (h2 : c ≫ e = 0) :
    (a ≫ b ≫ c ≫ d) ≫ (d' ≫ e ≫ g) = 0 := by
  simp only [CategoryTheory.Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h2]
  simp

/-- The `m`-th `ξ`-coefficient of `ξ^m` is `1`: `frameHom m ≫ symCoeffHom m = 𝟙` (assembled from the previous leaf,
`totalIncl_totalProj` and `structureIso`). -/
theorem BasedJet.frameHom_symCoeffHom (L : LineBundle ρ.source.toVariety) (m : ℕ) :
    BasedJet.frameHom L m ≫ BasedJet.symCoeffHom L m = CategoryTheory.CategoryStruct.id _ :=
  (BasedJet.comp_cancel_aux _ _ _ _ _ _ _ _
    (AlgebraicGeometry.Scheme.relativeSpec.structureIso _).hom_inv_id
    (AlgebraicGeometry.Scheme.GradedQCAlgebra.totalIncl_totalProj
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)) m)
    (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart_symPartToMonoidalPow L.toModules m)).trans
    (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower _ m).hom_inv_id

/-- The `m`-th `ξ`-coefficient of `ξ^n` is `0` for `n ≠ m`. -/
theorem BasedJet.frameHom_symCoeffHom_of_ne (L : LineBundle ρ.source.toVariety) {n m : ℕ} (h : n ≠ m) :
    BasedJet.frameHom L n ≫ BasedJet.symCoeffHom L m = 0 :=
  BasedJet.comp_cancel_zero_aux _ _ _ _ _ _ _
    (AlgebraicGeometry.Scheme.relativeSpec.structureIso _).hom_inv_id
    ((CategoryTheory.Limits.Sigma.ι_desc _ _).trans (dif_neg h))


/-- The algebra map of the universal frame, `⊕_{q≤κ} (L^{-1})^{⊗q} → (pr ≫ p)_*O_{Tot ×_k D_κ}`: the `q`-th piece goes
    through `(L^{-1})^{⊗q} ≅ (L^∨)^{⊗q} → Sym^q(L^∨) → ⊕ Sym → p_*O_Tot` (i.e. `c ↦ c·ξ^q`) and is then multiplied by
    `t^q` in `p_*pr_*O` (`t` the parameter of the jet thickening). -/

noncomputable def BasedJet.universalFrameAlg (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) (κ : ℕ) :
    letI := BasedJet.totOverField ρ L
    (truncatedJetAlgebra L κ).carrier ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward
          (jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ≫
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom)).obj
        (SheafOfModules.unit (jetThickening (k := k) κ (BasedJet.totOver ρ L).left).ringCatSheaf) :=
  letI := BasedJet.totOverField ρ L
  let Tot := AlgebraicGeometry.Scheme.totalSpace L.toModules
  let pr := jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left
  let t := jetThickening.parameter (k := k) κ (BasedJet.totOver ρ L).left
  let D := AlgebraicGeometry.Scheme.Modules.dual L.toModules
  let S := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra D
  show CategoryTheory.Limits.biproduct (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) ⟶ _ from
    CategoryTheory.Limits.biproduct.desc fun q : Fin (κ + 1) =>
      (truncatedJetAlgebra.pieceIso L q).hom ≫
        (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower D q).hom ≫
        AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules q ≫
        S.totalIncl q ≫
        AlgebraicGeometry.Scheme.relativeSpec.structureHom S.total ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward Tot.hom).map
          (SheafOfModules.unitToPushforwardObjUnit pr.toRingCatSheafHom ≫
            (AlgebraicGeometry.Scheme.Modules.pushforward pr).map
              (AlgebraicGeometry.Scheme.Modules.unitMul (t ^ (q : ℕ)))) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardComp pr Tot.hom).hom.app _

/-- The `t^n`-coefficient of a finite sum: the coefficient of order `n` of `Σ_q pr^♯(a_q)·t^q` is `a_n` (`coeff_add` +
`coeff_proj_mul_parameter_pow`). -/
theorem jetThickening.coeff_sum_proj_mul_parameter_pow {k : Type u} [Field k] (r : ℕ)
    (W : AlgebraicGeometry.Scheme.{u}) [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (V : W.Opens)
    (n : ℕ) (hn : n ≤ r) (a : Fin (r + 1) → Γ(W, V)) :
    jetThickening.coeff (k := k) r W V n hn
        (∑ q : Fin (r + 1), ((jetThickeningProj (k := k) r W).app V).hom (a q) *
          (((jetThickening (k := k) r W).presheaf.map (homOfLE le_top).op).hom
            (jetThickening.parameter (k := k) r W)) ^ (q : ℕ)) =
      a ⟨n, Nat.lt_succ_of_le hn⟩ := by
  have h0 : jetThickening.coeff (k := k) r W V n hn 0 = 0 := by
    have h := jetThickening.coeff_add (k := k) r W V n hn 0 0
    rw [add_zero] at h
    exact (add_eq_left.mp h.symm)
  have hsum : ∀ (s : Finset (Fin (r + 1)))
      (g : Fin (r + 1) → Γ(jetThickening (k := k) r W, jetThickeningProj (k := k) r W ⁻¹ᵁ V)),
      jetThickening.coeff (k := k) r W V n hn (∑ q ∈ s, g q) =
        ∑ q ∈ s, jetThickening.coeff (k := k) r W V n hn (g q) := by
    intro s g
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, jetThickening.coeff_add, ih]
  rw [hsum]
  simp only [jetThickening.coeff_proj_mul_parameter_pow]
  rw [Finset.sum_eq_single ⟨n, Nat.lt_succ_of_le hn⟩]
  · simp
  · intro q _ hq
    rw [if_neg]
    intro h
    exact hq (Fin.ext h.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h


/-- **Leaf.** The algebra map of the universal frame on the `q`-th piece: `c ∈ (L^{-1})^{⊗q}(V) ↦ pr^♯(c·ξ^q)·t^q`,
    where `c·ξ^q = frameHom q (pieceIso c) ∈ Γ(Tot(L), p⁻¹V)`.

    Proof: `universalFrameAlg = biproduct.desc (fun q => …)`, so by `biproduct.ι_desc` the `q`-th component is
    `pieceIso.hom ≫ powIso.hom ≫ tensorPowerToSymPart ≫ totalIncl q ≫ structureHom ≫ p_*(unitTo… ≫ pr_*(unitMul (t^q))) ≫ pushforwardComp.hom`;
    the first five segments are `pieceIso.hom ≫ frameHom L q` (definition of `frameHom`, `rfl`). The last two on
    sections: `unitToPushforwardObjUnit pr.toRingCatSheafHom` on `p⁻¹V` is `pr.app (p⁻¹V)`; `unitMul (t^q)` on an open
    `O` is multiplication by `(t^q)|_O`; `pushforwardComp.hom.app` is the identity on sections. Restriction commutes
    with powers (`map_pow`). -/
theorem BasedJet.universalFrameAlg_app_ι (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) (κ : ℕ)
    (V : ρ.source.toScheme.Opens) (q : Fin (κ + 1))
    (c : ((truncatedJetAlgebra.piece L q).val.obj (Opposite.op V) : Type u)) :
    letI := BasedJet.totOverField ρ L
    (show Γ(jetThickening (k := k) κ (BasedJet.totOver ρ L).left,
        jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ⁻¹ᵁ
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)) from
      ((BasedJet.universalFrameAlg ρ L κ).val.app (Opposite.op V)).hom
        (((CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).val.app
          (Opposite.op V)).hom c)) =
    ((jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left).app
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)).hom
      (show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) from
        ((BasedJet.frameHom L q).val.app (Opposite.op V)).hom
          (((truncatedJetAlgebra.pieceIso L q).hom.val.app (Opposite.op V)).hom c)) *
      (((jetThickening (k := k) κ (BasedJet.totOver ρ L).left).presheaf.map (homOfLE le_top).op).hom
        (jetThickening.parameter (k := k) κ (BasedJet.totOver ρ L).left)) ^ (q : ℕ) := by
  letI := BasedJet.totOverField ρ L
  change ((CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q ≫
    BasedJet.universalFrameAlg ρ L κ).val.app (Opposite.op V)).hom c = _
  unfold BasedJet.universalFrameAlg
  rw [CategoryTheory.Limits.biproduct.ι_desc]
  show ((jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left).app
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)).hom
      (((BasedJet.frameHom L q).val.app (Opposite.op V)).hom
          (((truncatedJetAlgebra.pieceIso L q).hom.val.app (Opposite.op V)).hom c)) *
      (((jetThickening (k := k) κ (BasedJet.totOver ρ L).left).presheaf.map (homOfLE le_top).op).hom
        (jetThickening.parameter (k := k) κ (BasedJet.totOver ρ L).left ^ (q : ℕ))) = _
  rw [map_pow]

/-- The `ℕ`-indexed form of `universalFrameAlg_app_ι` (`n ≤ κ`), avoiding the spelling difference between
`Fin.val ⟨n, _⟩` and `n`. -/
theorem BasedJet.universalFrameAlg_app_ι' (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) (κ : ℕ)
    (V : ρ.source.toScheme.Opens) (n : ℕ) (hn : n ≤ κ)
    (c : ((truncatedJetAlgebra.piece L n).val.obj (Opposite.op V) : Type u)) :
    letI := BasedJet.totOverField ρ L
    (show Γ(jetThickening (k := k) κ (BasedJet.totOver ρ L).left,
        jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ⁻¹ᵁ
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)) from
      ((BasedJet.universalFrameAlg ρ L κ).val.app (Opposite.op V)).hom
        (((CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨n, Nat.lt_succ_of_le hn⟩).val.app (Opposite.op V)).hom c)) =
    ((jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left).app
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)).hom
      (show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) from
        ((BasedJet.frameHom L n).val.app (Opposite.op V)).hom
          (((truncatedJetAlgebra.pieceIso L n).hom.val.app (Opposite.op V)).hom c)) *
      (((jetThickening (k := k) κ (BasedJet.totOver ρ L).left).presheaf.map (homOfLE le_top).op).hom
        (jetThickening.parameter (k := k) κ (BasedJet.totOver ρ L).left)) ^ n :=
  BasedJet.universalFrameAlg_app_ι ρ L κ V ⟨n, Nat.lt_succ_of_le hn⟩ c

/-- The `t^n`-coefficient of the algebra map of the universal frame, for an arbitrary section `c ∈ (⊕_{q≤κ} L^{-q})(V)`:
    `coeff_n(Φ c) = (π_n c)·ξ^n`. `biproduct_section_eq_sum` writes `c = Σ ι_q(π_q c)`, `universalFrameAlg_app_ι`
    handles each term, and `coeff_sum_proj_mul_parameter_pow` takes the coefficient. Shared by `universalFrame_coeff`
    and `jetConstantTerm_universalFrame`. -/
theorem BasedJet.universalFrameAlg_coeff (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) (κ : ℕ)
    (V : ρ.source.toScheme.Opens) (n : ℕ) (hn : n ≤ κ)
    (c : ((truncatedJetAlgebra L κ).carrier.val.obj (Opposite.op V) : Type u)) :
    letI := BasedJet.totOverField ρ L
    jetThickening.coeff (k := k) κ (BasedJet.totOver ρ L).left
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) n hn
        (((BasedJet.universalFrameAlg ρ L κ).val.app (Opposite.op V)).hom c) =
      ((BasedJet.frameHom L n).val.app (Opposite.op V)).hom
        (((truncatedJetAlgebra.pieceIso L n).hom.val.app (Opposite.op V)).hom
          (((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
            ⟨n, Nat.lt_succ_of_le hn⟩).val.app (Opposite.op V)).hom c)) := by
  letI := BasedJet.totOverField ρ L
  have happ : ∀ (q : Fin (κ + 1)) (d : ((truncatedJetAlgebra.piece L q).val.obj (Opposite.op V) : Type u)),
      ((BasedJet.universalFrameAlg ρ L κ).val.app (Opposite.op V)).hom
        (((CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).val.app
          (Opposite.op V)).hom d) =
      ((jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left).app
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)).hom
        (((BasedJet.frameHom L q).val.app (Opposite.op V)).hom
          (((truncatedJetAlgebra.pieceIso L q).hom.val.app (Opposite.op V)).hom d)) *
        (((jetThickening (k := k) κ (BasedJet.totOver ρ L).left).presheaf.map (homOfLE le_top).op).hom
          (jetThickening.parameter (k := k) κ (BasedJet.totOver ρ L).left)) ^ (q : ℕ) :=
    fun q d => BasedJet.universalFrameAlg_app_ι ρ L κ V q d
  have hsum := map_sum ((BasedJet.universalFrameAlg ρ L κ).val.app (Opposite.op V)).hom
    (fun q : Fin (κ + 1) =>
      ((CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).val.app
        (Opposite.op V)).hom
      (((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).val.app
        (Opposite.op V)).hom c)) Finset.univ
  conv_lhs => rw [AlgebraicGeometry.Scheme.Modules.biproduct_section_eq_sum
    (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) V c]
  erw [hsum]
  erw [Finset.sum_congr rfl (fun q _ => happ q
    (((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).val.app
      (Opposite.op V)).hom c))]
  exact jetThickening.coeff_sum_proj_mul_parameter_pow (k := k) κ (BasedJet.totOver ρ L).left
    ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) n hn (fun q : Fin (κ + 1) =>
      ((BasedJet.frameHom L q).val.app (Opposite.op V)).hom
        (((truncatedJetAlgebra.pieceIso L q).hom.val.app (Opposite.op V)).hom
          (((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).val.app
            (Opposite.op V)).hom c)))

/-! ### The three leaves of `universalFrameAlg_isAlgebraMap` -/

/-- **Leaf.** `c ↦ c·ξ^n` is multiplicative: for `a ∈ (L^{-1})^{⊗p}(V)` and `b ∈ (L^{-1})^{⊗q}(V)`,
`(a·b)ξ^{p+q} = (aξ^p)(bξ^q)` in `Γ(Tot(L), p⁻¹V)`.

    Proof in three steps:
    (i) `pieceIso` is compatible with concatenation:
        `pieceMul L p q ≫ (pieceIso (p+q)).hom = ((pieceIso p).hom ⊗ₘ (pieceIso q).hom) ≫ (monoidalPowCat D p q).hom`
        (`truncatedJetAlgebra.pieceIso_mul`; both sides are defined by recursion on `q`, the induction step being the
        naturality of the associator);
    (ii) the first two segments of `frameHom`, `powIso.hom ≫ tensorPowerToSymPart = symPowπ` (quasi-coherent branch),
        and the multiplication `symPowMul` of `Sym` satisfies
        `(symPowπ p ⊗ₘ symPowπ q) ≫ symPowMul p q = (monoidalPowCat D p q).hom ≫ symPowπ (p+q)`
        (`tensorHom_symPowπ_symPowMul` / `Modules.mul_comp_symPartToMonoidalPow`);
    (iii) the multiplication of `⊕ Sym` on components is `S.mul` (component formula of `totalMul`), and `structureHom`
        is an algebra map (`structureHom_isAlgebraMap_jnl`).
    The morphism-level assembly of the three steps is `pieceMul_comp_frameHomCore` (module
    `JetWeightComponentEqCoefficientFrameHomMul`); the translation to sections is
    `IsAlgebraMapToPushforward.app_mul_of_comp_eq` together with the naturality of `tensorSections` with respect to
    `tensorHom`.
    Edge cases: for `p = 0` or `q = 0` this is the unit law; no `n!` appears, so the characteristic plays no role. -/
theorem BasedJet.frameHom_pieceMul (L : LineBundle ρ.source.toVariety) (p q : ℕ)
    (V : ρ.source.toScheme.Opens)
    (a : ((truncatedJetAlgebra.piece L p).val.obj (Opposite.op V) : Type u))
    (b : ((truncatedJetAlgebra.piece L q).val.obj (Opposite.op V) : Type u)) :
    (show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) from
      (((truncatedJetAlgebra.pieceIso L (p + q)).hom ≫ BasedJet.frameHom L (p + q)).val.app (Opposite.op V)).hom
        (((truncatedJetAlgebra.pieceMul L p q).val.app (Opposite.op V)).hom
          (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V a b))) =
    (show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) from
      (((truncatedJetAlgebra.pieceIso L p).hom ≫ BasedJet.frameHom L p).val.app (Opposite.op V)).hom a) *
    (show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) from
      (((truncatedJetAlgebra.pieceIso L q).hom ≫ BasedJet.frameHom L q).val.app (Opposite.op V)).hom b) := by
  -- morphism level: `pieceMul_comp_frameHomCore` (module `FrameHomMul`: `pieceIso_mul` + compatibility of the
  -- multiplication of `Sym` with `χ` + component formula of `totalMul`); section level: `structureHom` is an algebra
  -- map (`structureHom_isAlgebraMap_jnl`), translated once by the variable-level lemma
  -- `IsAlgebraMapToPushforward.app_mul_of_comp_eq`.
  have hcore := truncatedJetAlgebra.pieceMul_comp_frameHomCore L p q
  refine AlgebraicGeometry.Scheme.QCAlgebra.IsAlgebraMapToPushforward.app_mul_of_comp_eq
    (AlgebraicGeometry.Scheme.relativeSpec.structureHom_isAlgebraMap_jnl
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total)
    (truncatedJetAlgebra.pieceMul L p q)
    ((truncatedJetAlgebra.pieceIso L (p + q)).hom ≫ BasedJet.frameHom L (p + q))
    ((truncatedJetAlgebra.pieceIso L p).hom ≫
      (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules) p).hom ≫
      AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules p ≫
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl p)
    ((truncatedJetAlgebra.pieceIso L q).hom ≫
      (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q).hom ≫
      AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules q ≫
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl q)
    ((truncatedJetAlgebra.pieceIso L p).hom ≫ BasedJet.frameHom L p)
    ((truncatedJetAlgebra.pieceIso L q).hom ≫ BasedJet.frameHom L q) ?_ ?_ ?_ V a b
  · unfold BasedJet.frameHom
    conv_rhs => rw [← CategoryTheory.Category.assoc]
    rw [← hcore]
    simp only [CategoryTheory.Category.assoc]
    rfl
  · unfold BasedJet.frameHom
    simp only [CategoryTheory.Category.assoc]
    rfl
  · unfold BasedJet.frameHom
    simp only [CategoryTheory.Category.assoc]
    rfl

/-- **Leaf.** The multiplication of the truncated algebra on two pieces: `ι_p(a)·ι_q(b) = ι_{p+q}(a·b)` if `p+q ≤ κ`,
and `0` otherwise.

    Proof: the morphism-level formula `truncatedJetAlgebra.ι_tensor_ι_comp_mulHom` gives `(ι_p ⊗ₘ ι_q) ≫ mulHom`; take
    sections over `V` applied to `tensorSections a b`, use `tensorHom_tensorSections`, and both sides agree after
    `split_ifs` by `rfl`. (Directly: `mulHom = Σ_{a',b'} [a'+b' ≤ κ] (π_{a'} ⊗ₘ π_{b'}) ≫ pieceMul ≫ ι_{a'+b'}`;
    `tensorSections` is natural with respect to `tensorHom`, `biproduct.ι_π` and the bilinearity of `tensorSections`
    leave only the term `(a', b') = (p, q)`.)
    Edge case: for `κ = 0` only `p = q = 0` occurs. -/
theorem truncatedJetAlgebra.mulHom_app_ι {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ : ℕ) (V : Ct.toScheme.Opens) (p q : Fin (κ + 1))
    (a : ((truncatedJetAlgebra.piece L p).val.obj (Opposite.op V) : Type u))
    (b : ((truncatedJetAlgebra.piece L q).val.obj (Opposite.op V) : Type u)) :
    ((truncatedJetAlgebra.mulHom L κ).val.app (Opposite.op V)).hom
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V
          (((CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) p).val.app
            (Opposite.op V)).hom a)
          (((CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).val.app
            (Opposite.op V)).hom b)) =
      if h : (p : ℕ) + (q : ℕ) ≤ κ then
        ((CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
            ⟨(p : ℕ) + (q : ℕ), Nat.lt_succ_of_le h⟩).val.app (Opposite.op V)).hom
          (((truncatedJetAlgebra.pieceMul L p q).val.app (Opposite.op V)).hom
            (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V a b))
      else 0 := by
  have h := congrArg (fun φ => (φ.val.app (Opposite.op V)).hom
      (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V a b))
    (truncatedJetAlgebra.ι_tensor_ι_comp_mulHom (L := L) κ (p : ℕ) (q : ℕ) p.2 q.2)
  rw [← AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections]
  refine h.trans ?_
  split_ifs with hpq
  · rfl
  · rfl

/-- The algebra map of the universal frame on a product of two pieces (the componentwise case of the multiplication
    clause of `universalFrameAlg_isAlgebraMap`): `Φ(ι_p a · ι_q b) = Φ(ι_p a)·Φ(ι_q b)`. For `p+q ≤ κ`: `mulHom_app_ι`
    gives `ι_{p+q}(a·b)`, `universalFrameAlg_app_ι'` gives `pr^♯((a·b)ξ^{p+q})·t^{p+q}`, `frameHom_pieceMul` gives
    `(a·b)ξ^{p+q} = aξ^p·bξ^q`, then `map_mul` and `pow_add`. For `p+q > κ`: the left side is `Φ(0) = 0`, and the right
    side contains `t^{p+q}` with `t^{κ+1} = 0` (`parameter_pow_succ`). -/
theorem BasedJet.universalFrameAlg_app_ι_mul (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) (κ : ℕ)
    (V : ρ.source.toScheme.Opens) (p q : Fin (κ + 1))
    (a : ((truncatedJetAlgebra.piece L p).val.obj (Opposite.op V) : Type u))
    (b : ((truncatedJetAlgebra.piece L q).val.obj (Opposite.op V) : Type u)) :
    letI := BasedJet.totOverField ρ L
    (show Γ(jetThickening (k := k) κ (BasedJet.totOver ρ L).left,
        jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ⁻¹ᵁ
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)) from
      ((BasedJet.universalFrameAlg ρ L κ).val.app (Opposite.op V)).hom
        (((truncatedJetAlgebra.mulHom L κ).val.app (Opposite.op V)).hom
          (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V
            (((CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) p).val.app
              (Opposite.op V)).hom a)
            (((CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).val.app
              (Opposite.op V)).hom b)))) =
    (show Γ(jetThickening (k := k) κ (BasedJet.totOver ρ L).left,
        jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ⁻¹ᵁ
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)) from
      ((BasedJet.universalFrameAlg ρ L κ).val.app (Opposite.op V)).hom
        (((CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) p).val.app
          (Opposite.op V)).hom a)) *
    (show Γ(jetThickening (k := k) κ (BasedJet.totOver ρ L).left,
        jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ⁻¹ᵁ
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)) from
      ((BasedJet.universalFrameAlg ρ L κ).val.app (Opposite.op V)).hom
        (((CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).val.app
          (Opposite.op V)).hom b)) := by
  letI := BasedJet.totOverField ρ L
  rw [truncatedJetAlgebra.mulHom_app_ι, BasedJet.universalFrameAlg_app_ι, BasedJet.universalFrameAlg_app_ι]
  split_ifs with hpq
  · rw [BasedJet.universalFrameAlg_app_ι' ρ L κ V ((p : ℕ) + (q : ℕ)) hpq]
    have hf : (show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) from
        ((BasedJet.frameHom L ((p : ℕ) + (q : ℕ))).val.app (Opposite.op V)).hom
          (((truncatedJetAlgebra.pieceIso L ((p : ℕ) + (q : ℕ))).hom.val.app (Opposite.op V)).hom
            (((truncatedJetAlgebra.pieceMul L p q).val.app (Opposite.op V)).hom
              (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V a b)))) =
        (show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) from
          ((BasedJet.frameHom L p).val.app (Opposite.op V)).hom
            (((truncatedJetAlgebra.pieceIso L p).hom.val.app (Opposite.op V)).hom a)) *
        (show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) from
          ((BasedJet.frameHom L q).val.app (Opposite.op V)).hom
            (((truncatedJetAlgebra.pieceIso L q).hom.val.app (Opposite.op V)).hom b)) :=
      BasedJet.frameHom_pieceMul L p q V a b
    rw [hf]
    erw [map_mul]
    rw [pow_add]
    ring
  · have ht : (((jetThickening (k := k) κ (BasedJet.totOver ρ L).left).presheaf.map
        (homOfLE (le_top : jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ⁻¹ᵁ
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) ≤ ⊤)).op).hom
        (jetThickening.parameter (k := k) κ (BasedJet.totOver ρ L).left)) ^ ((p : ℕ) + (q : ℕ)) = 0 := by
      refine pow_eq_zero_of_le (show κ + 1 ≤ (p : ℕ) + (q : ℕ) by omega) ?_
      erw [← map_pow]
      rw [jetThickening.parameter_pow_succ, map_zero]
    erw [map_zero]
    rw [mul_mul_mul_comm, ← pow_add, ht, mul_zero]
    rfl

/-- **Leaf (assembly).** `universalFrameAlg` is an algebra map.

    Proof (`IsAlgebraMapToPushforward` consists of two conditions on each open `V`).
    Multiplication: for `x, y ∈ (⊕_{q≤κ} piece q)(V)`, write `x = Σ_p ι_p(x_p)`, `y = Σ_q ι_q(y_q)` by
    `biproduct_section_eq_sum`; by bilinearity of `tensorSections` and additivity of both maps it suffices to treat
    `x = ι_p(a)`, `y = ι_q(b)`, which is `universalFrameAlg_app_ι_mul` (the reduction is the variable-level lemma
    `Modules.isAlgebraMap_mul_of_pieces` of module `FrameHomMul`).
    Unit: `1 = ι_0(1)` (`oneHom = biproduct.ι 0`), `universalFrameAlg_app_ι'` (with `n = 0`) gives `pr^♯(1·ξ^0)·t^0`, and
    `frameHom L 0` sends `1` to `1` (`pieceIso_zero_comp_frameHom_zero`).
    Edge case: for `κ = 0` there is only the term `p = q = 0`. -/
theorem BasedJet.universalFrameAlg_isAlgebraMap (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) (κ : ℕ) :
    letI := BasedJet.totOverField ρ L
    (truncatedJetAlgebra L κ).IsAlgebraMapToPushforward
      (jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ≫
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom)
      (BasedJet.universalFrameAlg ρ L κ) := by
  -- multiplication: `isAlgebraMap_mul_of_pieces` (module `FrameHomMul`, componentwise decomposition of biproduct
  -- sections) reduces to `universalFrameAlg_app_ι_mul`; unit: `oneHom = ι_0`, `universalFrameAlg_app_ι'` (`n = 0`)
  -- and `pieceIso_zero_comp_frameHom_zero`.
  letI := BasedJet.totOverField ρ L
  constructor
  · intro V x y
    exact AlgebraicGeometry.Scheme.Modules.isAlgebraMap_mul_of_pieces
      (jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ≫
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom)
      (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) (truncatedJetAlgebra.mulHom L κ)
      (BasedJet.universalFrameAlg ρ L κ) V (fun p q a b => BasedJet.universalFrameAlg_app_ι_mul ρ L κ V p q a b) x y
  · intro V
    have h0 := BasedJet.universalFrameAlg_app_ι' ρ L κ V 0 (Nat.zero_le κ) (show Γ(ρ.source.toScheme, V) from 1)
    have h1 := congrArg (fun φ => (φ.val.app (Opposite.op V)).hom (show Γ(ρ.source.toScheme, V) from 1))
      (BasedJet.pieceIso_zero_comp_frameHom_zero L)
    refine h0.trans ?_
    rw [pow_zero, mul_one]
    refine (congrArg ((jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left).app
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)).hom h1).trans ?_
    show ((jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left).app
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)).hom
      (((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.app V).hom (1 : Γ(ρ.source.toScheme, V))) = 1
    exact (congrArg ((jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left).app
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)).hom
      (map_one ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.app V).hom)).trans (map_one _)

/-- The universal frame `u : Tot(L) ×_k D_κ → C̃_(κ)(L)` (a morphism over `C̃`); the algebra-map compatibility is
`universalFrameAlg_isAlgebraMap`. -/

noncomputable def BasedJet.universalFrame (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) (κ : ℕ) :
    letI := BasedJet.totOverField ρ L
    jetThickening (k := k) κ (BasedJet.totOver ρ L).left ⟶ (jetNeighborhood L κ).left :=
  letI := BasedJet.totOverField ρ L
  ((AlgebraicGeometry.Scheme.relativeSpecHomEquiv (truncatedJetAlgebra L κ)
      (CategoryTheory.Over.mk (jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ≫
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom))).symm
    ⟨BasedJet.universalFrameAlg ρ L κ, BasedJet.universalFrameAlg_isAlgebraMap ρ L κ⟩).left

/-- `u` is a morphism over `C̃`: `u ≫ p_κ = pr ≫ p` (`relativeSpecHomEquiv.symm` produces an `Over` morphism; `Over.w`). -/
theorem BasedJet.universalFrame_proj (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) (κ : ℕ) :
    letI := BasedJet.totOverField ρ L
    BasedJet.universalFrame ρ L κ ≫ jetNeighborhood.proj L κ =
      jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ≫
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom :=
  letI := BasedJet.totOverField ρ L
  CategoryTheory.Over.w ((AlgebraicGeometry.Scheme.relativeSpecHomEquiv (truncatedJetAlgebra L κ)
      (CategoryTheory.Over.mk (jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ≫
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom))).symm
    ⟨BasedJet.universalFrameAlg ρ L κ, BasedJet.universalFrameAlg_isAlgebraMap ρ L κ⟩)

/-- The value of the constant-term section `ι₀` followed by the universal frame `u` on `σ(c)`:
    `(ι₀ ≫ u)^♯(σ c) = p^♯(π₀ c)` (`appLE_comp_appLE`, `ofAlgebraMap_appLE_structureHom`,
    `jetConstantTerm_appLE_eq_coeff_zero`, `universalFrameAlg_coeff` with `n = 0`, `pieceIso_zero_comp_frameHom_zero`). -/
theorem BasedJet.jetConstantTerm_universalFrame_appLE (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety)
    (κ : ℕ) (V : ρ.source.toScheme.Opens) (c : ((truncatedJetAlgebra L κ).carrier.val.obj (Opposite.op V) : Type u)) :
    letI := BasedJet.totOverField ρ L
    ∀ e : (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V ≤
      (jetConstantTerm (k := k) κ (BasedJet.totOver ρ L).left ≫ BasedJet.universalFrame ρ L κ) ⁻¹ᵁ
        ((jetNeighborhood L κ).hom ⁻¹ᵁ V),
    ((jetConstantTerm (k := k) κ (BasedJet.totOver ρ L).left ≫ BasedJet.universalFrame ρ L κ).appLE
        ((jetNeighborhood L κ).hom ⁻¹ᵁ V) ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) e).hom
      ((AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ)).app V c) =
    ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.app V).hom
      (((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨0, Nat.succ_pos κ⟩).val.app (Opposite.op V)).hom c) := by
  letI := BasedJet.totOverField ρ L
  intro e
  have e₃ : jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ⁻¹ᵁ
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) ≤
      BasedJet.universalFrame ρ L κ ⁻¹ᵁ ((jetNeighborhood L κ).hom ⁻¹ᵁ V) := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, BasedJet.universalFrame_proj]
    exact le_of_eq (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).symm
  have hB := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE (jetConstantTerm (k := k) κ (BasedJet.totOver ρ L).left)
    (BasedJet.universalFrame ρ L κ) ((jetNeighborhood L κ).hom ⁻¹ᵁ V)
    (jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ⁻¹ᵁ
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V))
    ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) e₃
    (jetConstantTerm_le (k := k) κ (BasedJet.totOver ρ L).left
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V))
  have hC := AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap_appLE_structureHom (truncatedJetAlgebra L κ)
    (CategoryTheory.Over.mk (jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ≫
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom))
    (BasedJet.universalFrameAlg ρ L κ) (BasedJet.universalFrameAlg_isAlgebraMap ρ L κ) V c e₃
  have hD := jetConstantTerm_appLE_eq_coeff_zero (k := k) κ (BasedJet.totOver ρ L).left
    ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)
    (((BasedJet.universalFrameAlg ρ L κ).val.app (Opposite.op V)).hom c)
  have hE := BasedJet.universalFrameAlg_coeff ρ L κ V 0 (Nat.zero_le κ) c
  have hF := congrArg (fun φ => (φ.val.app (Opposite.op V)).hom
      (((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨0, Nat.succ_pos κ⟩).val.app (Opposite.op V)).hom c))
    (BasedJet.pieceIso_zero_comp_frameHom_zero L)
  refine (congrArg (fun ψ => ψ.hom
    ((AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ)).app V c)) hB.symm).trans ?_
  refine (congrArg ((jetConstantTerm (k := k) κ (BasedJet.totOver ρ L).left).appLE _ _
    (jetConstantTerm_le (k := k) κ (BasedJet.totOver ρ L).left
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V))).hom hC).trans ?_
  refine hD.trans ?_
  refine hE.trans ?_
  exact hF

/-- The value of "`p` followed by the zero section" on `σ(c)`: `(p ≫ 0_κ)^♯(σ c) = p^♯(π₀ c)` (`appLE_comp_appLE`,
    the zero section is `ofAlgebraMap … augmentation` so `ofAlgebraMap_appLE_structureHom` applies, and
    `augmentation = π₀ ≫ (𝟙_*)⁻¹` is `π₀` on sections). -/
theorem BasedJet.totalSpace_zeroSection_appLE_structureHom (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety)
    (κ : ℕ) (V : ρ.source.toScheme.Opens) (c : ((truncatedJetAlgebra L κ).carrier.val.obj (Opposite.op V) : Type u)) :
    ∀ e : (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V ≤
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫ jetNeighborhood.zeroSection L κ) ⁻¹ᵁ
        ((jetNeighborhood L κ).hom ⁻¹ᵁ V),
    (((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫ jetNeighborhood.zeroSection L κ).appLE
        ((jetNeighborhood L κ).hom ⁻¹ᵁ V) ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) e).hom
      ((AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ)).app V c) =
    ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.app V).hom
      (((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨0, Nat.succ_pos κ⟩).val.app (Opposite.op V)).hom c) := by
  intro e
  have e₅ : (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id ρ.source.toScheme)).hom ⁻¹ᵁ V ≤
      jetNeighborhood.zeroSection L κ ⁻¹ᵁ ((jetNeighborhood L κ).hom ⁻¹ᵁ V) :=
    le_of_eq (by
      show (CategoryTheory.CategoryStruct.id ρ.source.toScheme) ⁻¹ᵁ V = _
      rw [← jetNeighborhood.zeroSection_proj L κ]; rfl)
  have e₆ : (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V ≤
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ
        ((CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id ρ.source.toScheme)).hom ⁻¹ᵁ V) := le_rfl
  have hB := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
    (jetNeighborhood.zeroSection L κ) ((jetNeighborhood L κ).hom ⁻¹ᵁ V)
    ((CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id ρ.source.toScheme)).hom ⁻¹ᵁ V)
    ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) e₅ e₆
  have hD := AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap_appLE_structureHom (truncatedJetAlgebra L κ)
    (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id ρ.source.toScheme))
    (jetNeighborhood.augmentation L κ) (jetNeighborhood.augmentation_isAlgebraMap L κ) V c e₅
  refine (congrArg (fun ψ => ψ.hom
    ((AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ)).app V c)) hB.symm).trans ?_
  refine (congrArg ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.appLE
    ((CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id ρ.source.toScheme)).hom ⁻¹ᵁ V)
    ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) e₆).hom hD).trans ?_
  exact congrArg (fun ψ => ψ.hom ((jetNeighborhood.augmentation L κ).app V c))
    (AlgebraicGeometry.Scheme.Hom.app_eq_appLE (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).symm

/-- **Leaf.** At `t = 0` the universal frame is "`p` followed by the zero section": `ι₀ ≫ u = p ≫ 0_κ`
(`Tot(L) → C̃ → C̃_(κ)(L)`).

    Proof: both sides are `C̃`-morphisms `Tot(L) → Spec_{C̃}(⊕_{q≤κ} L^{-q})` (the left one by `universalFrame_proj` and
    `jetConstantTerm_proj : ι₀ ≫ pr = 𝟙`, the right one by `zeroSection_proj`), so by injectivity of
    `relativeSpecHomEquiv` it suffices to compare the corresponding algebra maps `⊕ L^{-q} → p_*O_Tot`, i.e. their
    values on `σ(c)` for every open `V` and section `c`. These are computed by the two preceding lemmas
    (`jetConstantTerm_universalFrame_appLE`, through the `t^0`-coefficient, and
    `totalSpace_zeroSection_appLE_structureHom`) and both equal `p^♯(π₀ c)`: the `q`-th component of
    `universalFrameAlg` followed by `ι₀^♯` contains the factor `ι₀^♯(t^q)`, which is `0` for `q ≥ 1`
    (`jetConstantTerm_parameter`), while the zero section corresponds to the projection `π_0`.
    Edge case: for `κ = 0`, `u` itself is `p` followed by the zero section (`D_0 = Spec k`). -/
theorem BasedJet.jetConstantTerm_universalFrame (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) (κ : ℕ) :
    letI := BasedJet.totOverField ρ L
    jetConstantTerm (k := k) κ (BasedJet.totOver ρ L).left ≫ BasedJet.universalFrame ρ L κ =
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫ jetNeighborhood.zeroSection L κ := by
  -- both sides are `C̃`-morphisms `Tot(L) → Spec_{C̃}(⊕ L^{-q})`; compare the algebra maps by injectivity of
  -- `relativeSpecHomEquiv`; for each open `V` and section `c`, the values on `σ(c)` are computed by
  -- `jetConstantTerm_universalFrame_appLE` (through the `t^0`-coefficient) and
  -- `totalSpace_zeroSection_appLE_structureHom`, and both equal `p^♯(π₀ c)`.
  letI := BasedJet.totOverField ρ L
  have hw₁ : (jetConstantTerm (k := k) κ (BasedJet.totOver ρ L).left ≫ BasedJet.universalFrame ρ L κ) ≫
      (jetNeighborhood L κ).hom =
      (CategoryTheory.Over.mk (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).hom := by
    have s1 : (jetConstantTerm (k := k) κ (BasedJet.totOver ρ L).left ≫ BasedJet.universalFrame ρ L κ) ≫
        (jetNeighborhood L κ).hom =
        jetConstantTerm (k := k) κ (BasedJet.totOver ρ L).left ≫
          (BasedJet.universalFrame ρ L κ ≫ jetNeighborhood.proj L κ) := CategoryTheory.Category.assoc _ _ _
    have s2 : jetConstantTerm (k := k) κ (BasedJet.totOver ρ L).left ≫
          (BasedJet.universalFrame ρ L κ ≫ jetNeighborhood.proj L κ) =
        jetConstantTerm (k := k) κ (BasedJet.totOver ρ L).left ≫
          (jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ≫
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom) :=
      congrArg (fun g => jetConstantTerm (k := k) κ (BasedJet.totOver ρ L).left ≫ g)
        (BasedJet.universalFrame_proj ρ L κ)
    have s3 : jetConstantTerm (k := k) κ (BasedJet.totOver ρ L).left ≫
          (jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ≫
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom) =
        (jetConstantTerm (k := k) κ (BasedJet.totOver ρ L).left ≫
          jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left) ≫
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom := (CategoryTheory.Category.assoc _ _ _).symm
    have s4 : (jetConstantTerm (k := k) κ (BasedJet.totOver ρ L).left ≫
          jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left) ≫
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom =
        CategoryTheory.CategoryStruct.id (BasedJet.totOver ρ L).left ≫
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom :=
      congrArg (fun g => g ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom)
        (jetConstantTerm_proj (k := k) κ (BasedJet.totOver ρ L).left)
    have s5 : CategoryTheory.CategoryStruct.id (BasedJet.totOver ρ L).left ≫
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom =
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom := CategoryTheory.Category.id_comp _
    exact s1.trans (s2.trans (s3.trans (s4.trans s5)))
  have hw₂ : ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫ jetNeighborhood.zeroSection L κ) ≫
      (jetNeighborhood L κ).hom =
      (CategoryTheory.Over.mk (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).hom := by
    rw [CategoryTheory.Category.assoc]
    exact (congrArg (fun g => (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫ g)
      (jetNeighborhood.zeroSection_proj L κ)).trans (CategoryTheory.Category.comp_id _)
  let h₁ : CategoryTheory.Over.mk (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⟶ jetNeighborhood L κ :=
    CategoryTheory.Over.homMk (jetConstantTerm (k := k) κ (BasedJet.totOver ρ L).left ≫ BasedJet.universalFrame ρ L κ) hw₁
  let h₂ : CategoryTheory.Over.mk (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⟶ jetNeighborhood L κ :=
    CategoryTheory.Over.homMk
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫ jetNeighborhood.zeroSection L κ) hw₂
  have key : h₁ = h₂ := by
    apply (AlgebraicGeometry.Scheme.relativeSpecHomEquiv (truncatedJetAlgebra L κ) _).injective
    apply Subtype.ext
    refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ (fun V => ?_)
    ext c
    have e₁ : (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V ≤
        (jetConstantTerm (k := k) κ (BasedJet.totOver ρ L).left ≫ BasedJet.universalFrame ρ L κ) ⁻¹ᵁ
          ((jetNeighborhood L κ).hom ⁻¹ᵁ V) :=
      le_of_eq (by rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, hw₁]; rfl)
    have e₂ : (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V ≤
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫ jetNeighborhood.zeroSection L κ) ⁻¹ᵁ
          ((jetNeighborhood L κ).hom ⁻¹ᵁ V) :=
      le_of_eq (by rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, hw₂]; rfl)
    -- both sides are by definition `pullbackSections = structureRingMap` followed by `(ι ≫ f)^♯` (in `appLE` form)
    have hA₁ : CommRingCat.ofHom (AlgebraicGeometry.Scheme.relativeSpec.pullbackSections (truncatedJetAlgebra L κ)
        (CategoryTheory.Over.mk (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom) h₁ V) =
        (AlgebraicGeometry.Scheme.relativeSpec.structureRingMap (truncatedJetAlgebra L κ)).app (Opposite.op V) ≫
        (jetConstantTerm (k := k) κ (BasedJet.totOver ρ L).left ≫ BasedJet.universalFrame ρ L κ).appLE
          ((jetNeighborhood L κ).hom ⁻¹ᵁ V)
          ((CategoryTheory.Over.mk (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).hom ⁻¹ᵁ V) e₁ := rfl
    have hA₂ : CommRingCat.ofHom (AlgebraicGeometry.Scheme.relativeSpec.pullbackSections (truncatedJetAlgebra L κ)
        (CategoryTheory.Over.mk (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom) h₂ V) =
        (AlgebraicGeometry.Scheme.relativeSpec.structureRingMap (truncatedJetAlgebra L κ)).app (Opposite.op V) ≫
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫ jetNeighborhood.zeroSection L κ).appLE
          ((jetNeighborhood L κ).hom ⁻¹ᵁ V)
          ((CategoryTheory.Over.mk (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).hom ⁻¹ᵁ V) e₂ := rfl
    have hS : ((AlgebraicGeometry.Scheme.relativeSpec.structureRingMap (truncatedJetAlgebra L κ)).app
        (Opposite.op V)).hom c =
        (show Γ((jetNeighborhood L κ).left, (jetNeighborhood L κ).hom ⁻¹ᵁ V) from
          (AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ)).app V c) :=
      (AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_apply _ V c).symm
    have hL := BasedJet.jetConstantTerm_universalFrame_appLE ρ L κ V c e₁
    have hR := BasedJet.totalSpace_zeroSection_appLE_structureHom ρ L κ V c e₂
    refine (congrArg (fun ψ => ψ.hom c) hA₁).trans (Eq.trans ?_ (congrArg (fun ψ => ψ.hom c) hA₂).symm)
    show ((jetConstantTerm (k := k) κ (BasedJet.totOver ρ L).left ≫ BasedJet.universalFrame ρ L κ).appLE
        ((jetNeighborhood L κ).hom ⁻¹ᵁ V) ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) e₁).hom
        (((AlgebraicGeometry.Scheme.relativeSpec.structureRingMap (truncatedJetAlgebra L κ)).app
          (Opposite.op V)).hom c) =
      (((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫ jetNeighborhood.zeroSection L κ).appLE
        ((jetNeighborhood L κ).hom ⁻¹ᵁ V) ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) e₂).hom
        (((AlgebraicGeometry.Scheme.relativeSpec.structureRingMap (truncatedJetAlgebra L κ)).app
          (Opposite.op V)).hom c)
    rw [hS]
    exact hL.trans hR.symm
  exact congrArg CategoryTheory.CommaMorphism.left key

/-- `u ≫ J` is a based jet on `W = Tot(L)`, assembled from `universalFrame_proj`, `jetConstantTerm_universalFrame`,
    `J.over` and `J.restrict`: (i) over `C`: `u ≫ J ≫ 𝒵.hom = u ≫ p_κ ≫ ρ = pr ≫ Tot.hom ≫ ρ`; (ii) constant term:
    `ι₀ ≫ u ≫ J = p ≫ 0_κ ≫ J = p ≫ ρ ≫ s`. -/
theorem BasedJet.universalFrame_comp_isBasedJet (J : BasedJet f ρ L κ) :
    letI := BasedJet.totOverField ρ L
    (BasedJet.universalFrame ρ L κ ≫ J.hom) ≫ (MMSetup.cone f).hom =
        jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ≫ (BasedJet.totOver ρ L).hom ∧
      jetConstantTerm (k := k) κ (BasedJet.totOver ρ L).left ≫ (BasedJet.universalFrame ρ L κ ≫ J.hom) =
        (BasedJet.totOver ρ L).hom ≫ (MMSetup.seed f).1 := by
  let _ := BasedJet.totOverField ρ L
  constructor
  · rw [CategoryTheory.Category.assoc, J.over, ← CategoryTheory.Category.assoc,
      BasedJet.universalFrame_proj ρ L κ]
    exact CategoryTheory.Category.assoc _ _ _
  · rw [← CategoryTheory.Category.assoc, BasedJet.jetConstantTerm_universalFrame ρ L κ]
    exact (CategoryTheory.Category.assoc _ _ _).trans
      ((congrArg (fun g => (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫ g) J.restrict).trans
        (CategoryTheory.Category.assoc _ _ _).symm)

/-- `φ_J : Tot(L) → J_κ^s(𝒵/C)` (a morphism over `C`): the point corresponding to the based jet `u ≫ J` (the based
condition is `universalFrame_comp_isBasedJet`). -/

noncomputable def BasedJet.jetPoint (J : BasedJet f ρ L κ) :
    BasedJet.totOver ρ L ⟶
      relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ :=
  relativeJetScheme.ofBasedJet (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ
    (BasedJet.totOver ρ L) ⟨BasedJet.universalFrame ρ L κ ≫ J.hom, J.universalFrame_comp_isBasedJet⟩

/-- `Ψ_m : ρ^*S_m → (L^∨)^{⊗m}`: the `m`-th graded component of the pullback along `φ_J` of the jet coordinate
functions of weight `m`. -/

noncomputable def BasedJet.weightComponent (J : BasedJet f ρ L κ) (m : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).obj ((jetAlgebra f κ).part m) ⟶
      AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m :=
  let Jk := relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ
  let Tot := AlgebraicGeometry.Scheme.totalSpace L.toModules
  let D := AlgebraicGeometry.Scheme.Modules.dual L.toModules
  let S := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra D
  let φ := J.jetPoint
  ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).homEquiv _ _).symm
    ((show (jetAlgebra f κ).part m ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward Jk.hom).obj
          (SheafOfModules.unit Jk.left.ringCatSheaf) from
        CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect
          (jetRescalingAction (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ) m)) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforward Jk.hom).map
        (SheafOfModules.unitToPushforwardObjUnit φ.left.toRingCatSheafHom) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp φ.left Jk.hom).hom.app _ ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardCongr (CategoryTheory.Over.w φ)).hom.app _ ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp Tot.hom ρ.hom).inv.app _ ≫
      (AlgebraicGeometry.Scheme.Modules.pushforward ρ.hom).map
        ((AlgebraicGeometry.Scheme.relativeSpec.structureIso S.total).inv ≫ S.totalProj m ≫
          AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow D m))





/-! ## Comparison of the two coefficient encodings -/

/-- A local section `t ∈ N(V)` does not vanish at a point `y ∈ V` (its germ does not lie in `𝔪_y N_y`; the negation of
the local-section version of `IsZeroAt`). -/
def AlgebraicGeometry.Scheme.Modules.GeneratesAt {Y : AlgebraicGeometry.Scheme.{u}} (N : Y.Modules)
    (V : Y.Opens) (t : (N.val.obj (Opposite.op V) : Type u)) (y : Y) (hy : y ∈ V) : Prop :=
  let N' : _root_.PresheafOfModules.{u} (Y.presheaf ⋙ CategoryTheory.forget₂ CommRingCat RingCat) := N.val
  (show (N.stalk y : Type u) from (TopCat.Presheaf.germ N'.presheaf V y hy).hom t) ∉
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) • (⊤ : Submodule (Y.presheaf.stalk y) (N.stalk y))

/-- The inclusion of the weight-`m` piece into `π_*O_J` (the `m`-th piece of `jetAlgebra` is by definition
`ker(weightDefect m)`). -/
noncomputable def BasedJet.partι (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ m : ℕ) :
    (jetAlgebra f κ).part m ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward
        (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom).obj
        (SheafOfModules.unit
          (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left.ringCatSheaf) :=
  CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect
    (jetRescalingAction (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ) m)

/-- The `J`-side encoding: the `m`-th `ξ`-coefficient of the pullback along `J` of a function `b ∈ Γ(𝒵, π⁻¹U)` on the
    cone: `J^♯ b ∈ Γ(C̃_(κ)(L), p⁻¹ρ⁻¹U) = (p_*O)(ρ⁻¹U) →(structureIso⁻¹) ⊕_{q≤κ} L^{-q} →(π_m) L^{-m} →(pieceIso) (L^∨)^{⊗m}`.
    This is the same chain `structureIso.inv ≫ biproduct.π ≫ pieceIso.hom` as in `J.coefficient`
    (`xiCoefficientThickening`). -/
noncomputable def BasedJet.pieceSection (J : BasedJet f ρ L κ) (U : C.toScheme.Opens) (m : ℕ) (hm : m ≤ κ)
    (b : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U)) :
    ((AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).val.obj
      (Opposite.op (ρ.hom ⁻¹ᵁ U)) : Type u) :=
  (((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
      CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨m, Nat.lt_succ_of_le hm⟩ ≫
      (truncatedJetAlgebra.pieceIso L m).hom).val.app (Opposite.op (ρ.hom ⁻¹ᵁ U))).hom
    (show (((AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
        (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf)).val.obj
          (Opposite.op (ρ.hom ⁻¹ᵁ U)) : Type u) from
      (J.hom.appLE ((MMSetup.cone f).hom ⁻¹ᵁ U) (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U)) (by
        rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, ← AlgebraicGeometry.Scheme.Hom.comp_preimage,
          J.over])).hom b)


/-- **Leaf (assembly).** The coefficient description of the universal frame: the `t^n`-coefficient of the pullback
along `u` of `g ∈ Γ(C̃_(κ)(L), p⁻¹V)` is `(the n-th piece of g)·ξ^n`, i.e. extract the `n`-th piece
`c_n ∈ L^{-n}(V)` by `structureIso⁻¹ ≫ π_n` and view it as a function on `p⁻¹V ⊆ Tot(L)` through `pieceIso` and
`frameHom L n`.

    Proof: let `c := structureIso⁻¹(g)`, so `g = structureHom(c)`.
    (1) `u` is `relativeSpec.ofAlgebraMap … universalFrameAlg …` (`rfl`), and `ofAlgebraMap_appLE_structureHom` gives
        `u^♯(structureHom c) = universalFrameAlg(c)`;
    (2) `biproduct_section_eq_sum`: `c = Σ_q ι_q(π_q c)`, and the section map of `universalFrameAlg` is additive (`map_sum`);
    (3) `universalFrameAlg_app_ι`: the `q`-th term is `pr^♯(frameHom q (pieceIso (π_q c)))·t^q`;
    (4) `jetThickening.coeff_sum_proj_mul_parameter_pow`: the `t^n`-coefficient is `frameHom n (pieceIso (π_n c))`;
    (5) the right-hand side unfolds by `SheafOfModules.comp_val`, `PresheafOfModules.comp_app` to the same expression
        (`frameHom` is `rfl`). Steps (2)–(4) are packaged as `universalFrameAlg_coeff`. -/
theorem BasedJet.universalFrame_coeff (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) (κ : ℕ)
    (V : ρ.source.toScheme.Opens) (n : ℕ) (hn : n ≤ κ)
    (g : Γ((jetNeighborhood L κ).left, jetNeighborhood.proj L κ ⁻¹ᵁ V)) :
    letI := BasedJet.totOverField ρ L
    ∀ h : jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ⁻¹ᵁ
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) ≤
        BasedJet.universalFrame ρ L κ ⁻¹ᵁ (jetNeighborhood.proj L κ ⁻¹ᵁ V),
    jetThickening.coeff (k := k) κ (BasedJet.totOver ρ L).left
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) n hn
        (((BasedJet.universalFrame ρ L κ).appLE _ _ h).hom g) =
      (show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) from
        (((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
            CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
              ⟨n, Nat.lt_succ_of_le hn⟩ ≫
            (truncatedJetAlgebra.pieceIso L n).hom ≫
            (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
              (AlgebraicGeometry.Scheme.Modules.dual L.toModules) n).hom ≫
            AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules n ≫
            (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
              (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl n ≫
            AlgebraicGeometry.Scheme.relativeSpec.structureHom
              (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
                (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).val.app (Opposite.op V)).hom
          (show (((AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
              (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf)).val.obj (Opposite.op V) : Type u) from g)) := by
  letI := BasedJet.totOverField ρ L
  intro h
  obtain ⟨c, hc⟩ : ∃ c : ((truncatedJetAlgebra L κ).carrier.val.obj (Opposite.op V) : Type u),
      (((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv.val.app
        (Opposite.op V)).hom g) = c := ⟨_, rfl⟩
  have hgc : ((AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ)).val.app
      (Opposite.op V)).hom c = g := by
    rw [← hc]
    exact congrArg (fun φ => (φ.val.app (Opposite.op V)).hom g)
      (AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv_hom_id
  have h1 : ((BasedJet.universalFrame ρ L κ).appLE _ _ h).hom
      (((AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ)).val.app
        (Opposite.op V)).hom c) = ((BasedJet.universalFrameAlg ρ L κ).val.app (Opposite.op V)).hom c :=
    AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap_appLE_structureHom (truncatedJetAlgebra L κ)
      (CategoryTheory.Over.mk (jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ≫
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom))
      (BasedJet.universalFrameAlg ρ L κ) (BasedJet.universalFrameAlg_isAlgebraMap ρ L κ) V c h
  conv_lhs => rw [← hgc]
  rw [h1]
  refine (BasedJet.universalFrameAlg_coeff ρ L κ V n hn c).trans ?_
  rw [← hc]
  rfl

/-- The jet coordinate `d_q b` (`b ∈ Γ(𝒵, π⁻¹U)`, `q : Fin κ`) has weight `q+1`: it is the image of a section of
    `S_{q+1}(U) = ker(weightDefect (q+1))(U)`. (Under `t ↦ λt` the universal jet `Σ D_n(b) t^n` becomes
    `Σ D_n(b) λ^n t^n`, so `act^♯(d_q b) = λ^{q+1}·pr₂^♯(d_q b)`.) -/
theorem BasedJet.exists_part_eq_jetCoordinate (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ)
    (U : C.toScheme.AffineZariskiSite) (q : Fin κ)
    (b : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U.1))
    (hU : (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1 =
      relativeJetScheme.chartOpen (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ U) :
    letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) U.1
    ∃ x : (((jetAlgebra f κ).part ((q : ℕ) + 1)).val.obj (Opposite.op U.1) : Type u),
      (show Γ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left,
          (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1) from
        ((BasedJet.partι f κ ((q : ℕ) + 1)).val.app (Opposite.op U.1)).hom x) =
      ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left.presheaf.map
          (CategoryTheory.eqToHom hU).op).hom
        ((relativeJetScheme.chartSections (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ U).hom
          (BasedJetAlgebra.coeffClass
            (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ
            ((q : ℕ) + 1) b)) := by
  -- assembled from the rescaling-chart lemmas: the weight-`(q+1)` defect vanishes on `d_q b`, and the kernel is
  -- computed open by open
  exact AlgebraicGeometry.Scheme.Modules.exists_kernel_section
    (GroupSchemeAction.weightDefect
      (jetRescalingAction (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ) ((q : ℕ) + 1)) U.1 _
    (jetRescalingAction_weightDefect_jetCoordinate (k := k) (MMSetup.cone f) (MMSetup.seed f).1
      (MMSetup.seed f).2 κ U q b hU)

/-- **Leaf.** Unfolding the adjoint transpose: the value of `weightComponent m` (viewed through `ρ^* ⊣ ρ_*` as
`S_m → ρ_*(L^∨)^{⊗m}`) on a section `x` over `U` is the `m`-th `ξ`-coefficient of `φ_J^♯(x)` (`x` viewed through
`partι` as a function on `π⁻¹U ⊆ J`, pulled back along `φ_J = jetPoint` to a function on `(ρ∘p)⁻¹U ⊆ Tot(L)`).

    Proof: `weightComponent m = homEquiv.symm (partι ≫ π_*(φ^♯) ≫ pushforwardComp.hom ≫ pushforwardCongr.hom ≫
    pushforwardComp.inv ≫ ρ_*(symCoeffHom L m))` (definition), so `homEquiv (weightComponent m)` is the composite in
    parentheses (`Equiv.apply_symm_apply`). On sections over `U`: `π_*(unitToPushforwardObjUnit φ.left)` is
    `φ.left.app (π⁻¹U)`, `pushforwardComp.hom/inv` are the identity, `pushforwardCongr (Over.w φ)` is restriction along
    an equality of opens, and together these are `φ.left.appLE (π⁻¹U) ((ρ∘p)⁻¹U)`; `ρ_*(symCoeffHom)` on `U` is
    `symCoeffHom` on `ρ⁻¹U`. Formally: `unfold weightComponent; rw [Equiv.apply_symm_apply]`, then `show` the left side
    as `symCoeffHom (presheaf.map (eqToHom e).op (φ^♯ x))`, use `eqToHom e = homOfLE hle` (the hom-sets of `Opens` are
    subsingletons), and the right side is `rfl` by the definition of `appLE`. -/
theorem BasedJet.weightComponent_adj_app (J : BasedJet f ρ L κ) (m : ℕ) (U : C.toScheme.Opens)
    (x : (((jetAlgebra f κ).part m).val.obj (Opposite.op U) : Type u))
    (hle : (BasedJet.totOver ρ L).hom ⁻¹ᵁ U ≤ J.jetPoint.left ⁻¹ᵁ
      ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U)) :
    (show ((AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
          m).val.obj (Opposite.op (ρ.hom ⁻¹ᵁ U)) : Type u) from
        ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).homEquiv _ _)
          (J.weightComponent m)).val.app (Opposite.op U)).hom x) =
      ((BasedJet.symCoeffHom L m).val.app (Opposite.op (ρ.hom ⁻¹ᵁ U))).hom
        (show (((AlgebraicGeometry.Scheme.Modules.pushforward
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
            (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)).val.obj
              (Opposite.op (ρ.hom ⁻¹ᵁ U)) : Type u) from
          (J.jetPoint.left.appLE
              ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U)
              ((BasedJet.totOver ρ L).hom ⁻¹ᵁ U) hle).hom
            (show Γ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left,
                (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U) from
              ((BasedJet.partι f κ m).val.app (Opposite.op U)).hom x)) := by
  unfold BasedJet.weightComponent
  rw [Equiv.apply_symm_apply]
  have e : (BasedJet.totOver ρ L).hom ⁻¹ᵁ U =
      (J.jetPoint.left ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom)
        ⁻¹ᵁ U := by
    rw [CategoryTheory.Over.w]
  show ((BasedJet.symCoeffHom L m).val.app (Opposite.op (ρ.hom ⁻¹ᵁ U))).hom
      (((AlgebraicGeometry.Scheme.totalSpace L.toModules).left.presheaf.map (CategoryTheory.eqToHom e).op).hom
        ((J.jetPoint.left.app
          ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U)).hom
          (((BasedJet.partι f κ m).val.app (Opposite.op U)).hom x))) = _
  have heq : (CategoryTheory.eqToHom e : (BasedJet.totOver ρ L).hom ⁻¹ᵁ U ⟶ _) = CategoryTheory.homOfLE hle :=
    Subsingleton.elim _ _
  rw [heq]
  rfl

/-- **Leaf (assembly).** `φ_J^♯(d_q b) = (the (q+1)-th piece of J^♯ b)·ξ^{q+1}`: the jet coordinate `d_q b` pulled
back along `φ_J = jetPoint` to `Tot(L)` equals `frameHom (q+1)` applied to `pieceSection` (the `(q+1)`-th
`ξ`-coefficient of `J^♯ b`).

    Proof (one lemma per step):
    (1) `jetPoint = ofBasedJet (totOver) ⟨u ≫ J.hom, _⟩` (definition). Move the left side along `eqToHom hU` to the
        chart image (`Scheme.Hom.appLE_map`) and use `relativeJetScheme.ofBasedJet_appLE_coeffClass` (with `W = totOver`,
        `φ = u ≫ J`): the left side is `jetThickening.coeff (q+1) ((u ≫ J.hom).appLE … b)`.
    (2) `Scheme.Hom.comp_appLE`: `(u ≫ J.hom).appLE = J.hom.appLE ≫ u.appLE` with intermediate open `p_κ⁻¹(ρ⁻¹U)`, so
        `(u ≫ J)^♯ b = u^♯(g)` with `g := J^♯ b` (the element in the body of `pieceSection`).
    (3) `BasedJet.universalFrame_coeff` (with `V = ρ⁻¹U`, `n = q+1`, this `g`):
        `coeff_{q+1}(u^♯ g) = (structureIso⁻¹ ≫ π_{q+1} ≫ pieceIso ≫ powIso ≫ tensorPowerToSymPart ≫ totalIncl ≫ structureHom)(g)`;
        the last four segments are `frameHom L (q+1)` (`rfl`), the first three applied to `g` are
        `pieceSection U (q+1) b` (`rfl`).
    The equalities of opens (`comp_preimage`, `Over.w`, `universalFrame_proj`, `universalFrame_comp_isBasedJet.1`)
    are used through `exact`/`le_of_eq` rather than `rw` (`totOver.left` and `Tot.left` are not reducibly equal). -/
theorem BasedJet.jetPoint_appLE_jetCoordinate (J : BasedJet f ρ L κ)
    (U : C.toScheme.AffineZariskiSite) (q : Fin κ)
    (b : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U.1))
    (hU : (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1 =
      relativeJetScheme.chartOpen (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ U)
    (hle : (BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1 ≤ J.jetPoint.left ⁻¹ᵁ
      ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1)) :
    letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) U.1
    (show (((AlgebraicGeometry.Scheme.Modules.pushforward
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
            (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)).val.obj
              (Opposite.op (ρ.hom ⁻¹ᵁ U.1)) : Type u) from
      (J.jetPoint.left.appLE
          ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1)
          ((BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1) hle).hom
        (((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left.presheaf.map
            (CategoryTheory.eqToHom hU).op).hom
          ((relativeJetScheme.chartSections (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ U).hom
            (BasedJetAlgebra.coeffClass
              (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ
              ((q : ℕ) + 1) b)))) =
      ((BasedJet.frameHom L ((q : ℕ) + 1)).val.app (Opposite.op (ρ.hom ⁻¹ᵁ U.1))).hom
        (J.pieceSection U.1 ((q : ℕ) + 1) (Nat.succ_le_of_lt q.2) b) := by
  letI := BasedJet.totOverField ρ L
  letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) U.1
  -- (1) move along eqToHom hU to the chart
  have hle' : (BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1 ≤ J.jetPoint.left ⁻¹ᵁ
      relativeJetScheme.chartOpen (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ U := by
    rw [← hU]; exact hle
  have h1 := congrArg (fun φ : Γ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left,
      relativeJetScheme.chartOpen (k := k) (MMSetup.cone f) (MMSetup.seed f).1
        (MMSetup.seed f).2 κ U) ⟶ Γ((BasedJet.totOver ρ L).left, (BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1) => φ.hom
      ((relativeJetScheme.chartSections (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ U).hom
        (BasedJetAlgebra.coeffClass
          (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ
          ((q : ℕ) + 1) b)))
    (AlgebraicGeometry.Scheme.Hom.map_appLE J.jetPoint.left hle (CategoryTheory.eqToHom hU).op)
  refine h1.trans ?_
  -- (2) ofBasedJet on the chart
  have hφ : jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ⁻¹ᵁ ((BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1) ≤
      (BasedJet.universalFrame ρ L κ ≫ J.hom) ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ U.1) := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, ← AlgebraicGeometry.Scheme.Hom.comp_preimage,
      J.universalFrame_comp_isBasedJet.1, AlgebraicGeometry.Scheme.Hom.comp_preimage]
  have h2 := relativeJetScheme.ofBasedJet_appLE_coeffClass (k := k) (MMSetup.cone f) (MMSetup.seed f).1
    (MMSetup.seed f).2 κ (BasedJet.totOver ρ L) ⟨BasedJet.universalFrame ρ L κ ≫ J.hom, J.universalFrame_comp_isBasedJet⟩
    U q b hle' hφ
  refine h2.trans ?_
  -- (3) split u ≫ J.hom through proj⁻¹(ρ⁻¹U)
  have e₁ : (MMSetup.cone f).hom ⁻¹ᵁ U.1 ≤ (MMSetup.cone f).hom ⁻¹ᵁ U.1 := le_rfl
  have e₂ : jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U.1) ≤ J.hom ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ U.1) := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage J.hom, J.over]
    exact le_rfl
  have e₃ : jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ⁻¹ᵁ
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U.1)) ≤
      BasedJet.universalFrame ρ L κ ⁻¹ᵁ (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U.1)) := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, BasedJet.universalFrame_proj]
    exact le_of_eq (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).symm
  have h3 := congrArg (fun φ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U.1) ⟶
      Γ(jetThickening (k := k) κ (BasedJet.totOver ρ L).left,
        jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ⁻¹ᵁ ((BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1)) => φ.hom b)
    (AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE (BasedJet.universalFrame ρ L κ) J.hom
      ((MMSetup.cone f).hom ⁻¹ᵁ U.1) (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U.1)) _ e₂ e₃)
  show jetThickening.coeff (k := k) κ (BasedJet.totOver ρ L).left
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U.1)) ((q : ℕ) + 1) (Nat.succ_le_of_lt q.2)
      (((BasedJet.universalFrame ρ L κ ≫ J.hom).appLE ((MMSetup.cone f).hom ⁻¹ᵁ U.1)
        (jetThickeningProj (k := k) κ (BasedJet.totOver ρ L).left ⁻¹ᵁ
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U.1))) hφ).hom b) = _
  refine (congrArg (jetThickening.coeff (k := k) κ (BasedJet.totOver ρ L).left
    ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U.1)) ((q : ℕ) + 1)
    (Nat.succ_le_of_lt q.2)) h3.symm).trans ?_
  -- (4) universalFrame_coeff
  exact BasedJet.universalFrame_coeff ρ L κ (ρ.hom ⁻¹ᵁ U.1) ((q : ℕ) + 1) (Nat.succ_le_of_lt q.2) _ e₃

/-- **Comparison theorem**: the value of `weightComponent` (viewed through the adjunction as
    `S_{q+1} → ρ_*(L^∨)^{⊗(q+1)}`) on the jet coordinate `d_q b` is the `(q+1)`-th `ξ`-coefficient of `J^♯ b`
    (`pieceSection`, the encoding chain used by `J.coefficient`). -/
theorem BasedJet.weightComponent_jetCoordinate (J : BasedJet f ρ L κ)
    (U : C.toScheme.AffineZariskiSite) (q : Fin κ)
    (b : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U.1))
    (hU : (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1 =
      relativeJetScheme.chartOpen (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ U)
    (x : (((jetAlgebra f κ).part ((q : ℕ) + 1)).val.obj (Opposite.op U.1) : Type u)) :
    letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) U.1
    (show Γ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left,
          (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1) from
        ((BasedJet.partι f κ ((q : ℕ) + 1)).val.app (Opposite.op U.1)).hom x) =
      ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left.presheaf.map
          (CategoryTheory.eqToHom hU).op).hom
        ((relativeJetScheme.chartSections (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ U).hom
          (BasedJetAlgebra.coeffClass
            (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ
            ((q : ℕ) + 1) b)) →
    (show ((AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
          ((q : ℕ) + 1)).val.obj (Opposite.op (ρ.hom ⁻¹ᵁ U.1)) : Type u) from
        ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).homEquiv _ _)
          (J.weightComponent ((q : ℕ) + 1))).val.app (Opposite.op U.1)).hom x) =
      J.pieceSection U.1 ((q : ℕ) + 1) (Nat.succ_le_of_lt q.2) b := by
  -- assembled from `weightComponent_adj_app`, `jetPoint_appLE_jetCoordinate` and `frameHom_symCoeffHom`
  intro hx
  have hle : (BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1 ≤ J.jetPoint.left ⁻¹ᵁ
      ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1) := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, CategoryTheory.Over.w]
  have h1 := J.weightComponent_adj_app ((q : ℕ) + 1) U.1 x hle
  have h2 := J.jetPoint_appLE_jetCoordinate U q b hU hle
  have h3 := congrArg (fun g => (g.val.app (Opposite.op (ρ.hom ⁻¹ᵁ U.1))).hom
    (J.pieceSection U.1 ((q : ℕ) + 1) (Nat.succ_le_of_lt q.2) b))
    (BasedJet.frameHom_symCoeffHom L ((q : ℕ) + 1))
  refine h1.trans ?_
  rw [hx]
  refine (congrArg (fun y => ((BasedJet.symCoeffHom L ((q : ℕ) + 1)).val.app
    (Opposite.op (ρ.hom ⁻¹ᵁ U.1))).hom y) h2).trans ?_
  exact h3


/-- **Leaf.** Cone-coordinate side: if `J.coefficient ℓ m` does not vanish at `y`, then there are an affine
    neighbourhood `U` of `ρ(y)` and a function `b ∈ Γ(𝒵, π⁻¹U)` on the cone such that the `m`-th `ξ`-coefficient
    (`pieceSection`) of `J^♯ b` does not vanish at `y`.

    Source: proof of Lemma 3.1 of the paper (choose a frame `ε` to write `P_ℓ` as `Σ c_{ℓ,q} ξ^q`;
    the coefficients are read off in the frame); the definition of `BasedJet.coefficient`
    (`xiCoefficientThickening`, `NormalizedTupleNowhereZero.lean`).

    Proof:
    (1) Choose an affine open `U ∋ ρ(y)` on which the line bundle `A := f^*O(1)` has a frame `a ∈ Γ(A, U)`
        (`exists_affine_frame_le`).
    (2) Build the dual frame `α ∈ Γ(A^∨, U)` from `a` (`IsFrame.dualSec`).
    (3) Let `b := totalSpace.coordinateFunctionOn (A, N+1, ℓ, U, α)` pulled back along the closed immersion
        `𝒵 ↪ Tot(A^{⊕(N+1)})`, i.e. the paper's `x_ℓ^a|_𝒵 ∈ Γ(𝒵, π⁻¹U)`.
    (4) Key identity: after restriction to `ρ⁻¹U`,
        `pullbackSectionToPushforward p M (coneCoordinate J ℓ) = a_M ⊗ (J ≫ coneι)^♯(x_ℓ^{a^∨})`
        (`BasedJet.coneCoordinate_res_eq_smul`, from `totalSpaceHomEquiv_coordinate_res_eq_smul`;
        `pullbackSectionToPushforward_coneCoordinate_res`; `coefficient_eq`). Both sides are compared in
        `M ⊗ (L^∨)^{⊗m}`; `coefficientModuleIso`/`tensorIsoTensorObj` only enter as one-way transports through
        `isZeroAt_hom_app`, and the chain `structureIso⁻¹ ≫ π_m ≫ pieceIso ≫ monoidalPowIsoTensorPower` in the body of
        `xiCoefficientThickening` agrees literally with the first three segments of `pieceSection` (`rfl`).
    (5) `ρ^*a` generates everywhere (the pullback of a frame is a frame), and tensoring with an everywhere generating
        section does not change "vanishes at `y`" (`IsFrame.germ_tensorSections_mem_maximalIdeal_smul_iff_left`,
        module `GermCriteria`); hence `¬IsZeroAt (J.coefficient ℓ m) y` implies `GeneratesAt … (pieceSection …) y`.
    The hypothesis `h1 : 1 ≤ m` is not used (the conclusion also holds for `m = 0`); it is kept so that the statement
    matches its use in `NormalizedTupleNowhereZero`. The unfolded form is
    `BasedJet.exists_pieceSection_germ_notMem_of_not_isZeroAt` (`JetWeightComponentEqCoefficientGeneratesAtAux.lean`).
    Edge case: `U = ⊥` cannot occur (`y` gives a point). -/
theorem BasedJet.exists_pieceSection_generatesAt (J : BasedJet f ρ L κ) (y : ρ.source.toScheme)
    (ℓ : Fin (X.embDim + 1)) (m : ℕ) (h1 : 1 ≤ m) (hm : m ≤ κ) (h : ¬ IsZeroAt (J.coefficient ℓ m) y) :
    ∃ (U : C.toScheme.AffineZariskiSite) (hy : y ∈ ρ.hom ⁻¹ᵁ U.1)
      (b : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U.1)),
      AlgebraicGeometry.Scheme.Modules.GeneratesAt
        (AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m)
        (ρ.hom ⁻¹ᵁ U.1) (J.pieceSection U.1 m hm b) y hy := by
  obtain ⟨U, hy, b, hb⟩ := J.exists_pieceSection_germ_notMem_of_not_isZeroAt y ℓ m hm h
  exact ⟨U, hy, b, hb⟩

/-- A tensor power of a line bundle is a line bundle. -/
theorem AlgebraicGeometry.Scheme.Modules.monoidalPow_isLineBundle {Y : AlgebraicGeometry.Scheme.{u}}
    (N : Y.Modules) [N.IsLineBundle] (m : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.monoidalPow N m).IsLineBundle := by
  -- induction on `m`: `IsLineBundle.unit`, `IsLineBundle.tensor`, `tensorIsoTensorObj`
  induction m with
  | zero => exact inferInstanceAs (SheafOfModules.unit Y.ringCatSheaf).IsLineBundle
  | succ n ih =>
      have := ih
      exact SheafOfModules.IsLineBundle.of_iso
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Scheme.Modules.monoidalPow N n) N)

/-- **Small variable-level lemma.** `homOfSection` and composition with a morphism:
    `homOfSection M s ≫ p = homOfSection N (p_⊤ s)` (`unitHomEquiv` is injective + `naturality_apply`). -/
theorem AlgebraicGeometry.Scheme.Modules.homOfSection_comp {T : AlgebraicGeometry.Scheme.{u}} {M N : T.Modules}
    (s : Γ(M, ⊤)) (p : M ⟶ N) :
    AlgebraicGeometry.Scheme.Modules.homOfSection M s ≫ p =
      AlgebraicGeometry.Scheme.Modules.homOfSection N ((p.val.app (Opposite.op ⊤)).hom s) := by
  apply (SheafOfModules.unitHomEquiv N).injective
  unfold AlgebraicGeometry.Scheme.Modules.homOfSection
  change PresheafOfModules.sectionsMap p.val
      ((SheafOfModules.unitHomEquiv _) ((SheafOfModules.unitHomEquiv _).symm _)) =
    (SheafOfModules.unitHomEquiv _) ((SheafOfModules.unitHomEquiv _).symm _)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext O
  exact PresheafOfModules.naturality_apply p.val (homOfLE le_top).op s

/-- **Leaf.** A section of a line bundle that generates at a point is a frame on a neighbourhood of that point.

    Source: Stacks 01CR / Nakayama (`Mathlib.RingTheory.Nakayama`); local triviality of line bundles, Stacks 01CV.

    Proof:
    (1) `N` is a line bundle; take a neighbourhood `W₀ ≤ V` of `y` with a frame `e` (`exists_frame_le`) and let `c` be
        the coordinate of `t` with respect to `e` (`coord`).
    (2) `GeneratesAt` says that the germ of `t` is not in `𝔪_y·N_y`; hence the germ of `c` is a unit of the local ring
        (`IsLocalRing.notMem_maximalIdeal`, `germ_smul'`, `Submodule.smul_mem_smul`).
    (3) Being a unit is an open condition: take `W := T.basicOpen c ∋ y` (`Scheme.mem_basicOpen`).
    (4) On `W` the coordinate `c` is a unit (`RingedSpace.isUnit_res_basicOpen`), so `t|_W` is a frame
        (`IsFrame.of_isUnit_coord`).
    Edge cases: `V = ⊥` cannot occur (`hy : y ∈ V`); for `t = 0`, `GeneratesAt` is false and the hypothesis fails. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_isFrame_of_generatesAt
    {T : AlgebraicGeometry.Scheme.{u}} (N : T.Modules) [N.IsLineBundle] (V : T.Opens)
    (t : (N.val.obj (Opposite.op V) : Type u)) (y : T) (hy : y ∈ V)
    (h : AlgebraicGeometry.Scheme.Modules.GeneratesAt N V t y hy) :
    ∃ (W : T.Opens) (_ : y ∈ W) (hWV : W ≤ V),
      AlgebraicGeometry.Scheme.Modules.IsFrame N W
        ((N.presheaf.map (CategoryTheory.homOfLE hWV).op) t) := by
  obtain ⟨W₀, hW₀V, hyW₀, e, hf⟩ := exists_frame_le N hy
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : Γ(N, W₀), N.res hW₀V t = t₀ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Γ(T, W₀), hf.coord le_rfl t₀ = c := ⟨_, rfl⟩
  have hct : c • e = t₀ := by
    rw [← hc]
    have := hf.coord_smul_frame le_rfl t₀
    rwa [res_self] at this
  have hcu : IsUnit (T.presheaf.germ W₀ y hyW₀ c) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    have h1 : N.presheaf.germ V y hy t = N.presheaf.germ W₀ y hyW₀ t₀ := by
      rw [← ht₀]
      exact (TopCat.Presheaf.germ_res_apply N.presheaf (homOfLE hW₀V) y hyW₀ t).symm
    have key : (show (N.stalk y : Type u) from N.presheaf.germ W₀ y hyW₀ t₀) ∈
        (IsLocalRing.maximalIdeal (T.presheaf.stalk y)) •
          (⊤ : Submodule (T.presheaf.stalk y) (N.stalk y)) := by
      have hmem' := Submodule.smul_mem_smul hmem
        (Submodule.mem_top (R := T.presheaf.stalk y)
          (x := (show (N.stalk y : Type u) from N.presheaf.germ W₀ y hyW₀ e)))
      rw [← hct, germ_smul']
      exact hmem'
    have key' : (show (N.stalk y : Type u) from N.presheaf.germ V y hy t) ∈
        (IsLocalRing.maximalIdeal (T.presheaf.stalk y)) •
          (⊤ : Submodule (T.presheaf.stalk y) (N.stalk y)) := by
      rw [h1]
      exact key
    exact h key'
  have hyW : y ∈ T.basicOpen c := (T.mem_basicOpen _ y hyW₀).mpr hcu
  have hWW₀ : T.basicOpen c ≤ W₀ := T.basicOpen_le _
  refine ⟨T.basicOpen c, hyW, hWW₀.trans hW₀V, ?_⟩
  have hres : (N.presheaf.map (homOfLE (hWW₀.trans hW₀V)).op t : Γ(N, T.basicOpen c)) =
      N.res hWW₀ t₀ := by
    rw [← ht₀]
    exact (res_res N hWW₀ hW₀V t).symm
  rw [hres]
  refine (hf.restrict hWW₀).of_isUnit_coord (t := N.res hWW₀ t₀) ?_
  have hcoord : (hf.restrict hWW₀).coord le_rfl (N.res hWW₀ t₀) =
      T.presheaf.map (homOfLE hWW₀).op c := by
    apply IsFrame.coord_unique
    rw [res_self, ← hct]
    exact (res_smul N hWW₀ c e).symm
  rw [hcoord]
  exact RingedSpace.isUnit_res_basicOpen (X := T.toRingedSpace) c

/-- **Leaf.** A criterion for a map to a line bundle to be surjective near a point: if `Ψ : g^*F → N` and
    `x ∈ F(U)` is such that the adjoint image of `x` (a section of `g_*N` over `U`, i.e. of `N` over `g⁻¹U`) does not
    vanish at `y`, then `Ψ` is an epimorphism on some open neighbourhood of `y`.

    Source: Stacks 01CR (the sheaf version of Nakayama); EGA I 9.4.1.

    Proof:
    (1) By `Modules.exists_isFrame_of_generatesAt`, choose `W ∋ y`, `W ≤ g⁻¹U`, such that `t := (homEquiv Ψ)(x)` is a
        frame of `N` on `W`.
    (2) A frame gives an isomorphism `O_W → N|_W`, `1 ↦ t|_W` (`IsFrame.restrictIso`); in particular this morphism is
        an epimorphism.
    (3) It factors through `Ψ`: by the triangle identity `Adjunction.homEquiv_unit`, `homEquiv Ψ = η_F ≫ g_*Ψ`, so
        `t = Ψ_{g⁻¹U}(η_F(x))` and "`O_W → N|_W`, `1 ↦ t|_W`" equals "`O_W → (g^*F)|_W`, `1 ↦ (η_F x)|_W`" followed by
        `(pullback W.ι).map Ψ`; here `(η_F x)|_W` is viewed as a *global* section of `(g^*F).restrict W.ι`
        (`homOfSection`, `homOfSection_comp`).
    (4) `CategoryTheory.epi_of_epi_fac`: the composite is an isomorphism (hence epi), so `(pullback W.ι).map Ψ` is epi.
        Take `U' := W`.
    Edge cases: `U' = ⊥` would be harmless (epi is trivial), but `hy` guarantees `y ∈ U'`; `N = 0` is not a line
    bundle and is excluded by the hypotheses. -/
theorem AlgebraicGeometry.Scheme.Modules.epi_of_generatesAt {T Y : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ Y)
    (F : Y.Modules) (N : T.Modules) [N.IsLineBundle]
    (Ψ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj F ⟶ N) (U : Y.Opens)
    (x : (F.val.obj (Opposite.op U) : Type u)) (y : T) (hy : y ∈ g ⁻¹ᵁ U)
    (h : AlgebraicGeometry.Scheme.Modules.GeneratesAt N (g ⁻¹ᵁ U)
      (show (N.val.obj (Opposite.op (g ⁻¹ᵁ U)) : Type u) from
        ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _) Ψ).val.app
          (Opposite.op U)).hom x) y hy) :
    ∃ (U' : T.Opens) (_ : y ∈ U'), CategoryTheory.Epi ((AlgebraicGeometry.Scheme.Modules.pullback U'.ι).map Ψ) := by
  obtain ⟨W, hyW, hWV, hf⟩ := exists_isFrame_of_generatesAt N (g ⁻¹ᵁ U) _ y hy h
  refine ⟨W, hyW, ?_⟩
  obtain ⟨s, hs⟩ : ∃ s : Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ U),
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F).val.app (op U)).hom x = s :=
    ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : Γ(N, g ⁻¹ᵁ U),
      ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _) Ψ).val.app
        (Opposite.op U)).hom x = t := ⟨_, rfl⟩
  have hf' : IsFrame N W (N.res hWV t) := by
    rw [← ht]
    exact hf
  have hts : t = (Ψ.val.app (op (g ⁻¹ᵁ U))).hom s := by
    rw [← ht, ← hs, Adjunction.homEquiv_unit]
    rfl
  have hfr : IsFrame (N.restrict W.ι) ⊤ (N.res (image_ι_le W ⊤) (N.res hWV t)) := hf'.restrict_top
  have hkey : (((AlgebraicGeometry.Scheme.Modules.restrictFunctor W.ι).map Ψ).val.app (op ⊤)).hom
      (((AlgebraicGeometry.Scheme.Modules.pullback g).obj F).res (image_ι_le W ⊤)
        (((AlgebraicGeometry.Scheme.Modules.pullback g).obj F).res hWV s)) =
      N.res (image_ι_le W ⊤) (N.res hWV t) := by
    show (Ψ.val.app (op (W.ι ''ᵁ ⊤))).hom
      (((AlgebraicGeometry.Scheme.Modules.pullback g).obj F).res (image_ι_le W ⊤)
        (((AlgebraicGeometry.Scheme.Modules.pullback g).obj F).res hWV s)) = _
    rw [res_res, res_res, hts]
    exact PresheafOfModules.naturality_apply Ψ.val (homOfLE ((image_ι_le W ⊤).trans hWV)).op s
  have hθ : homOfSection (((AlgebraicGeometry.Scheme.Modules.pullback g).obj F).restrict W.ι)
        (((AlgebraicGeometry.Scheme.Modules.pullback g).obj F).res (image_ι_le W ⊤)
          (((AlgebraicGeometry.Scheme.Modules.pullback g).obj F).res hWV s)) ≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor W.ι).map Ψ =
      homOfSection (N.restrict W.ι) (N.res (image_ι_le W ⊤) (N.res hWV t)) :=
    (homOfSection_comp _ _).trans (congrArg (homOfSection (N.restrict W.ι)) hkey)
  have hiso : IsIso (homOfSection (N.restrict W.ι) (N.res (image_ι_le W ⊤) (N.res hWV t))) :=
    (Iso.isIso_hom hfr.topTrivialization)
  have hepi : Epi ((AlgebraicGeometry.Scheme.Modules.restrictFunctor W.ι).map Ψ) :=
    @epi_of_epi_fac _ _ _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ hiso) hθ
  exact epi_of_epi_fac
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.naturality Ψ).symm

/-- A nonzero global section of a line bundle on an integral scheme does not vanish at the generic point. -/
theorem AlgebraicGeometry.Scheme.Modules.not_isZeroAt_genericPoint {Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral Y] (N : Y.Modules) [N.IsLineBundle]
    (s : (N.val.obj (Opposite.op ⊤) : Type u)) (hs : s ≠ 0) : ¬ IsZeroAt s (genericPoint Y) := by
  -- at the generic point the stalk is a field, `𝔪 = ⊥`, and `IsZeroAt` means the germ is `0`; then a section of a line
  -- bundle whose germ at the generic point is `0` is `0`
  intro h
  apply hs
  apply lineBundle_section_eq_zero_of_germ_genericPoint_eq_zero N s
  unfold IsZeroAt at h
  have hm : IsLocalRing.maximalIdeal (Y.presheaf.stalk (genericPoint Y)) = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.1 (Field.toIsField (Y.functionField))
  rw [hm, Submodule.bot_smul] at h
  exact (Submodule.mem_bot _).1 h

/-- Pointwise generation: if some positive-order coefficient does not vanish at `y`, then `Ψ_m` is an epimorphism near
`y` for some positive `m`. Assembled from the four preceding lemmas. -/
theorem BasedJet.weightComponent_generates_at (J : BasedJet f ρ L κ) (y : ρ.source.toScheme)
    (h : ∃ (ℓ : Fin (X.embDim + 1)) (q : ℕ), 1 ≤ q ∧ q ≤ κ ∧ ¬ IsZeroAt (J.coefficient ℓ q) y) :
    ∃ (U : ρ.source.toScheme.Opens) (_ : y ∈ U) (m : ℕ) (_ : 0 < m),
      CategoryTheory.Epi ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).map (J.weightComponent m)) := by
  obtain ⟨ℓ, m, h1, hm, hz⟩ := h
  obtain ⟨U, hy, b, hgen⟩ := J.exists_pieceSection_generatesAt y ℓ m h1 hm hz
  obtain ⟨q, rfl⟩ : ∃ q : Fin κ, m = (q : ℕ) + 1 := ⟨⟨m - 1, by omega⟩, by simp; omega⟩
  have hU := relativeJetScheme.preimage_eq_chartOpen (k := k) (MMSetup.cone f) (MMSetup.seed f).1
    (MMSetup.seed f).2 κ U
  obtain ⟨x, hx⟩ := BasedJet.exists_part_eq_jetCoordinate f κ U q b hU
  have hmain := J.weightComponent_jetCoordinate U q b hU x hx
  have := AlgebraicGeometry.Scheme.Modules.monoidalPow_isLineBundle
    (AlgebraicGeometry.Scheme.Modules.dual L.toModules) ((q : ℕ) + 1)
  obtain ⟨U', hyU', hepi⟩ := AlgebraicGeometry.Scheme.Modules.epi_of_generatesAt ρ.hom _ _
    (J.weightComponent ((q : ℕ) + 1)) U.1 x y hy (hmain ▸ hgen)
  exact ⟨U', hyU', (q : ℕ) + 1, Nat.succ_pos _, hepi⟩

/-- If the normalized coefficient tuple of `J` is nowhere zero, then at every point some `Ψ_m` (`m > 0`) is an
epimorphism nearby. -/
theorem BasedJet.weightComponent_generates_of_nowhereZero (J : BasedJet f ρ L κ)
    (hnz : NormalizedTupleNowhereZero J) :
    ∀ t : ρ.source.toScheme, ∃ (U : ρ.source.toScheme.Opens) (_ : t ∈ U) (m : ℕ) (_ : 0 < m),
      CategoryTheory.Epi ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).map (J.weightComponent m)) :=
  fun t => J.weightComponent_generates_at t (hnz t)

/-- If some positive-order coefficient of `J` is nonzero, then the weight components restricted to the generic point
of `C̃` generate: at every point of `Spec κ(C̃)` some `precompΨ … m` (`m > 0`) is an epimorphism nearby. -/
theorem BasedJet.genericWeightComponent_generates_of_ne_zero (J : BasedJet f ρ L κ)
    (hne : ∃ ℓ q, 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0) :
    ∀ t : ↥(AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))),
      ∃ (U : (AlgebraicGeometry.Spec
          (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) (_ : t ∈ U)
        (m : ℕ) (_ : 0 < m),
        CategoryTheory.Epi ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).map
          (AlgebraicGeometry.Scheme.relativeProj.precompΨ
            (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme)) J.weightComponent m)) := by
  intro t
  obtain ⟨ℓ, q, h1, hq, hc⟩ := hne
  have : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  have hz := AlgebraicGeometry.Scheme.Modules.not_isZeroAt_genericPoint _ (J.coefficient ℓ q) hc
  refine AlgebraicGeometry.Scheme.relativeProj.precompΨ_generates_at _ _ t ?_
  rw [show (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme)).base t =
    genericPoint ρ.source.toScheme from AlgebraicGeometry.Scheme.fromSpecResidueField_apply _ t]
  exact J.weightComponent_generates_at _ ⟨ℓ, q, h1, hq, hz⟩

end
