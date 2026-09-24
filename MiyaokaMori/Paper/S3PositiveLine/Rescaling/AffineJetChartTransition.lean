import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.AffineJetChartCoords
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.ChartFamilyWeightFunction
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.WeightedOrderChartIndependent
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.JetTransitionPolynomialLinearPart
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialPresentationRestrict
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.GenericAffineJetPoint

/-! # The coordinate tuples of one affine jet in two charts are related by the jet transition
(step 1 of the proof of Lemma 3.1 of the paper,
`829--839`)

> The tuples `b_α = (b_{α,i,q})` satisfy (2.7), with its coefficients mapped to `K`
> through `k(C) ↪ k(C̃₀) ↪ K`. … This number [`w_y`] is independent of the chart. The transition
> coefficients are regular at `ρ(y)`, so every weight-`q` transition monomial has order at least
> `q w_y`. The inverse transition gives the reverse inequality.

* `HonestJetChart.nonempty_polyPresentation`: honesty as a `GradedQCAlgebra.PolyPresentation` with
  variables indexed by `Fin (n+1) × Fin κ`.
* `affineJetCoord_jetTransitionStep`: one direction of the transition, `JetTransitionStep (b α) (b β) y`.
* `affineJetCoord_jetTransitionRelated`: the tuples `b α`, `b β` of one affine jet `ĵ` in two
  honest charts are `JetTransitionRelated` at every codimension-one point `y` with `ρ(y) ∈ V α ∩ V β`
  (both directions of the previous theorem).
* `weightedOrder_affineJetCoord_chart_independent`: hence their weighted orders agree
  (`weightedOrder_chart_independent`).
* `exists_weightFunction_of_affineJet`: the integer weight function `w` of the affine jet
  (`exists_weightFunction_of_chartIndependent`).

Helper modules: `JetTransitionPolynomialLinearPart` (linear part of a weighted-homogeneous
polynomial, the jet transition polynomial, the matrices of inverse substitutions),
the restriction lemma for honest charts (a polynomial presentation of a graded quasi-coherent algebra on an
affine open restricts to a common basic open — Stacks 01I8), `GenericAffineJetPoint` (the constants
of the generic affine jet are germs at the generic point; `ĵ` lies over every open containing `η_C`).

Note that with a single matrix `g` for all weights the transition statement would be **false** — two honest charts
differ by an arbitrary graded automorphism of `Γ(V)[x_{i,q}]`, whose weight-`(q+1)` linear part depends on `q`
(`x^β_{i,q} = λ_q x^α_{i,q}`; for `n = 0`, `κ = 2`, `b_α = (t, 1)`, `t` a uniformizer at `y`, one needs
`c = 1/t² ∈ O_{C̃,y}`). Hence `JetTransitionStep` has `g : Fin κ → Matrix …`, which is what the consumer
`weightedOrder_chart_independent` uses (only the regularity of the weight-`q` coefficients).
-/
set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}

/-- The polynomial presentation of an honest chart, with variables indexed by `Fin (n+1) × Fin κ`
(`jetChart.IsHonest` renamed along `Equiv.ulift`). -/
theorem HonestJetChart.nonempty_polyPresentation {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ}
    {V : C.toScheme.Opens} (chart : HonestJetChart f κ V) :
    Nonempty ((jetAlgebra f κ).PolyPresentation (JetChartTransitionPoly.jetWt X.toVariety.dim κ) V
      chart.coords) := by
  obtain ⟨ε, -, -, hgr, hunit, hcoords, -, -⟩ := chart.honest
  let e := (MvPolynomial.renameEquiv Γ(C.toScheme, V)
    (Equiv.ulift : ULift.{u} (Fin (X.toVariety.dim + 1) × Fin κ) ≃
      Fin (X.toVariety.dim + 1) × Fin κ)).toRingEquiv
  refine ⟨⟨ε.trans e, fun r => ?_, fun p => ?_, fun m a ha => ?_⟩⟩
  · exact (congrArg e (hunit r)).trans (MvPolynomial.rename_C _ r)
  · exact (congrArg e (hcoords p)).trans (MvPolynomial.rename_X _ _)
  · exact JetChartTransitionPoly.isWeightedHomogeneous_rename_of_injective Equiv.ulift.injective
      ((hgr m a).mp ha)

theorem affineJetCoord_jetTransitionStep
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (ρ : FiniteCover k C)
    (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    (hĵ : ĵ ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom =
      ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)
    {Vα Vβ : C.toScheme.Opens} (chartα : HonestJetChart f κ Vα) (chartβ : HonestJetChart f κ Vβ)
    (hĵVα : (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ Vα))
    (hĵVβ : (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ Vβ))
    (bα bβ : Fin (X.toVariety.dim + 1) → Fin κ → ρ.source.toScheme.functionField)
    (hbα : ∀ (i : Fin (X.toVariety.dim + 1)) (q : Fin κ),
      bα i q = affineJetCoord ρ ĵ hĵVα _ (chartα.coords (i, q)))
    (hbβ : ∀ (i : Fin (X.toVariety.dim + 1)) (q : Fin κ),
      bβ i q = affineJetCoord ρ ĵ hĵVβ _ (chartβ.coords (i, q)))
    (y : ρ.source.toScheme) (hyα : ρ.hom.base y ∈ Vα) (hyβ : ρ.hom.base y ∈ Vβ) :
    JetTransitionStep bα bβ y := by
  classical
  have hint : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  have hCint : AlgebraicGeometry.IsIntegral C.toScheme := C.isIntegral
  -- a common basic open `V' = D(fα) = D(fβ)` around `ρ(y)`
  obtain ⟨fα, fβ, hff, hc⟩ := AlgebraicGeometry.exists_basicOpen_le_affine_inter
    chartα.isAffineOpen chartβ.isAffineOpen (ρ.hom.base y) ⟨hyα, hyβ⟩
  have hV'α : C.toScheme.basicOpen fα ≤ Vα := C.toScheme.basicOpen_le fα
  have hV'β : C.toScheme.basicOpen fα ≤ Vβ := by
    rw [hff]
    exact C.toScheme.basicOpen_le fβ
  have hηV' : genericPoint C.toScheme ∈ C.toScheme.basicOpen fα :=
    (genericPoint_specializes (ρ.hom.base y)).mem_open (C.toScheme.basicOpen fα).isOpen hc
  have hĵV' := top_le_preimage_of_genericPoint_mem ρ ĵ hĵ hηV'
  have hyV' : y ∈ ρ.hom ⁻¹ᵁ C.toScheme.basicOpen fα := hc
  -- the honest presentations and the transition polynomials on `V'`
  obtain ⟨Pα⟩ := chartα.nonempty_polyPresentation
  obtain ⟨Pβ⟩ := chartβ.nonempty_polyPresentation
  obtain ⟨T, T', hT, hT', hTe, -, hbind, hbind'⟩ := (jetAlgebra f κ).exists_transition
    (JetChartTransitionPoly.jetWt X.toVariety.dim κ) chartα.isAffineOpen chartβ.isAffineOpen Pα Pβ
    fα fβ rfl hff hV'α hV'β
  -- the coefficient homomorphisms `Γ(C, V') → O_{C̃,y} → K(C̃)`
  let θ : Γ(C.toScheme, C.toScheme.basicOpen fα) →+* ρ.source.toScheme.presheaf.stalk y :=
    (ρ.source.toScheme.presheaf.germ (ρ.hom ⁻¹ᵁ C.toScheme.basicOpen fα) y hyV').hom.comp
      (ρ.hom.app (C.toScheme.basicOpen fα)).hom
  let θK : Γ(C.toScheme, C.toScheme.basicOpen fα) →+* ρ.source.toScheme.functionField :=
    (algebraMap (ρ.source.toScheme.presheaf.stalk y) ρ.source.toScheme.functionField).comp θ
  -- `ĵ^♯` on `S(V')`, read in `K(C̃)`
  let Ψ : (jetAlgebra f κ).sectionsRing (C.toScheme.basicOpen fα) →+* ρ.source.toScheme.functionField :=
    ρ.source.toScheme.functionFieldIsoResidueField.inv.hom.comp (affineJetSectionsHom ĵ hĵV')
  have hΨunit : ∀ r, Ψ ((jetAlgebra f κ).sectionsUnitHom _ r) = θK r := fun r =>
    affineJetSectionsHom_unit_eq_germ ρ ĵ hĵ hĵV' y hyV' r
  have hΨα : ∀ p : Fin (X.toVariety.dim + 1) × Fin κ,
      Ψ ((jetAlgebra f κ).ofPiece _ _ ((jetAlgebra f κ).restrictCoords
        (JetChartTransitionPoly.jetWt X.toVariety.dim κ) hV'α chartα.coords p)) = bα p.1 p.2 := by
    intro p
    have e1 := (jetAlgebra f κ).sectionsRestrictHom_ofPiece hV'α
      (JetChartTransitionPoly.jetWt X.toVariety.dim κ p) (chartα.coords p)
    have e2 := affineJetSectionsHom_sectionsRestrictHom ĵ hV'α hĵV' hĵVα
      ((jetAlgebra f κ).ofPiece Vα (JetChartTransitionPoly.jetWt X.toVariety.dim κ p) (chartα.coords p))
    rw [hbα p.1 p.2, affineJetCoord_eq_affineJetSectionsHom ρ ĵ hĵVα]
    exact congrArg ρ.source.toScheme.functionFieldIsoResidueField.inv.hom
      ((congrArg (affineJetSectionsHom ĵ hĵV') e1.symm).trans e2)
  have hΨβ : ∀ p : Fin (X.toVariety.dim + 1) × Fin κ,
      Ψ ((jetAlgebra f κ).ofPiece _ _ ((jetAlgebra f κ).restrictCoords
        (JetChartTransitionPoly.jetWt X.toVariety.dim κ) hV'β chartβ.coords p)) = bβ p.1 p.2 := by
    intro p
    have e1 := (jetAlgebra f κ).sectionsRestrictHom_ofPiece hV'β
      (JetChartTransitionPoly.jetWt X.toVariety.dim κ p) (chartβ.coords p)
    have e2 := affineJetSectionsHom_sectionsRestrictHom ĵ hV'β hĵV' hĵVβ
      ((jetAlgebra f κ).ofPiece Vβ (JetChartTransitionPoly.jetWt X.toVariety.dim κ p) (chartβ.coords p))
    rw [hbβ p.1 p.2, affineJetCoord_eq_affineJetSectionsHom ρ ĵ hĵVβ]
    exact congrArg ρ.source.toScheme.functionFieldIsoResidueField.inv.hom
      ((congrArg (affineJetSectionsHom ĵ hĵV') e1.symm).trans e2)
  -- the key identity: `bβ i q = T (i, q)` evaluated at `bα` with coefficients through `θK`
  have hkey : ∀ (i : Fin (X.toVariety.dim + 1)) (q : Fin κ),
      bβ i q = MvPolynomial.eval₂ θK (fun p => bα p.1 p.2) (T (i, q)) := by
    intro i q
    rw [← hΨβ (i, q), ← hTe (i, q)]
    show Ψ (MvPolynomial.eval₂Hom ((jetAlgebra f κ).sectionsUnitHom _)
      (fun p => (jetAlgebra f κ).ofPiece _ _ ((jetAlgebra f κ).restrictCoords
        (JetChartTransitionPoly.jetWt X.toVariety.dim κ) hV'α chartα.coords p)) (T (i, q))) = _
    rw [← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]
    show MvPolynomial.eval₂ (Ψ.comp ((jetAlgebra f κ).sectionsUnitHom _))
      (fun p => Ψ ((jetAlgebra f κ).ofPiece _ _ ((jetAlgebra f κ).restrictCoords
        (JetChartTransitionPoly.jetWt X.toVariety.dim κ) hV'α chartα.coords p))) (T (i, q)) = _
    congr 1
    · exact RingHom.ext hΨunit
    · exact funext hΨα
  -- the matrices of weight-`(q+1)` linear parts and their inverses
  let G : Fin κ → Matrix (Fin (X.toVariety.dim + 1)) (Fin (X.toVariety.dim + 1))
      Γ(C.toScheme, C.toScheme.basicOpen fα) :=
    fun q => Matrix.of fun i j => (T (i, q)).coeff (Finsupp.single (j, q) 1)
  let G' : Fin κ → Matrix (Fin (X.toVariety.dim + 1)) (Fin (X.toVariety.dim + 1))
      Γ(C.toScheme, C.toScheme.basicOpen fα) :=
    fun q => Matrix.of fun j l => (T' (j, q)).coeff (Finsupp.single (l, q) 1)
  have hGG' : ∀ q, G q * G' q = 1 := fun q =>
    JetChartTransitionPoly.matrix_mul_eq_one_of_bind₁_eq_X q T T' hT hT' fun i => hbind (i, q)
  have hG'G : ∀ q, G' q * G q = 1 := fun q =>
    JetChartTransitionPoly.matrix_mul_eq_one_of_bind₁_eq_X q T' T hT' hT fun i => hbind' (i, q)
  refine ⟨fun q => (G q).map θ,
    fun i q => MvPolynomial.map θ (T (i, q) - MiyaokaMori.JetTransition.linearPart (T (i, q))),
    fun q => ?_, fun i q => ?_, fun i q => ?_⟩
  · refine ⟨⟨(G q).map θ, (G' q).map θ, ?_, ?_⟩, rfl⟩
    · rw [← Matrix.map_mul, hGG' q]
      exact Matrix.map_one θ (map_zero θ) (map_one θ)
    · rw [← Matrix.map_mul, hG'G q]
      exact Matrix.map_one θ (map_zero θ) (map_one θ)
  · exact JetChartTransitionPoly.isJetTransitionPolynomial_map θ
      (JetChartTransitionPoly.isJetTransitionPolynomial_sub_linearPart q (hT (i, q)))
  · rw [hkey i q, JetChartTransitionPoly.eval₂_eq_sum_linear_add_eval₂_sub_linearPart θK _ q (hT (i, q))]
    congr 1
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]

/-- **Jet transition between the coordinate tuples of one affine jet** (Lemma 3.1 of the paper,
`833--837`; (2.7) is `jet_transition_formula`). Let `ĵ` be a
`κ(η_{C̃})`-point of the affine jet scheme `J_κ^s` over `η_{C̃} ≫ ρ`, `(V α, chart α)`, `(V β, chart β)`
two affine honest jet charts, both containing the image of `ĵ`, and `b α`, `b β` the coordinate tuples
of `ĵ` in the two charts (`affineJetCoord`). Then at every point `y ∈ C̃` of coheight `1` with
`ρ(y) ∈ V α ∩ V β`, the tuples are related by a jet transition in both directions
(`JetTransitionRelated (b α) (b β) y`, ; the linear part `g q` of weight
`q + 1` may depend on `q`, see the module docstring).

Proof (`affineJetCoord_jetTransitionStep`, applied in both directions). Write `S := jetAlgebra f κ`,
`c := ρ(y) ∈ V α ∩ V β`. **(1)** `exists_basicOpen_le_affine_inter` gives `f_α ∈ Γ(V α)`, `f_β ∈ Γ(V β)`
with `V' := D(f_α) = D(f_β) ∋ c`; `V'` is a nonempty open of the irreducible `C`, so `η_C ∈ V'`, and `ĵ`
lies over `V'` because `π(ĵ) = ρ(η_{C̃}) = η_C` (`top_le_preimage_of_genericPoint_mem`). **(2)** Honesty
of each chart is a polynomial presentation `ε : S(V) ≃+* Γ(V)[x_p]` (`x_p ↦ coords p`, constants,
grading = weighted homogeneity; `HonestJetChart.nonempty_polyPresentation`, variables renamed from
`ULift` to `Fin (n+1) × Fin κ`). `GradedQCAlgebra.exists_transition` (quasi-coherence: `S(V') = S(V)[1/f]`,
Stacks 01I8) gives weighted-homogeneous `T_p, T'_p ∈ Γ(V')[x]` of weight `w p = p.2 + 1` with
`x^β_p|_{V'} = T_p(x^α|_{V'})`, `x^α_p|_{V'} = T'_p(x^β|_{V'})` in `S(V')` and `T_p[x ↦ T'] = X_p`,
`T'_p[x ↦ T] = X_p`. **(3)** `ĵ^♯ : S(V') → κ(η_{C̃}) → K(C̃)` (`affineJetSectionsHom`) is a ring
homomorphism with `ĵ^♯(ofPiece (x^α_p|_{V'})) = b α p` (restriction compatibility,
`affineJetSectionsHom_sectionsRestrictHom`) and `ĵ^♯(r) = algebraMap (O_{C̃,y}) K(C̃) (germ_y (ρ^♯ r))` on
constants `r ∈ Γ(V')` (`affineJetSectionsHom_unit_eq_germ`). Applying it to `x^β_{i,q}|_{V'} = T_{(i,q)}(x^α)`:
`b β i q = eval₂ θ_K (b α) (T_{(i,q)})` with `θ_K = algebraMap ∘ θ`, `θ := germ_y ∘ ρ^♯ : Γ(V') → O_{C̃,y}`.
**(4)** `eval₂_eq_sum_linear_add_eval₂_sub_linearPart`: `T_{(i,q)}` of weight `q + 1` evaluates to
`Σ_j θ_K(g_q)_{ij} · b α j q + P_{i,q}(b α)` with `(g_q)_{ij} = coeff_{X_{(j,q)}} T_{(i,q)}` and
`P_{i,q} := map θ (T_{(i,q)} − linearPart T_{(i,q)})`, a jet transition polynomial of weight `q + 1`
(`isJetTransitionPolynomial_sub_linearPart`, `isJetTransitionPolynomial_map`). **(5)** `g_q · g'_q = 1` and
`g'_q · g_q = 1` over `Γ(V')` from `T[x ↦ T'] = X` and `T'[x ↦ T] = X` (`matrix_mul_eq_one_of_bind₁_eq_X`),
hence `IsUnit (g_q.map θ)`. This is `JetTransitionStep (b α) (b β) y`; the reverse step is the same with
`α`, `β` exchanged. ∎

Edge cases: `κ = 0` — no coordinates, both steps hold with the empty matrices; `V α = V β` — `T = X`, `g = 1`,
`P = 0`; the hypothesis `coheight y = 1` is not used (the statement holds at every `y` over `V α ∩ V β`,
including the generic point), it is kept because the consumer needs it. -/
theorem affineJetCoord_jetTransitionRelated
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (ρ : FiniteCover k C)
    (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    (hĵ : ĵ ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom =
      ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)
    {Vα Vβ : C.toScheme.Opens} (chartα : HonestJetChart f κ Vα) (chartβ : HonestJetChart f κ Vβ)
    (hĵVα : (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ Vα))
    (hĵVβ : (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ Vβ))
    (bα bβ : Fin (X.toVariety.dim + 1) → Fin κ → ρ.source.toScheme.functionField)
    (hbα : ∀ (i : Fin (X.toVariety.dim + 1)) (q : Fin κ),
      bα i q = affineJetCoord ρ ĵ hĵVα _ (chartα.coords (i, q)))
    (hbβ : ∀ (i : Fin (X.toVariety.dim + 1)) (q : Fin κ),
      bβ i q = affineJetCoord ρ ĵ hĵVβ _ (chartβ.coords (i, q)))
    (y : ρ.source.toScheme) (hy : Order.coheight y = 1)
    (hyα : ρ.hom.base y ∈ Vα) (hyβ : ρ.hom.base y ∈ Vβ) :
    JetTransitionRelated bα bβ y :=
  ⟨affineJetCoord_jetTransitionStep f κ ρ ĵ hĵ chartα chartβ hĵVα hĵVβ bα bβ hbα hbβ y hyα hyβ,
   affineJetCoord_jetTransitionStep f κ ρ ĵ hĵ chartβ chartα hĵVβ hĵVα bβ bα hbβ hbα y hyβ hyα⟩

/-- **Chart independence of the weighted order of an affine jet** (Lemma 3.1 of the paper): the
weighted orders of the coordinate tuples of one affine jet in two honest charts agree at every
codimension-one point over both charts. From `affineJetCoord_jetTransitionRelated` and
`weightedOrder_chart_independent` (a coheight-`1` point of
a curve is closed, `AlgebraicGeometry.Intersection.isClosed_singleton_of_coheight_eq_one`). -/
theorem weightedOrder_affineJetCoord_chart_independent
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (ρ : FiniteCover k C)
    (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    (hĵ : ĵ ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom =
      ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)
    {Vα Vβ : C.toScheme.Opens} (chartα : HonestJetChart f κ Vα) (chartβ : HonestJetChart f κ Vβ)
    (hĵVα : (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ Vα))
    (hĵVβ : (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ Vβ))
    (bα bβ : Fin (X.toVariety.dim + 1) → Fin κ → ρ.source.toScheme.functionField)
    (hbα : ∀ (i : Fin (X.toVariety.dim + 1)) (q : Fin κ),
      bα i q = affineJetCoord ρ ĵ hĵVα _ (chartα.coords (i, q)))
    (hbβ : ∀ (i : Fin (X.toVariety.dim + 1)) (q : Fin κ),
      bβ i q = affineJetCoord ρ ĵ hĵVβ _ (chartβ.coords (i, q)))
    (hneα : ∃ i q, bα i q ≠ 0) (hneβ : ∃ i q, bβ i q ≠ 0)
    (y : ρ.source.toScheme) (hy : Order.coheight y = 1)
    (hyα : ρ.hom.base y ∈ Vα) (hyβ : ρ.hom.base y ∈ Vβ) :
    weightedOrderQ bα hneα y = weightedOrderQ bβ hneβ y := by
  have hclosed : IsClosed ({y} : Set ρ.source.toScheme) :=
    AlgebraicGeometry.Intersection.isClosed_singleton_of_coheight_eq_one
      (le_of_eq ρ.source.dim_one) y hy
  exact weightedOrder_chart_independent bα bβ hneα hneβ y hclosed
    (affineJetCoord_jetTransitionRelated f κ ρ ĵ hĵ chartα chartβ hĵVα hĵVβ bα bβ hbα hbβ y hy hyα hyβ)

/-- **The weight function of an affine jet** (Lemma 3.1 of the paper; step 1 of
`exists_basedJet_of_affineJet_frame`): for the coordinate tuples `b α` of one affine jet `ĵ` in a
family of honest charts covering `C`, all with roots, there is a finitely supported `w : C̃ → ℤ` with
`w y = weightedOrderQ (b α) y` whenever `ρ(y) ∈ V α`. Assembled from
`weightedOrder_affineJetCoord_chart_independent` and `exists_weightFunction_of_chartIndependent`. -/
theorem exists_weightFunction_of_affineJet
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (ρ : FiniteCover k C)
    (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    (hĵ : ĵ ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom =
      ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)
    {ι : Type u} {V : ι → C.toScheme.Opens}
    (chart : ∀ α, HonestJetChart f κ (V α))
    (hcover : ∀ c : C.toScheme, ∃ α, c ∈ V α)
    (hĵV : ∀ α, (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V α))
    (b : ι → Fin (X.toVariety.dim + 1) → Fin κ → ρ.source.toScheme.functionField)
    (hb : ∀ α (i : Fin (X.toVariety.dim + 1)) (q : Fin κ),
      b α i q = affineJetCoord ρ ĵ (hĵV α) _ ((chart α).coords (i, q)))
    (hne : ∀ α, ∃ i q, b α i q ≠ 0)
    (hroot : ∀ α (i : Fin (X.toVariety.dim + 1)) (q : Fin κ), b α i q ≠ 0 →
      ∃ c : ρ.source.toScheme.functionField, c ^ ((q : ℕ) + 1) = b α i q) :
    ∃ w : ρ.source.toScheme → ℤ, (Function.support w).Finite ∧
      ∀ α (y : ρ.source.toScheme), ρ.hom.base y ∈ V α →
        (w y : ℚ) = weightedOrderQ (b α) (hne α) y :=
  exists_weightFunction_of_chartIndependent ρ hcover b hne hroot fun α β y hy hyα hyβ =>
    weightedOrder_affineJetCoord_chart_independent f κ ρ ĵ hĵ (chart α) (chart β) (hĵV α) (hĵV β)
      (b α) (b β) (hb α) (hb β) (hne α) (hne β) y hy hyα hyβ

end
