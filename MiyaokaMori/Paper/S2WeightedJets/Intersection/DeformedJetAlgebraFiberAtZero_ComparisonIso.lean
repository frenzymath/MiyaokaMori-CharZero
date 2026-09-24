import MiyaokaMori.Prelude
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraFiberAtZero_Comparison
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraFiberAtZero_FiberChart
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraFiberAtZero_IsoOfSectionsBijective
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymSectionsRingEquivSym
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraLWP_HomSectionsRing
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01y1
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ic

/-! # The comparison morphism `weightedSymAlgebra V ⟶ s₀^*R` is an isomorphism

The comparison morphism from the weighted symmetric algebra to the fiber at `λ = 0` of the Rees deformation is
bijective on the section ring over every chart of a weighted-polynomial atlas with the jet weights, hence an
isomorphism of graded quasi-coherent algebras (Lemma 2.3 of the paper, "removing the nonlinear
terms": the fiber at `λ = 0` is the weighted projectivization of copies of `E`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry DirectSum

noncomputable section

/-! ## §A Pure algebra -/

namespace MvPolynomial

variable {σ : Type*} {B : Type*} [CommRing B]

/-- The linear part of a weighted-homogeneous polynomial of weight `m` is a linear form in the variables of weight `m`. -/
theorem homogeneousComponent_one_mem_span_X_of_isWeightedHomogeneous (w : σ → ℕ) {m : ℕ} {P : MvPolynomial σ B}
    (hP : P.IsWeightedHomogeneous w m) :
    homogeneousComponent 1 P ∈ Submodule.span B (X '' {s | w s = m}) := by
  classical
  have h1 : homogeneousComponent 1 P ∈ Submodule.span B (Set.range X) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact homogeneousComponent_isHomogeneous 1 P
  have hwP : (homogeneousComponent 1 P).IsWeightedHomogeneous w m := fun d hd => by
    refine hP fun h0 => hd ?_
    rw [coeff_homogeneousComponent, h0, ite_self]
  have h2 : weightedHomogeneousComponent w m (homogeneousComponent 1 P) = homogeneousComponent 1 P := by
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule B w m _).2 hwP), if_pos rfl]
  rw [← h2]
  refine Submodule.span_induction (p := fun q _ => weightedHomogeneousComponent w m q ∈
    Submodule.span B (X '' {s | w s = m})) ?_ ?_ ?_ ?_ h1
  · rintro _ ⟨s, rfl⟩
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule B w (w s) _).2
      (isWeightedHomogeneous_X B w s))]
    split_ifs with h
    · exact Submodule.subset_span ⟨s, h.symm, rfl⟩
    · exact zero_mem _
  · rw [map_zero]; exact zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]; exact add_mem ha hb
  · intro c a _ ha
    rw [map_smul]; exact Submodule.smul_mem _ c ha

end MvPolynomial

namespace WeightedSym

variable {B : Type*} [CommRing B] {σ : Type*} {r : ℕ} {W : Fin r → Type*} [∀ q, AddCommGroup (W q)] [∀ q, Module B (W q)]

/-- **A `B`-algebra map `Sym_B(⊕_q W_q) → B[y_s]` whose restriction to each `W_q` is injective with image the linear forms in
the variables `y_s`, `qOf s = q`, is bijective.** Proof: choose `w_s ∈ W_{qOf s}` with `ψ(w_s) = y_s`; the algebra map
`g := aeval (s ↦ gen (w_s)) : B[y_s] → Sym` is a two-sided inverse: `ψ ∘ g = id` on the generators `y_s`, and `g ∘ ψ = id`
on the generators `gen_q v` because `ψ(gen_q v)` is a linear form `Σ c_s y_s` in the variables of index `q`, so
`g(ψ(gen_q v)) = gen_q (Σ c_s w_s)` and `ψ(gen_q (Σ c_s w_s)) = ψ(gen_q v)` forces `Σ c_s w_s = v` by injectivity. -/
theorem algHom_bijective_of_gen (qOf : σ → Fin r) (ψ : SymmetricAlgebra B (⨁ q, W q) →ₐ[B] MvPolynomial σ B)
    (hinj : ∀ q, Function.Injective (ψ.toLinearMap ∘ₗ WeightedSym.gen B W q))
    (hX : ∀ s, MvPolynomial.X s ∈ LinearMap.range (ψ.toLinearMap ∘ₗ WeightedSym.gen B W (qOf s)))
    (hlin : ∀ q, LinearMap.range (ψ.toLinearMap ∘ₗ WeightedSym.gen B W q) ≤
      Submodule.span B (MvPolynomial.X '' {s | qOf s = q})) :
    Function.Bijective ψ := by
  classical
  simp only [LinearMap.mem_range] at hX
  choose wOf hwOf using hX
  let g : MvPolynomial σ B →ₐ[B] SymmetricAlgebra B (⨁ q, W q) :=
    MvPolynomial.aeval fun s => WeightedSym.gen B W (qOf s) (wOf s)
  have hgX : ∀ s, g (MvPolynomial.X s) = WeightedSym.gen B W (qOf s) (wOf s) := fun s => MvPolynomial.aeval_X _ s
  have hψg : ∀ P, ψ (g P) = P := by
    intro P
    have : ψ.comp g = AlgHom.id B _ := MvPolynomial.algHom_ext fun s => by
      rw [AlgHom.comp_apply, AlgHom.id_apply, hgX]
      exact hwOf s
    exact AlgHom.congr_fun this P
  have key : ∀ (q : Fin r) (v : W q), g ((ψ.toLinearMap ∘ₗ WeightedSym.gen B W q) v) = WeightedSym.gen B W q v := by
    intro q v
    have hv := hlin q (LinearMap.mem_range_self _ v)
    have hind : ∀ P ∈ Submodule.span B (MvPolynomial.X '' {s | qOf s = q}),
        ∃ v' : W q, (ψ.toLinearMap ∘ₗ WeightedSym.gen B W q) v' = P ∧ g P = WeightedSym.gen B W q v' := by
      intro P hP
      refine Submodule.span_induction (p := fun P _ => ∃ v' : W q,
        (ψ.toLinearMap ∘ₗ WeightedSym.gen B W q) v' = P ∧ g P = WeightedSym.gen B W q v') ?_ ?_ ?_ ?_ hP
      · rintro _ ⟨s, hs, rfl⟩
        have hs' : qOf s = q := hs
        subst hs'
        exact ⟨wOf s, hwOf s, hgX s⟩
      · exact ⟨0, by rw [map_zero], by rw [map_zero, map_zero]⟩
      · rintro x y _ _ ⟨v₁, h₁, g₁⟩ ⟨v₂, h₂, g₂⟩
        exact ⟨v₁ + v₂, by rw [map_add, h₁, h₂], by rw [map_add, g₁, g₂, map_add]⟩
      · rintro c x _ ⟨v₁, h₁, g₁⟩
        exact ⟨c • v₁, by rw [map_smul, h₁], by rw [map_smul, g₁, map_smul]⟩
    obtain ⟨v', hv', hg⟩ := hind _ hv
    rw [hg]
    exact congrArg _ (hinj q hv')
  have hgψ : ∀ a, g (ψ a) = a := by
    intro a
    have : g.comp ψ = AlgHom.id B _ := by
      apply SymmetricAlgebra.algHom_ext
      apply DirectSum.linearMap_ext
      intro q
      ext v
      exact key q v
    exact AlgHom.congr_fun this a
  exact Function.bijective_iff_has_inverse.2 ⟨g, hgψ, hψg⟩

end WeightedSym

/-! ## §B A morphism of graded QC algebras bijective on the section ring is bijective on every piece -/

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

theorem Hom.app_app_bijective_of_sectionsRingHom_bijective {X : AlgebraicGeometry.Scheme.{u}} {S T : X.GradedQCAlgebra}
    (φ : S ⟶ T) (U : X.Opens) (h : Function.Bijective (φ.sectionsRingHom U)) (m : ℕ) :
    Function.Bijective ((φ.app m).app U) := by
  constructor
  · intro a b hab
    apply S.ofPiece_injective U m
    apply h.1
    rw [φ.sectionsRingHom_ofPiece U m a, φ.sectionsRingHom_ofPiece U m b, hab]
  · intro b
    obtain ⟨x, hx⟩ := h.2 (T.ofPiece U m b)
    refine ⟨S.component U m x, ?_⟩
    rw [← φ.sectionsRingHom_component U m x, hx]
    exact T.component_ofPiece U m b

/-! ## §C The comparison morphism is bijective on sections over the charts -/

namespace reesDeformation

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)
variable {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
variable {σ : Type u} {w : σ → ℕ} (𝒜 : S.toGradedAffineAlgebra.WeightedPolynomialAtlas w) (hw : ∀ s, 0 < w s)
variable {r : ℕ} (V : Fin r → X.Modules) [∀ q, (V q).IsLocallyFree] [∀ q, (V q).IsFiniteType]
  (e : ∀ q : Fin r, AlgebraicGeometry.Scheme.Modules.dual (V q) ≅
    CategoryTheory.Limits.cokernel (S.irrelevantPow 2 (q.1 + 1)).2)
  (qOf : σ → Fin r) (hqOf : ∀ s, w s = qOf s + 1)

include hw qOf hqOf in
/-- **`Φ` is bijective on the section ring over every chart `U_i`** (the jet weights `w s = qOf s + 1`). -/
theorem comparisonHom_sectionsRingHom_bijective (i : 𝒜.I) :
    Function.Bijective ((comparisonHom S (k := k) V e).sectionsRingHom (𝒜.chart i).toOpens) := by
  classical
  let χ := S.fiberChartEquiv (k := k) 𝒜 hw i
  let Φr := (comparisonHom S (k := k) V e).sectionsRingHom (𝒜.chart i).toOpens
  let sl := AlgebraicGeometry.Scheme.weightedSymAlgebra.symLiftHom V (𝒜.chart i).toOpens
  let ψ : SymmetricAlgebra Γ(X, (𝒜.chart i).toOpens)
      (⨁ q, AlgebraicGeometry.Scheme.weightedSymAlgebra.genSectionsModule V (𝒜.chart i).toOpens q)
      →ₐ[Γ(X, (𝒜.chart i).toOpens)] MvPolynomial σ Γ(X, (𝒜.chart i).toOpens) :=
    { toRingHom := χ.toRingHom.comp (Φr.comp sl)
      commutes' := fun c => by
        show χ (Φr (sl (algebraMap _ _ c))) = algebraMap _ _ c
        rw [AlgebraicGeometry.Scheme.weightedSymAlgebra.symLiftHom_algebraMap, Hom.sectionsRingHom_sectionsUnitHom,
          S.fiberChartEquiv_sectionsUnitHom 𝒜 hw i, MvPolynomial.algebraMap_eq] }
  -- `ψ` on the generators
  have hgen : ∀ (q : Fin r) (v : Γ(AlgebraicGeometry.Scheme.Modules.dual (V q), (𝒜.chart i).toOpens)),
      ψ (WeightedSym.gen Γ(X, (𝒜.chart i).toOpens)
          (AlgebraicGeometry.Scheme.weightedSymAlgebra.genSectionsModule V (𝒜.chart i).toOpens) q v) =
        χ ((S.reesDeformation.restrictToLambda (0 : k)).ofPiece (𝒜.chart i).toOpens (q.1 + 1)
          ((linearPieceToFiber S (k := k) q).app (𝒜.chart i).toOpens ((e q).hom.app (𝒜.chart i).toOpens v))) := by
    intro q v
    show χ (Φr (sl (WeightedSym.gen _ _ q v))) = _
    rw [AlgebraicGeometry.Scheme.weightedSymAlgebra.symLiftHom_gen]
    show χ (Φr ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece (𝒜.chart i).toOpens (q.1 + 1)
      ((AlgebraicGeometry.Scheme.weightedSymAlgebra.genIncl V q).app (𝒜.chart i).toOpens v))) = _
    erw [Hom.sectionsRingHom_ofPiece]
    rw [comparisonHom_app_app_genIncl_app]
  -- sections of the cokernel projection over the affine chart are surjective
  have hqcL : ∀ q : Fin r, (CategoryTheory.Limits.cokernel (S.irrelevantPow 2 (q.1 + 1)).2).IsQuasicoherent := fun q => by
    have := S.irrelevantPow_isQuasicoherent 2 (q.1 + 1)
    have := S.quasicoherent (q.1 + 1)
    exact (Modules.isQuasicoherent_kernel (S.irrelevantPow 2 (q.1 + 1)).2).2
  have hsurj : ∀ q : Fin r, Function.Surjective
      ((CategoryTheory.Limits.cokernel.π (S.irrelevantPow 2 (q.1 + 1)).2).app (𝒜.chart i).toOpens) := fun q => by
    have := S.quasicoherent (q.1 + 1)
    have := hqcL q
    exact Stacks01y1Aux.surjective_app_of_epi _ (𝒜.chart i).2
  -- the value of `ψ` on a generator, through the fibre chart
  have hval : ∀ (q : Fin r) (v : Γ(AlgebraicGeometry.Scheme.Modules.dual (V q), (𝒜.chart i).toOpens))
      (x : Γ(S.part (q.1 + 1), (𝒜.chart i).toOpens)),
      (CategoryTheory.Limits.cokernel.π (S.irrelevantPow 2 (q.1 + 1)).2).app (𝒜.chart i).toOpens x =
        (e q).hom.app (𝒜.chart i).toOpens v →
      ψ (WeightedSym.gen Γ(X, (𝒜.chart i).toOpens)
          (AlgebraicGeometry.Scheme.weightedSymAlgebra.genSectionsModule V (𝒜.chart i).toOpens) q v) =
        MvPolynomial.homogeneousComponent 1 (𝒜.equiv i (S.ofPiece (𝒜.chart i).toOpens (q.1 + 1) x)) := by
    intro q v x hx
    rw [hgen, ← hx]
    exact S.fiberChartEquiv_ofPiece_linearPieceToFiber 𝒜 hw i q.1 x
  -- (α) injectivity on each `W_q`
  have hinj : ∀ q, Function.Injective (ψ.toLinearMap ∘ₗ WeightedSym.gen Γ(X, (𝒜.chart i).toOpens)
      (AlgebraicGeometry.Scheme.weightedSymAlgebra.genSectionsModule V (𝒜.chart i).toOpens) q) := by
    intro q v₁ v₂ h
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at h
    rw [hgen, hgen] at h
    have h1 := χ.injective h
    have h2 := (S.reesDeformation.restrictToLambda (0 : k)).ofPiece_injective (𝒜.chart i).toOpens (q.1 + 1) h1
    have hqcT := (S.reesDeformation.restrictToLambda (0 : k)).quasicoherent (q.1 + 1)
    have hqcL' := hqcL q
    have h3 := Stacks01y1Aux.injective_app_of_mono (linearPieceToFiber S (k := k) q) (𝒜.chart i).2 h2
    have h4 := congrArg ((e q).inv.app (𝒜.chart i).toOpens) h3
    rwa [Modules.modIso_inv_app_hom_app, Modules.modIso_inv_app_hom_app] at h4
  -- (β) every variable `y_s` is hit from `W_{qOf s}`
  have hX : ∀ s, MvPolynomial.X s ∈ LinearMap.range (ψ.toLinearMap ∘ₗ WeightedSym.gen Γ(X, (𝒜.chart i).toOpens)
      (AlgebraicGeometry.Scheme.weightedSymAlgebra.genSectionsModule V (𝒜.chart i).toOpens) (qOf s)) := by
    intro s
    have hXs : (MvPolynomial.X s : MvPolynomial σ Γ(X, (𝒜.chart i).toOpens)).IsWeightedHomogeneous w (qOf s + 1) := by
      have := MvPolynomial.isWeightedHomogeneous_X (R := Γ(X, (𝒜.chart i).toOpens)) w s
      rwa [hqOf s] at this
    have hmem := 𝒜.symm_mem i hXs
    set x := S.component (𝒜.chart i).toOpens (qOf s + 1) ((𝒜.equiv i).symm (MvPolynomial.X s)) with hxdef
    have hx : S.ofPiece (𝒜.chart i).toOpens (qOf s + 1) x = (𝒜.equiv i).symm (MvPolynomial.X s) :=
      (S.mem_sectionsGrading_iff (𝒜.chart i).toOpens (qOf s + 1) _).1 hmem
    refine ⟨(e (qOf s)).inv.app (𝒜.chart i).toOpens
      ((CategoryTheory.Limits.cokernel.π (S.irrelevantPow 2 (qOf s + 1)).2).app (𝒜.chart i).toOpens x), ?_⟩
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [hval (qOf s) _ x (Modules.modIso_hom_app_inv_app (e (qOf s)) (𝒜.chart i).toOpens _).symm, hx,
      RingEquiv.apply_symm_apply, MvPolynomial.homogeneousComponent_of_mem
        ((MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X _ s)), if_pos rfl]
  -- (γ) the image of `W_q` consists of linear forms in the variables of index `q`
  have hlin : ∀ q, LinearMap.range (ψ.toLinearMap ∘ₗ WeightedSym.gen Γ(X, (𝒜.chart i).toOpens)
      (AlgebraicGeometry.Scheme.weightedSymAlgebra.genSectionsModule V (𝒜.chart i).toOpens) q) ≤
      Submodule.span Γ(X, (𝒜.chart i).toOpens) (MvPolynomial.X '' {s | qOf s = q}) := by
    intro q
    rintro _ ⟨v, rfl⟩
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    obtain ⟨x, hx⟩ := hsurj q ((e q).hom.app (𝒜.chart i).toOpens v)
    rw [hval q v x hx]
    have hP : (𝒜.equiv i (S.ofPiece (𝒜.chart i).toOpens (q.1 + 1) x)).IsWeightedHomogeneous w (q.1 + 1) :=
      𝒜.equiv_isWeightedHomogeneous i ⟨x, rfl⟩
    have hset : {s | w s = q.1 + 1} = {s | qOf s = q} := by
      ext s
      simp only [Set.mem_ofPred_eq, hqOf s]
      exact ⟨fun h => Fin.ext (Nat.succ_injective h), fun h => by rw [h]⟩
    rw [← hset]
    exact MvPolynomial.homogeneousComponent_one_mem_span_X_of_isWeightedHomogeneous w hP
  have hψ : Function.Bijective ψ := WeightedSym.algHom_bijective_of_gen qOf ψ hinj hX hlin
  have h1 : Function.Bijective (⇑χ ∘ (⇑Φr ∘ ⇑sl)) := hψ
  have h2 : Function.Bijective (⇑Φr ∘ ⇑sl) := (Function.Bijective.of_comp_iff' χ.bijective _).1 h1
  exact (Function.Bijective.of_comp_iff _
    (AlgebraicGeometry.Scheme.weightedSymAlgebra.symLiftHom_bijective V (𝒜.chart i).2)).1 h2

include 𝒜 hw qOf hqOf in
/-- **The comparison morphism is an isomorphism** for a weighted-polynomial atlas with the jet weights `w s = qOf s + 1`
(criterion `isIso_of_affineOpens_cover_bijective` on the charts of `𝒜`). -/
theorem comparisonHom_isIso : IsIso (comparisonHom S (k := k) V e) :=
  isIso_of_affineOpens_cover_bijective _ (fun i => (𝒜.chart i).toOpens) (fun i => (𝒜.chart i).2) 𝒜.covers
    fun m i => Hom.app_app_bijective_of_sectionsRingHom_bijective _ _
      (comparisonHom_sectionsRingHom_bijective S 𝒜 hw V e qOf hqOf i) m

end reesDeformation

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
