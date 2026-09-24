import MiyaokaMori.Prelude
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraFiberAtZero_Generators
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraFiberAtZero_ReesAtlas
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.RestrictToLambdaBundleFamilyTransition_PullbackSections

/-! # The fibre chart of `T = s₀^*R`

The chart isomorphisms `χ_i : T(U_i) ≃+* Γ(U_i)[y_s]` of the fibre `T = s₀^*R` at `λ = 0` of the Rees deformation on
the charts `U_i` of a weighted-polynomial atlas, and the description of the images of the generator maps under them;
used to show that the comparison morphism `weightedSymAlgebra V ⟶ T` is an isomorphism
(`DeformedJetAlgebraFiberAtZero_ComparisonIso`; Lemma 2.3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## §A Pure algebra: the Rees lift `Σ_α t^{|α|-p} c_α y^α` of a polynomial -/

namespace MvPolynomial

variable {σ : Type*} {B : Type*} [CommRing B]

/-- `reesLift t p P := Σ_α t^{|α| - p} · c_α · y^α` for `P = Σ_α c_α x^α`. For `P` weighted-homogeneous of weight `j` with
all monomials of degree `≥ p` this is the unique `Q` with `reesRescale t w Q = t^{j-p} · P`. -/
noncomputable def reesLift (t : B) (p : ℕ) (P : MvPolynomial σ B) : MvPolynomial σ B :=
  ∑ α ∈ P.support, monomial α (t ^ (α.degree - p) * coeff α P)

theorem coeff_reesLift (t : B) (p : ℕ) (P : MvPolynomial σ B) (β : σ →₀ ℕ) :
    coeff β (reesLift t p P) = t ^ (β.degree - p) * coeff β P := by
  classical
  unfold reesLift
  rw [coeff_sum]
  simp only [coeff_monomial]
  by_cases hβ : β ∈ P.support
  · rw [Finset.sum_eq_single β (fun α _ hαβ => if_neg hαβ) (fun h => absurd hβ h), if_pos rfl]
  · rw [Finset.sum_eq_zero (fun α hα => if_neg (fun (h : α = β) => hβ (h ▸ hα))), notMem_support_iff.mp hβ, mul_zero]

/-- `reesRescale t w (reesLift t p P) = t^{j-p} · P` for `P` of weight `j` with all monomials of degree `≥ p`. -/
theorem reesRescale_reesLift (t : B) (w : σ → ℕ) (hw : ∀ s, 0 < w s) {p j : ℕ} (P : MvPolynomial σ B)
    (hP : ∀ α ∈ P.support, Finsupp.weight w α = j ∧ p ≤ α.degree) :
    reesRescale t w (reesLift t p P) = C (t ^ (j - p)) * P := by
  ext β
  rw [coeff_reesRescale, coeff_reesLift, coeff_C_mul]
  by_cases hβ : β ∈ P.support
  · obtain ⟨h1, h2⟩ := hP β hβ
    have h3 : β.degree ≤ j := h1 ▸ degree_le_weight_of_pos w hw β
    have h4 : β.degree - p + (j - β.degree) = j - p := by omega
    rw [weight_sub_one_eq w hw β, h1, mul_right_comm, ← pow_add, h4]
  · rw [notMem_support_iff.mp hβ, mul_zero, zero_mul, mul_zero]

/-- Along a ring map killing `t`, the Rees lift becomes the degree-`p` homogeneous component. -/
theorem map_reesLift_of_eq_zero {B' : Type*} [CommRing B'] (f : B →+* B') {t : B} (hf : f t = 0) (p : ℕ)
    (P : MvPolynomial σ B) (hP : ∀ α ∈ P.support, p ≤ α.degree) :
    map f (reesLift t p P) = homogeneousComponent p (map f P) := by
  ext β
  rw [coeff_map, coeff_reesLift, coeff_homogeneousComponent, coeff_map, map_mul, map_pow, hf]
  by_cases hβ : β ∈ P.support
  · have h := hP β hβ
    by_cases hd : β.degree = p
    · rw [if_pos hd, hd, Nat.sub_self, pow_zero, one_mul]
    · rw [if_neg hd, zero_pow (by omega), zero_mul]
  · rw [notMem_support_iff.mp hβ, map_zero, mul_zero]
    split_ifs <;> rfl

end MvPolynomial

/-! ## §B The section `s₀ : X → A¹_X` against `π : A¹_X → X` on opens and sections -/

namespace AlgebraicGeometry.Scheme.affineLineOver

variable {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]

private theorem sectionAt_comp_toBase_fiberChart (t : k) :
    AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t ≫ AlgebraicGeometry.Scheme.affineLineOver.toBase X = 𝟙 X :=
  AlgebraicGeometry.AffineSpace.homOfVector_over _ _

/-- `U ⊆ s_t⁻¹(π⁻¹U)` (indeed equality, since `π ∘ s_t = 𝟙`). -/
theorem le_sectionAt_preimage_toBase_preimage (t : k) (U : X.Opens) :
    U ≤ AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t ⁻¹ᵁ
      (AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U) := by
  intro x hx
  show (AlgebraicGeometry.Scheme.affineLineOver.toBase X).base
    ((AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t).base x) ∈ U
  have h := congrArg (fun f : X ⟶ X => f.base x) (sectionAt_comp_toBase_fiberChart (X := X) t)
  simp only [AlgebraicGeometry.Scheme.Hom.comp_base, AlgebraicGeometry.Scheme.Hom.id_base] at h
  rw [show (AlgebraicGeometry.Scheme.affineLineOver.toBase X).base
      ((AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t).base x) = x from h]
  exact hx

/-- `s_t^♯ ∘ π^♯ = id` on `Γ(X, U)`. -/
theorem sectionAt_appLE_toBase_appLE (t : k) (U : X.Opens)
    (h : U ≤ AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t ⁻¹ᵁ
      (AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U)) (b : Γ(X, U)) :
    ((AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t).appLE
        (AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U) U h).hom
      (((AlgebraicGeometry.Scheme.affineLineOver.toBase X).appLE U
        (AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U) le_rfl).hom b) = b := by
  have key : ∀ (g : X ⟶ X) (hg : g = 𝟙 X) (e : U ≤ g ⁻¹ᵁ U), (g.appLE U U e).hom b = b := by
    rintro g rfl e
    have : (𝟙 X : X ⟶ X).appLE U U e = (𝟙 X : X ⟶ X).appLE U ((𝟙 X : X ⟶ X) ⁻¹ᵁ U) le_rfl := rfl
    rw [this, AlgebraicGeometry.Scheme.Hom.appLE_eq_app, AlgebraicGeometry.Scheme.Hom.id_app]
    rfl
  rw [← CommRingCat.comp_apply, AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE]
  exact key _ (sectionAt_comp_toBase_fiberChart t) _

/-- `s₀^♯ λ = 0` on the chart `π⁻¹U`. -/
theorem sectionAt_zero_appLE_lambdaRes (U : X.Opens)
    (h : U ≤ AlgebraicGeometry.Scheme.affineLineOver.sectionAt X (0 : k) ⁻¹ᵁ
      (AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U)) :
    ((AlgebraicGeometry.Scheme.affineLineOver.sectionAt X (0 : k)).appLE
        (AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U) U h).hom
      (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U)) = 0 := by
  have h0 := AlgebraicGeometry.Scheme.affineLineOver.sectionAt_zero_appTop_coord_pow_succ (k := k) X 0
  rw [zero_add, pow_one] at h0
  have e := AlgebraicGeometry.Scheme.Hom.map_appLE (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X (0 : k))
    (U := AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U) (V := U) h
    (CategoryTheory.homOfLE (le_top : AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U ≤ ⊤)).op
  have e' := ConcreteCategory.congr_hom e (AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1)) :
    Γ(AlgebraicGeometry.Scheme.affineLineOver X, ⊤))
  erw [CommRingCat.comp_apply] at e'
  refine e'.trans ?_
  rw [AlgebraicGeometry.Scheme.Hom.appLE]
  erw [CommRingCat.comp_apply, h0]
  exact map_zero _

end AlgebraicGeometry.Scheme.affineLineOver

/-! ## §C `η⁻¹ : M → s_t^*π^*M` on sections -/

namespace AlgebraicGeometry.Scheme.Modules

/-- Transport along an equality of morphisms preserves pulled-back sections (`eqToHom` form). -/
theorem eqToHom_congrArg_pullback_app_app {X Y : AlgebraicGeometry.Scheme.{u}} {f f' : X ⟶ Y} (e : f = f')
    (M : Y.Modules) (U : Y.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ U) (h' : W ≤ f' ⁻¹ᵁ U) (s : Γ(M, U)) :
    ((eqToHom (congrArg AlgebraicGeometry.Scheme.Modules.pullback e)).app M).app W (pullbackSectionsOn f M U W h s) =
      pullbackSectionsOn f' M U W h' s := by
  subst e
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)
variable {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]

/-- **`η⁻¹` on sections**: the inverse of `s_t^* ∘ π^* ≅ 𝟭` sends `m ∈ Γ(U, M)` to the pullback along `s_t` of the pullback
along `π` of `m`. -/
theorem pullbackToBaseCompPullbackSectionAtIso_inv_app_app (t : k) (M : X.Modules) (U : X.Opens)
    (h : U ≤ affineLineOver.sectionAt X t ⁻¹ᵁ (affineLineOver.toBase X ⁻¹ᵁ U)) (m : Γ(M, U)) :
    ((pullbackToBaseCompPullbackSectionAtIso (X := X) t).inv.app M).app U m =
      Modules.pullbackSectionsOn (affineLineOver.sectionAt X t) ((Modules.pullback (affineLineOver.toBase X)).obj M)
        (affineLineOver.toBase X ⁻¹ᵁ U) U h (Modules.pullbackUnitHom (affineLineOver.toBase X) M U m) := by
  have hπ : affineLineOver.sectionAt X t ≫ affineLineOver.toBase X = 𝟙 X := affineLineOver.sectionAt_comp_toBase_fiberChart t
  have h1 : ((Modules.pullbackId X).inv.app M).app U m = Modules.pullbackUnitHom (𝟙 X) M U m := by
    have e1 := Modules.pullbackId_hom_app_unit_app_apply X M U m
    have e2 := Modules.modIso_inv_app_hom_app ((Modules.pullbackId X).app M) U (Modules.pullbackUnitHom (𝟙 X) M U m)
    refine Eq.trans ?_ e2
    exact congrArg (((Modules.pullbackId X).inv.app M).app U) e1.symm
  have h2 : ((eqToIso (congrArg Modules.pullback hπ)).inv.app M).app U (Modules.pullbackUnitHom (𝟙 X) M U m) =
      Modules.pullbackSectionsOn (affineLineOver.sectionAt X t ≫ affineLineOver.toBase X) M U U h m := by
    rw [← Modules.pullbackSectionsOn_self (𝟙 X) M U m]
    exact Modules.eqToHom_congrArg_pullback_app_app hπ.symm M U U le_rfl h m
  have h3 := Modules.pullbackComp_inv_app_pullbackSectionsOn (affineLineOver.sectionAt X t) (affineLineOver.toBase X)
    M U U h h m
  show ((Modules.pullbackComp (affineLineOver.sectionAt X t) (affineLineOver.toBase X)).inv.app M).app U
    (((eqToIso (congrArg Modules.pullback hπ)).inv.app M).app U (((Modules.pullbackId X).inv.app M).app U m)) = _
  rw [h1, h2]
  exact h3

/-- **`fiberGen` on sections**: the fibre generator sends `x ∈ Γ(U, I^{(p)}_j)` to the pullback along `s₀` of the Rees
generator applied to the pullback of `x` along `π` (i.e. of `λ^{j-p}·π^*x ∈ Γ(π⁻¹U, R_j)`). -/
theorem fiberGen_app (j : ℕ) (p : Fin (j + 1)) (U : X.Opens)
    (h : U ≤ affineLineOver.sectionAt X (0 : k) ⁻¹ᵁ (affineLineOver.toBase X ⁻¹ᵁ U))
    (x : Γ((S.irrelevantPow p.1 j).1, U)) :
    (fiberGen S (k := k) j p).app U x =
      Modules.pullbackSectionsOn (affineLineOver.sectionAt X (0 : k)) (part S j) (affineLineOver.toBase X ⁻¹ᵁ U) U h
        ((reesGen S j p).app (affineLineOver.toBase X ⁻¹ᵁ U)
          (Modules.pullbackUnitHom (affineLineOver.toBase X) (S.irrelevantPow p.1 j).1 U x)) := by
  show ((Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (reesGen S j p)).app U
    (((pullbackToBaseCompPullbackSectionAtIso (X := X) (0 : k)).inv.app (S.irrelevantPow p.1 j).1).app U x) = _
  rw [pullbackToBaseCompPullbackSectionAtIso_inv_app_app (0 : k) _ U h x]
  exact Modules.pullback_map_app_pullbackSectionsOn_bc (affineLineOver.sectionAt X (0 : k)) (reesGen S j p) _ U h _

/-- `ι₁ ≫ π₂ ≫ γ_q = fiberGen S (q+1) 1`: the generator map on the class of `ι₁ x'` is the fibre generator on `x'`. -/
theorem irrelevantPow_one_snd_comp_π_comp_linearPieceToFiber (q : ℕ) :
    (S.irrelevantPow 1 (q + 1)).2 ≫ cokernel.π (S.irrelevantPow 2 (q + 1)).2 ≫ linearPieceToFiber S (k := k) q =
      fiberGen S (k := k) (q + 1) ⟨1, by omega⟩ := by
  unfold linearPieceToFiber
  rw [← S.π_comp_linearPieceIso_hom_assoc (q + 1) (Nat.succ_pos q), Iso.hom_inv_id_assoc]
  exact π_comp_grSummandIncl S (k := k) (q + 1) ⟨1, by omega⟩

theorem linearPieceToFiber_app_π_app (q : ℕ) (U : X.Opens) (x' : Γ((S.irrelevantPow 1 (q + 1)).1, U)) :
    (linearPieceToFiber S (k := k) q).app U
        ((cokernel.π (S.irrelevantPow 2 (q + 1)).2).app U ((S.irrelevantPow 1 (q + 1)).2.app U x')) =
      (fiberGen S (k := k) (q + 1) ⟨1, by omega⟩).app U x' :=
  congrArg (fun φ => φ.app U x') (irrelevantPow_one_snd_comp_π_comp_linearPieceToFiber S (k := k) q)

end AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation


/-! ## §D The fibre chart `χ_i : T(U_i) ≃+* Γ(U_i)[y_s]` and the class of a section -/

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)
variable {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
variable {σ : Type u} {w : σ → ℕ} (𝒜 : S.toGradedAffineAlgebra.WeightedPolynomialAtlas w) (hw : ∀ s, 0 < w s) (i : 𝒜.I)

/-- `U_i ≤ s_t⁻¹(V_i)`, `V_i = π⁻¹U_i` (indeed equal). -/
theorem chart_le_sectionAt_preimage_reesChart (t : k) :
    (𝒜.chart i).toOpens ≤ affineLineOver.sectionAt X t ⁻¹ᵁ (S.reesChart 𝒜 i).toOpens :=
  affineLineOver.le_sectionAt_preimage_toBase_preimage t _

include hw in
/-- **The fibre chart** `χ_i : T(U_i) ≃+* Γ(U_i)[y_s]` of `T = s₀^*R` on the chart `U_i` of `𝒜`: the chart isomorphism of
a pullback (`pullbackAtlasEquiv`, Stacks 01I9) applied to `R` with its atlas `reesAtlas` along `s₀`, on
`U_i ⊆ s₀⁻¹(V_i)`. -/
def fiberChartEquiv :
    (S.reesDeformation.restrictToLambda (0 : k)).sectionsRing (𝒜.chart i).toOpens ≃+*
      MvPolynomial σ Γ(X, (𝒜.chart i).toOpens) :=
  S.reesDeformation.pullbackAtlasEquiv (affineLineOver.sectionAt X (0 : k)) (S.reesAtlas 𝒜 hw) i (𝒜.chart i)
    (S.chart_le_sectionAt_preimage_reesChart 𝒜 i 0)
    (S.reesDeformation.pullbackTensorAlgHom_bijective (affineLineOver.sectionAt X (0 : k)) ((S.reesAtlas 𝒜 hw).chart i)
      (𝒜.chart i) (S.chart_le_sectionAt_preimage_reesChart 𝒜 i 0))

/-- (a) `χ_i` sends the structure map to the constants. -/
theorem fiberChartEquiv_sectionsUnitHom (b : Γ(X, (𝒜.chart i).toOpens)) :
    S.fiberChartEquiv 𝒜 hw i ((S.reesDeformation.restrictToLambda (0 : k)).sectionsUnitHom (𝒜.chart i).toOpens b) =
      MvPolynomial.C b :=
  S.reesDeformation.pullbackAtlasEquiv_unitHom (affineLineOver.sectionAt X (0 : k)) (S.reesAtlas 𝒜 hw) i (𝒜.chart i)
    (S.chart_le_sectionAt_preimage_reesChart 𝒜 i 0)
    (S.reesDeformation.pullbackTensorAlgHom_bijective (affineLineOver.sectionAt X (0 : k)) ((S.reesAtlas 𝒜 hw).chart i)
      (𝒜.chart i) (S.chart_le_sectionAt_preimage_reesChart 𝒜 i 0)) b

/-- **(b) The class of `x ∈ Γ(U_i, I^{(p)}_j)` in the fibre is the degree-`p` part of its polynomial**: under `χ_i`,
`of_j (fiberGen S j p x) ↦ homogeneousComponent p (φ_i (of_j (ι_p x)))`. Proof: `fiberGen x` is the pullback along `s₀` of
`z := reesGen (π^*x) ∈ Γ(V_i, R_j)` (`fiberGen_app`); `χ_i (of_j (s₀^*z)) = map s₀^♯ (e_i (of_j z))`
(`pullbackAtlasEquiv_ofPiece_pullbackPiece`); `e_i (of_j z) = reesLift λ_i p P'` with `P' := map π^♯ P`, `P := φ_i (of_j (ι_p x))`,
because `Φ_i` of both sides is `λ_i^{j-p} · P'` (`reesRescale_reesChartEquiv`, `reesChartAlgHom_ofPiece`,
`reesGen_comp_incl`, `mulCoordPow_app`, `pullbackAtlasEquiv_ofPiece_pullbackPiece` for `π`, `reesRescale_reesLift`) and `Φ_i` is
injective; finally `map s₀^♯` kills `λ_i` (`map_reesLift_of_eq_zero`) and `s₀^♯ ∘ π^♯ = id`. -/
theorem fiberChartEquiv_ofPiece_fiberGen (j : ℕ) (p : Fin (j + 1)) (x : Γ((S.irrelevantPow p.1 j).1, (𝒜.chart i).toOpens)) :
    S.fiberChartEquiv 𝒜 hw i ((S.reesDeformation.restrictToLambda (0 : k)).ofPiece (𝒜.chart i).toOpens j
        ((reesDeformation.fiberGen S (k := k) j p).app (𝒜.chart i).toOpens x)) =
      MvPolynomial.homogeneousComponent p.1
        (𝒜.equiv i (S.ofPiece (𝒜.chart i).toOpens j ((S.irrelevantPow p.1 j).2.app (𝒜.chart i).toOpens x) :
          S.toGradedAffineAlgebra.toAffineAlgebra.sections (𝒜.chart i))) := by
  have hle := S.chart_le_sectionAt_preimage_reesChart 𝒜 i (0 : k)
  have hΨ := S.pullbackTensorAlgHom_bijective (affineLineOver.toBase X) (𝒜.chart i) (S.reesChart 𝒜 i) le_rfl
  -- `P`, `P'`
  set P : MvPolynomial σ Γ(X, (𝒜.chart i).toOpens) :=
    𝒜.equiv i (S.ofPiece (𝒜.chart i).toOpens j ((S.irrelevantPow p.1 j).2.app (𝒜.chart i).toOpens x)) with hPdef
  set P' : MvPolynomial σ Γ(affineLineOver X, (S.reesChart 𝒜 i).toOpens) :=
    MvPolynomial.map ((affineLineOver.toBase X).appLE (𝒜.chart i).toOpens (S.reesChart 𝒜 i).toOpens le_rfl).hom P with hP'def
  have hP : P ∈ ReesAlgebra.irrPow (MvPolynomial.weightedHomogeneousSubmodule Γ(X, (𝒜.chart i).toOpens) w) p.1 j :=
    (S.mem_irrPow_iff_equiv_mem 𝒜 i p.1 j _).1 (S.ofPiece_irrelevantPow_app_mem_irrPow (𝒜.chart i) p.1 j x)
  have hP' : ∀ α ∈ P'.support, Finsupp.weight w α = j ∧ p.1 ≤ α.degree := fun α hα => by
    have hα' : α ∈ P.support := MvPolynomial.support_map_subset _ _ hα
    exact ⟨(MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).1 hP.2 (MvPolynomial.mem_support_iff.1 hα'),
      MvPolynomial.degree_le_of_mem_irrelevant_pow w hw hP.1 α hα'⟩
  -- `y := π^*x ∈ Γ(V_i, π^*I^{(p)}_j)`, `z := reesGen y ∈ Γ(V_i, R_j)`
  set y := Modules.pullbackUnitHom (affineLineOver.toBase X) (S.irrelevantPow p.1 j).1 (𝒜.chart i).toOpens x with hydef
  set z : S.reesDeformation.sectionsPiece (S.reesChart 𝒜 i).toOpens j :=
    (reesDeformation.reesGen S j p).app (S.reesChart 𝒜 i).toOpens y with hzdef
  -- `incl z = λ^{j-p} • π^*(ι_p x)`
  have hz : (reesDeformation.incl S j).app (S.reesChart 𝒜 i).toOpens z =
      @HSMul.hSMul Γ(affineLineOver X, (S.reesChart 𝒜 i).toOpens)
        Γ((S.pullback (affineLineOver.toBase X)).part j, (S.reesChart 𝒜 i).toOpens)
        Γ((S.pullback (affineLineOver.toBase X)).part j, (S.reesChart 𝒜 i).toOpens) _
        (affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens ^ (j - p.1))
        (S.pullbackPiece (affineLineOver.toBase X) (𝒜.chart i).toOpens (S.reesChart 𝒜 i).toOpens le_rfl j
          ((S.irrelevantPow p.1 j).2.app (𝒜.chart i).toOpens x)) := by
    have e1 := congrArg (fun φ => φ.app (S.reesChart 𝒜 i).toOpens y) (reesDeformation.reesGen_comp_incl S j p)
    refine e1.trans ?_
    show (affineLineOver.mulCoordPow (j - p.1) _).app (S.reesChart 𝒜 i).toOpens
      ((reesDeformation.pullMap S (S.irrelevantPow p.1 j).2).app (S.reesChart 𝒜 i).toOpens y) = _
    rw [affineLineOver.mulCoordPow_app]
    congr 1
    show ((Modules.pullback (affineLineOver.toBase X)).map (S.irrelevantPow p.1 j).2).app
      (affineLineOver.toBase X ⁻¹ᵁ (𝒜.chart i).toOpens) (Modules.pullbackUnitHom (affineLineOver.toBase X) _ _ x) = _
    rw [← Modules.pullbackSectionsOn_self (affineLineOver.toBase X) (S.irrelevantPow p.1 j).1 (𝒜.chart i).toOpens x]
    exact Modules.pullback_map_app_pullbackSectionsOn_bc (affineLineOver.toBase X) (S.irrelevantPow p.1 j).2
      (𝒜.chart i).toOpens _ le_rfl x
  -- `e_i (of_j z) = reesLift λ_i p P'`
  have hQ : ∀ a : S.reesDeformation.toGradedAffineAlgebra.toAffineAlgebra.sections (S.reesChart 𝒜 i),
      a = S.reesDeformation.ofPiece (S.reesChart 𝒜 i).toOpens j z →
      S.reesChartEquiv 𝒜 hw i a =
        MvPolynomial.reesLift (affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) p.1 P' := by
    intro a ha
    apply S.reesRescale_lambdaRes_reesChart_injective 𝒜 i
    rw [S.reesRescale_reesChartEquiv 𝒜 hw i, MvPolynomial.reesRescale_reesLift _ w hw P' hP', ha]
    erw [S.reesChartAlgHom_ofPiece 𝒜 i j z]
    show S.pullbackAtlasEquiv (affineLineOver.toBase X) 𝒜 i (S.reesChart 𝒜 i) le_rfl hΨ
      ((S.pullback (affineLineOver.toBase X)).ofPiece (S.reesChart 𝒜 i).toOpens j
        ((reesDeformation.incl S j).app (S.reesChart 𝒜 i).toOpens z)) = _
    rw [hz]
    have hu : ∀ r, S.pullbackAtlasEquiv (affineLineOver.toBase X) 𝒜 i (S.reesChart 𝒜 i) le_rfl hΨ
        ((S.pullback (affineLineOver.toBase X)).sectionsUnitHom (S.reesChart 𝒜 i).toOpens r) = MvPolynomial.C r :=
      fun r => S.pullbackAtlasEquiv_unitHom (affineLineOver.toBase X) 𝒜 i (S.reesChart 𝒜 i) le_rfl hΨ r
    rw [← (S.pullback (affineLineOver.toBase X)).sectionsUnitHom_mul_ofPiece (S.reesChart 𝒜 i).toOpens _ _]
    refine (map_mul (S.pullbackAtlasEquiv (affineLineOver.toBase X) 𝒜 i (S.reesChart 𝒜 i) le_rfl hΨ)
      ((S.pullback (affineLineOver.toBase X)).sectionsUnitHom (S.reesChart 𝒜 i).toOpens
        (affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens ^ (j - p.1)))
      ((S.pullback (affineLineOver.toBase X)).ofPiece (S.reesChart 𝒜 i).toOpens j
        (S.pullbackPiece (affineLineOver.toBase X) (𝒜.chart i).toOpens (S.reesChart 𝒜 i).toOpens le_rfl j
          ((S.irrelevantPow p.1 j).2.app (𝒜.chart i).toOpens x)))).trans ?_
    erw [hu, S.pullbackAtlasEquiv_ofPiece_pullbackPiece (affineLineOver.toBase X) 𝒜 i (S.reesChart 𝒜 i) le_rfl hΨ j]
  -- assemble
  rw [reesDeformation.fiberGen_app S j p (𝒜.chart i).toOpens hle x]
  have h2 := S.reesDeformation.pullbackAtlasEquiv_ofPiece_pullbackPiece (affineLineOver.sectionAt X (0 : k))
    (S.reesAtlas 𝒜 hw) i (𝒜.chart i) hle
    (S.reesDeformation.pullbackTensorAlgHom_bijective (affineLineOver.sectionAt X (0 : k)) ((S.reesAtlas 𝒜 hw).chart i)
      (𝒜.chart i) hle) j z
  refine h2.trans ?_
  -- normalise the spelling: `(reesAtlas).chart i ↦ reesChart 𝒜 i`, `(reesAtlas).equiv i ↦ reesChartEquiv` (both `rfl`)
  show MvPolynomial.map ((affineLineOver.sectionAt X (0 : k)).appLE (S.reesChart 𝒜 i).toOpens (𝒜.chart i).toOpens hle).hom
    (S.reesChartEquiv 𝒜 hw i (S.reesDeformation.ofPiece (S.reesChart 𝒜 i).toOpens j z)) = _
  have h3 : S.reesChartEquiv 𝒜 hw i (S.reesDeformation.ofPiece (S.reesChart 𝒜 i).toOpens j z) =
      MvPolynomial.reesLift (affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) p.1 P' := hQ _ rfl
  have hlam : ((affineLineOver.sectionAt X (0 : k)).appLE (S.reesChart 𝒜 i).toOpens (𝒜.chart i).toOpens hle).hom
      (affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) = 0 :=
    affineLineOver.sectionAt_zero_appLE_lambdaRes (𝒜.chart i).toOpens hle
  have hid : ((affineLineOver.sectionAt X (0 : k)).appLE (S.reesChart 𝒜 i).toOpens (𝒜.chart i).toOpens hle).hom.comp
      ((affineLineOver.toBase X).appLE (𝒜.chart i).toOpens (S.reesChart 𝒜 i).toOpens le_rfl).hom = RingHom.id _ :=
    RingHom.ext fun b => affineLineOver.sectionAt_appLE_toBase_appLE 0 (𝒜.chart i).toOpens hle b
  rw [h3]
  refine (MvPolynomial.map_reesLift_of_eq_zero _ hlam p.1 P' (fun α hα => (hP' α hα).2)).trans ?_
  rw [hP'def, MvPolynomial.map_map, hid, MvPolynomial.map_id]

/-- **(b) for the generator map**: under `χ_i`, the class `γ_q (π x)` of `x ∈ Γ(U_i, S_{q+1})` in the fibre `T_{q+1}` goes to the
**linear part** `homogeneousComponent 1 (φ_i (of_{q+1} x))` of the polynomial of `x`. -/
theorem fiberChartEquiv_ofPiece_linearPieceToFiber (q : ℕ) (x : Γ(S.part (q + 1), (𝒜.chart i).toOpens)) :
    S.fiberChartEquiv 𝒜 hw i ((S.reesDeformation.restrictToLambda (0 : k)).ofPiece (𝒜.chart i).toOpens (q + 1)
        ((reesDeformation.linearPieceToFiber S (k := k) q).app (𝒜.chart i).toOpens
          ((CategoryTheory.Limits.cokernel.π (S.irrelevantPow 2 (q + 1)).2).app (𝒜.chart i).toOpens x))) =
      MvPolynomial.homogeneousComponent 1
        (𝒜.equiv i (S.ofPiece (𝒜.chart i).toOpens (q + 1) x :
          S.toGradedAffineAlgebra.toAffineAlgebra.sections (𝒜.chart i))) := by
  have := S.isIso_irrelevantPow_one_snd (q + 1) (Nat.succ_pos q)
  obtain ⟨x', rfl⟩ : ∃ x', (S.irrelevantPow 1 (q + 1)).2.app (𝒜.chart i).toOpens x' = x :=
    ⟨(asIso (S.irrelevantPow 1 (q + 1)).2).inv.app (𝒜.chart i).toOpens x,
      Modules.modIso_hom_app_inv_app (asIso (S.irrelevantPow 1 (q + 1)).2) (𝒜.chart i).toOpens x⟩
  rw [reesDeformation.linearPieceToFiber_app_π_app S q (𝒜.chart i).toOpens x']
  exact S.fiberChartEquiv_ofPiece_fiberGen 𝒜 hw i (q + 1) ⟨1, by omega⟩ x'

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
