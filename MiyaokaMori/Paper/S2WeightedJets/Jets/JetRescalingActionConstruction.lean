import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.GmActionOnJetBase
import MiyaokaMori.AlgebraicGeometry.Morphisms.GroupSchemeAction
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetBaseHomExt
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetBaseScheme
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetConstantTerm
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetThickening
import MiyaokaMori.AlgebraicGeometry.Morphisms.MultiplicativeGroupScheme
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetFunctor
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetRepresentableBy
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetScheme

/-! # Construction of the rescaling action on the jet scheme

The `𝔾_m`-action `t ↦ λt` on the relative jet scheme `J = J_r^s(Z/C)` (§2 of the paper: parameter rescaling
grades the coordinate algebra of `J_k^s`): the data `jetRescalingAction : GmActionOver k J` together with all its
axioms (`act_over`, `one_act`, `mul_act`).

The non-negativity of the action (its extension to `𝔸¹`) is proved in `JetRescalingActionAffineLine`
(`jetRescalingAction_isNonnegative'`), and `JetRescalingAction` derives `jetRescalingAction_isNonnegative` from it;
the import graph is `Construction ← AffineLine ← JetRescalingAction`.

Route (Yoneda): `W := 𝔾_m ×_k J` over `C`, `λ := pr₁`,
`ρ_λ : W ×_k D_r → W ×_k D_r` the rescaling `t ↦ λt` (`jetThickening.rescaleBy`), `x₀` the universal
based jet pulled back along `pr₂ : W → J`; `ρ_λ ≫ x₀` is again a based jet (`jetRescalingAction_point_prop`:
`ρ_λ` preserves the projection and fixes `t = 0`), and `act` is the `C`-morphism `W → J` it corresponds
to under `relativeJetScheme.representableBy`.  `one_act` and `mul_act` follow from the naturality of the
representing bijection and the two identities `ρ_1 = 𝟙` (`jetThickening.rescaleBy_one`) and
`ρ_λ ≫ ρ_μ = ρ_{λμ}` (`jetThickening.rescaleBy_mul`), both checked on the parameter `t` via
`JetBase.hom_ext_of_over`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `jetBaseRescaling` is a `k`-morphism: the coaction is a `k`-algebra homomorphism (`AdjoinRoot.lift_of`), plus
`pullbackSpecIso_hom_base`. -/

theorem jetBaseRescaling_over (k : Type u) [Field k] (r : ℕ) :
    jetBaseRescaling k r ≫ (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      CategoryTheory.Limits.pullback.fst (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫
        (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  have hco : CommRingCat.ofHom (algebraMap k (MiyaokaMori.Jet.TruncatedJetRing k r)) ≫
      CommRingCat.ofHom (jetBaseRescaling.coaction k r) =
      CommRingCat.ofHom (algebraMap k (TensorProduct k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r))) := by
    ext c
    show jetBaseRescaling.coaction k r (AdjoinRoot.of _ c) = _
    unfold jetBaseRescaling.coaction
    exact AdjoinRoot.lift_of (jetBaseRescaling.coaction_wellDefined k r)
  have key : (AlgebraicGeometry.pullbackSpecIso k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)).hom ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (jetBaseRescaling.coaction k r)) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (MiyaokaMori.Jet.TruncatedJetRing k r))) =
      CategoryTheory.Limits.pullback.fst _ _ ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k))) := by
    rw [← AlgebraicGeometry.Spec.map_comp, hco]
    exact AlgebraicGeometry.pullbackSpecIso_hom_base k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)
  exact (CategoryTheory.Category.assoc _ _ _).trans key

/-! ## The coordinate of `G_m` and the comorphism of `t ↦ λt` on the parameter -/

/-- The coordinate `T ∈ Γ(G_m, O)` of `G_m = Spec k[T, T⁻¹]`. -/
noncomputable def GmCoordinate (k : Type u) [Field k] : Γ(Gm k, ⊤) :=
  (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom (LaurentPolynomial.T 1)

/-- The unit `e : Spec k → G_m` of the group scheme `G_m` (`Spec` of the counit `T ↦ 1`), with its type
spelled out as a morphism of schemes (`.left` of `MonObj.one` has codomain `((Gm k).asOver _).left`,
which is only definitionally `Gm k`; `rw` needs the syntactic form). -/
noncomputable def GmOne (k : Type u) [Field k] : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ Gm k :=
  (CategoryTheory.MonObj.one : CategoryTheory.MonoidalCategory.tensorUnit
    (CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))) ⟶
    (Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).left

/-- The multiplication `m : G_m ×_k G_m → G_m` (`Spec` of the comultiplication `T ↦ T ⊗ T`), with its
type spelled out as a morphism of schemes (`(G ⊗ G).left` is definitionally `pullback G.hom G.hom`). -/
noncomputable def GmMul (k : Type u) [Field k] :
    CategoryTheory.Limits.pullback (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ⟶ Gm k :=
  (CategoryTheory.MonObj.mul : CategoryTheory.MonoidalCategory.tensorObj
    ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k)))
    ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))) ⟶
    (Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).left

/-- The unit `e : Spec k → G_m` (`Spec` of the counit `T ↦ 1`) sends the coordinate to `1`
(`AlgebraicGeometry.one_spec_asOver_spec_left`, `LaurentPolynomial.counit_T`). -/
theorem Gm_one_left_appTop_coordinate (k : Type u) [Field k] :
    (GmOne k).appTop.hom (GmCoordinate k) = 1 := by
  show (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (Bialgebra.counitAlgHom k (LaurentPolynomial k) : LaurentPolynomial k →+* k))).appTop.hom
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom (LaurentPolynomial.T 1)) = 1
  rw [Spec_map_appTop_ΓSpecIso_inv]
  show (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    (Coalgebra.counit (R := k) (LaurentPolynomial.T 1 : LaurentPolynomial k)) = 1
  rw [LaurentPolynomial.counit_T, map_one]

/-- The multiplication `m : G_m ×_k G_m → G_m` (`Spec` of the comultiplication `T ↦ T ⊗ T`) on the
coordinate: `(a, b)^♯ m^♯ (T) = a^♯(T) · b^♯(T)` (`AlgebraicGeometry.mul_spec_asOver_spec_left`,
`LaurentPolynomial.comul_T`, `pullbackSpecIso_lift_appTop_tmul`). -/
theorem Gm_mul_left_appTop_coordinate (k : Type u) [Field k] {W : AlgebraicGeometry.Scheme.{u}}
    (a b : W ⟶ Gm k)
    (hab : a ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      b ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    (CategoryTheory.Limits.pullback.lift a b hab ≫ GmMul k).appTop.hom (GmCoordinate k) =
      a.appTop.hom (GmCoordinate k) * b.appTop.hom (GmCoordinate k) := by
  show (CategoryTheory.Limits.pullback.lift a b hab ≫
      (AlgebraicGeometry.pullbackSpecIso k (LaurentPolynomial k) (LaurentPolynomial k)).hom).appTop.hom
    ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (Bialgebra.comulAlgHom k (LaurentPolynomial k) :
        LaurentPolynomial k →+* TensorProduct k (LaurentPolynomial k) (LaurentPolynomial k)))).appTop.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom (LaurentPolynomial.T 1))) = _
  rw [Spec_map_appTop_ΓSpecIso_inv]
  have hc : (CommRingCat.ofHom (Bialgebra.comulAlgHom k (LaurentPolynomial k) :
      LaurentPolynomial k →+* TensorProduct k (LaurentPolynomial k) (LaurentPolynomial k))).hom (LaurentPolynomial.T 1) =
      TensorProduct.tmul k (LaurentPolynomial.T 1 : LaurentPolynomial k) (LaurentPolynomial.T 1 : LaurentPolynomial k) := by
    show Bialgebra.comulAlgHom k (LaurentPolynomial k) (LaurentPolynomial.T 1) = _
    rw [Bialgebra.comulAlgHom_apply, LaurentPolynomial.comul_T]
  rw [hc]
  exact pullbackSpecIso_lift_appTop_tmul (k := k) a b hab (LaurentPolynomial.T 1) (LaurentPolynomial.T 1)

/-- The comorphism of `(a, b) ↦ a·b : W → G_m ×_k D_r → D_r` on the parameter: `t ↦ a^♯(T) · b^♯(t)`
(the `G_m`-version of `jetBaseRescalingA1_lift_appTop_parameter`; `coaction t = T ⊗ t`,
`AdjoinRoot.lift_root`, then `pullbackSpecIso_lift_appTop_tmul`). -/
theorem jetBaseRescaling_lift_appTop_parameter {k : Type u} [Field k] (r : ℕ) {W : AlgebraicGeometry.Scheme.{u}}
    (a : W ⟶ Gm k) (b : W ⟶ jetBase k r)
    (hab : a ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      b ≫ (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    (CategoryTheory.Limits.pullback.lift a b hab ≫ jetBaseRescaling k r).appTop.hom (JetBase.parameter (k := k) r) =
      a.appTop.hom (GmCoordinate k) * b.appTop.hom (JetBase.parameter (k := k) r) := by
  have h1 : (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (jetBaseRescaling.coaction k r))).appTop.hom
      (JetBase.parameter (k := k) r) =
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (TensorProduct k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)))).inv.hom
        (TensorProduct.tmul k (LaurentPolynomial.T 1 : LaurentPolynomial k)
          (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1)))) := by
    show (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (jetBaseRescaling.coaction k r))).appTop.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (MiyaokaMori.Jet.TruncatedJetRing k r))).inv.hom
        (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1)))) = _
    rw [Spec_map_appTop_ΓSpecIso_inv]
    show (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (TensorProduct k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)))).inv.hom
      ((jetBaseRescaling.coaction k r) (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1)))) = _
    unfold jetBaseRescaling.coaction
    rw [AdjoinRoot.lift_root]
  show (CategoryTheory.Limits.pullback.lift a b hab ≫
      (AlgebraicGeometry.pullbackSpecIso k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)).hom).appTop.hom
    ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom (jetBaseRescaling.coaction k r))).appTop.hom
      (JetBase.parameter (k := k) r)) = _
  rw [h1]
  exact pullbackSpecIso_lift_appTop_tmul (k := k) a b hab (LaurentPolynomial.T 1) (AdjoinRoot.root _)

/-! ## `ρ_λ`: the rescaling of the jet thickening induced by `t ↦ λt`

In general, a `k`-scheme `V` and a `k`-morphism `λ : V → 𝔾_m` (`hlam` says `λ` is over `Spec k`) give
`ρ_λ : V ×_k D_r → V ×_k D_r`. `jetRescalingAction` takes `V := 𝔾_m ×_k J` and `λ :=` the first projection. -/

section RescaleBy

variable {k : Type u} [Field k] (r : ℕ) (V : AlgebraicGeometry.Scheme.{u})
  [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (lam : V ⟶ Gm k)

/-- The `pullback.lift` compatibility condition for `τ_λ`: `(pr ≫ λ) ≫ (𝔾_m → Spec k) = snd ≫ (D_r → Spec k)`. -/

theorem jetThickening.rescaleParam_cond
    (hlam : lam ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ lam) ≫
      (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
    CategoryTheory.Limits.pullback.snd (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫
      (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  rw [CategoryTheory.Category.assoc, hlam]
  exact CategoryTheory.Limits.pullback.condition

/-- `τ_λ : V ×_k D_r ⟶ D_r`: first `(λ, t)` into `𝔾_m ×_k D_r`, then the coaction `t ↦ λ ⊗ t`
(`jetBaseRescaling`). -/

noncomputable def jetThickening.rescaleParam
    (hlam : lam ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) : jetThickening (k := k) r V ⟶ jetBase k r :=
  CategoryTheory.Limits.pullback.lift
      (CategoryTheory.Limits.pullback.fst _ _ ≫ lam) (CategoryTheory.Limits.pullback.snd _ _)
      (jetThickening.rescaleParam_cond (k := k) r V lam hlam) ≫
    jetBaseRescaling k r

/-- The `pullback.lift` compatibility condition for `ρ_λ`: `pr ≫ (V → Spec k) = τ_λ ≫ (D_r → Spec k)`.
Same route as `jetRescalingAction_rho_cond`: `jetBaseRescaling` is a `k`-morphism (`jetBaseRescaling_over`). -/

theorem jetThickening.rescaleBy_cond
    (hlam : lam ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
    jetThickening.rescaleParam (k := k) r V lam hlam ≫
      (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  unfold jetThickening.rescaleParam
  refine Eq.symm ?_
  refine (CategoryTheory.Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (jetBaseRescaling_over k r)).trans ?_
  refine (CategoryTheory.Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (CategoryTheory.Limits.pullback.lift_fst _ _ _)).trans ?_
  refine (CategoryTheory.Category.assoc _ _ _).trans ?_
  exact congrArg (_ ≫ ·) hlam

/-- `ρ_λ : V ×_k D_r ⟶ V ×_k D_r` (`t ↦ λt`): the first component is unchanged, the second is `τ_λ`. -/

noncomputable def jetThickening.rescaleBy
    (hlam : lam ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    jetThickening (k := k) r V ⟶ jetThickening (k := k) r V :=
  CategoryTheory.Limits.pullback.lift (CategoryTheory.Limits.pullback.fst _ _)
    (jetThickening.rescaleParam (k := k) r V lam hlam)
    (jetThickening.rescaleBy_cond (k := k) r V lam hlam)

/-- `ρ_λ` preserves the projection to `V`: `ρ_λ ≫ pr = pr`. -/

@[reassoc]
theorem jetThickening.rescaleBy_proj
    (hlam : lam ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    jetThickening.rescaleBy (k := k) r V lam hlam ≫ jetThickeningProj (k := k) r V =
      jetThickeningProj (k := k) r V :=
  CategoryTheory.Limits.pullback.lift_fst _ _ _

/-- In the `D_r` direction, `ρ_λ` is `τ_λ`. -/

@[reassoc]
theorem jetThickening.rescaleBy_snd
    (hlam : lam ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    jetThickening.rescaleBy (k := k) r V lam hlam ≫
        CategoryTheory.Limits.pullback.snd (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      jetThickening.rescaleParam (k := k) r V lam hlam :=
  CategoryTheory.Limits.pullback.lift_snd _ _ _

/-- `ρ_λ` depends only on `λ` (the hypothesis `hlam` is a proof). -/
theorem jetThickening.rescaleBy_congr {lam' : V ⟶ Gm k} (h : lam = lam')
    (hlam : lam ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (hlam' : lam' ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    jetThickening.rescaleBy (k := k) r V lam hlam = jetThickening.rescaleBy (k := k) r V lam' hlam' := by
  subst h
  rfl

/-- `τ_λ` on the parameter: `t ↦ pr^♯(λ^♯ T) · t` (`jetBaseRescaling_lift_appTop_parameter`). -/
theorem jetThickening.rescaleParam_appTop_parameter
    (hlam : lam ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    (jetThickening.rescaleParam (k := k) r V lam hlam).appTop.hom (JetBase.parameter (k := k) r) =
      (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ lam).appTop.hom (GmCoordinate k) *
        (CategoryTheory.Limits.pullback.snd (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop.hom (JetBase.parameter (k := k) r) := by
  delta jetThickening.rescaleParam jetThickening
  exact jetBaseRescaling_lift_appTop_parameter (k := k) r _ _ _

/-- `ρ_λ` fixes `t = 0`: `(constant term) ≫ ρ_λ = (constant term)`.

Proof. Compare the two projections (`pullback.hom_ext`). On `V`: `ρ_λ ≫ pr = pr`. On `D_r`: both
sides are `k`-morphisms `V → D_r`, so by `JetBase.hom_ext_of_over` it suffices to compare the
images of `t`; the left side is `ct^♯(pr^♯(λ^♯T) · t) = λ^♯T · ct^♯(t)` and `ct^♯(t) = 0` because
`ct ≫ snd = (V ↘ k) ≫ (t ↦ 0)` kills `t` (`JetBase.zero_appTop_parameter`). -/
theorem jetConstantTerm_comp_rescaleBy
    (hlam : lam ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    jetConstantTerm (k := k) r V ≫ jetThickening.rescaleBy (k := k) r V lam hlam =
      jetConstantTerm (k := k) r V := by
  apply CategoryTheory.Limits.pullback.hom_ext
  · show jetConstantTerm (k := k) r V ≫ (jetThickening.rescaleBy (k := k) r V lam hlam ≫
        jetThickeningProj (k := k) r V) = jetConstantTerm (k := k) r V ≫ jetThickeningProj (k := k) r V
    rw [jetThickening.rescaleBy_proj]
  · show jetConstantTerm (k := k) r V ≫ (jetThickening.rescaleBy (k := k) r V lam hlam ≫
        CategoryTheory.Limits.pullback.snd _ _) = jetConstantTerm (k := k) r V ≫ CategoryTheory.Limits.pullback.snd _ _
    rw [jetThickening.rescaleBy_snd, jetConstantTerm_comp_snd]
    apply JetBase.hom_ext_of_over (k := k) r
    · rw [CategoryTheory.Category.assoc, ← jetThickening.rescaleBy_cond (k := k) r V lam hlam]
      refine (CategoryTheory.Category.assoc _ _ _).symm.trans ?_
      have h := jetConstantTerm_comp_proj (k := k) r (W := V)
      rw [show jetConstantTerm (k := k) r V ≫ CategoryTheory.Limits.pullback.fst
          (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
          CategoryTheory.CategoryStruct.id V from h]
      exact CategoryTheory.Category.id_comp _
    · rw [CategoryTheory.Category.assoc, jetBaseZero_comp_structure, CategoryTheory.Category.comp_id]
    · have h0 : ((V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ jetBaseZero k r).appTop.hom
          (JetBase.parameter (k := k) r) = 0 := by
        show (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop.hom
          ((jetBaseZero k r).appTop.hom (JetBase.parameter (k := k) r)) = 0
        rw [JetBase.zero_appTop_parameter, map_zero]
      have h2 : (jetConstantTerm (k := k) r V).appTop.hom
          ((CategoryTheory.Limits.pullback.snd (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop.hom (JetBase.parameter (k := k) r)) = 0 :=
        (congrArg (fun φ : V ⟶ jetBase k r => φ.appTop.hom (JetBase.parameter (k := k) r))
          (jetConstantTerm_comp_snd (k := k) r (W := V))).trans h0
      rw [h0]
      show (jetConstantTerm (k := k) r V).appTop.hom
        ((jetThickening.rescaleParam (k := k) r V lam hlam).appTop.hom (JetBase.parameter (k := k) r)) = 0
      refine (congrArg (jetConstantTerm (k := k) r V).appTop.hom
        (jetThickening.rescaleParam_appTop_parameter (k := k) r V lam hlam)).trans ?_
      refine (map_mul _ _ _).trans ?_
      rw [h2, mul_zero]

/-- `ρ_λ` is natural in the base: `(g × 𝟙) ≫ ρ_λ = ρ_{g ≫ λ} ≫ (g × 𝟙)`. -/
theorem jetThickening.rescaleBy_naturality {V' : AlgebraicGeometry.Scheme.{u}}
    [V'.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (g : V ⟶ V')
    [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (lam' : V' ⟶ Gm k)
    (hlam' : lam' ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V' ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (hlam : (g ≫ lam') ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    jetThickeningMap (k := k) r g ≫ jetThickening.rescaleBy (k := k) r V' lam' hlam' =
      jetThickening.rescaleBy (k := k) r V (g ≫ lam') hlam ≫ jetThickeningMap (k := k) r g := by
  have hl : CategoryTheory.Limits.pullback.map (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (V' ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) g
        (CategoryTheory.CategoryStruct.id _) (CategoryTheory.CategoryStruct.id _) (by simp) (by simp) ≫
      CategoryTheory.Limits.pullback.lift
        (CategoryTheory.Limits.pullback.fst (V' ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ lam')
        (CategoryTheory.Limits.pullback.snd _ _) (jetThickening.rescaleParam_cond (k := k) r V' lam' hlam') =
      CategoryTheory.Limits.pullback.lift
        (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ g ≫ lam')
        (CategoryTheory.Limits.pullback.snd _ _) (jetThickening.rescaleParam_cond (k := k) r V (g ≫ lam') hlam) := by
    apply CategoryTheory.Limits.pullback.hom_ext
    · rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.lift_fst,
        CategoryTheory.Limits.pullback.lift_fst, CategoryTheory.Limits.pullback.lift_fst_assoc,
        CategoryTheory.Category.assoc]
    · rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.lift_snd,
        CategoryTheory.Limits.pullback.lift_snd, CategoryTheory.Limits.pullback.lift_snd,
        CategoryTheory.Category.comp_id]
  have helper : jetThickeningMap (k := k) r g ≫ jetThickening.rescaleParam (k := k) r V' lam' hlam' =
      jetThickening.rescaleParam (k := k) r V (g ≫ lam') hlam := by
    delta jetThickeningMap jetThickening.rescaleParam jetThickening
    rw [← CategoryTheory.Category.assoc, hl]
  apply CategoryTheory.Limits.pullback.hom_ext
  · show (jetThickeningMap (k := k) r g ≫ jetThickening.rescaleBy (k := k) r V' lam' hlam') ≫
        jetThickeningProj (k := k) r V' =
      (jetThickening.rescaleBy (k := k) r V (g ≫ lam') hlam ≫ jetThickeningMap (k := k) r g) ≫
        jetThickeningProj (k := k) r V'
    rw [CategoryTheory.Category.assoc, jetThickening.rescaleBy_proj, jetThickeningMap_proj,
      CategoryTheory.Category.assoc, jetThickeningMap_proj, jetThickening.rescaleBy_proj_assoc]
  · exact ((CategoryTheory.Category.assoc _ _ _).trans
      ((congrArg (jetThickeningMap (k := k) r g ≫ ·) (jetThickening.rescaleBy_snd (k := k) r V' lam' hlam')).trans
        helper)).trans
      (((CategoryTheory.Category.assoc _ _ _).trans
        ((congrArg (jetThickening.rescaleBy (k := k) r V (g ≫ lam') hlam ≫ ·) (jetThickeningMap_snd (k := k) r g)).trans
          (jetThickening.rescaleBy_snd (k := k) r V (g ≫ lam') hlam))).symm)

/-- Rescaling by `λ = 1` (the unit `V → Spec k → G_m`) is the identity: on the parameter,
`t ↦ pr^♯((V ↘ k)^♯(e^♯ T)) · t = 1 · t` (`Gm_one_left_appTop_coordinate`). -/
theorem jetThickening.rescaleBy_one
    (hlam : ((V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ GmOne k) ≫
        (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    jetThickening.rescaleBy (k := k) r V ((V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ GmOne k) hlam =
      CategoryTheory.CategoryStruct.id (jetThickening (k := k) r V) := by
  apply CategoryTheory.Limits.pullback.hom_ext
  · exact (jetThickening.rescaleBy_proj (k := k) r V _ hlam).trans (CategoryTheory.Category.id_comp _).symm
  · refine (jetThickening.rescaleBy_snd (k := k) r V _ hlam).trans
      (Eq.trans ?_ (CategoryTheory.Category.id_comp _).symm)
    letI : (jetThickening (k := k) r V).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨jetThickeningProj (k := k) r V ≫ (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    apply JetBase.hom_ext_of_over (k := k) r
    · exact (jetThickening.rescaleBy_cond (k := k) r V _ hlam).symm
    · exact CategoryTheory.Limits.pullback.condition.symm
    · rw [jetThickening.rescaleParam_appTop_parameter]
      have h1 : (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫
            (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ GmOne k).appTop.hom (GmCoordinate k) = 1 := by
        show (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop.hom
            ((V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop.hom
              ((GmOne k).appTop.hom (GmCoordinate k))) = 1
        rw [Gm_one_left_appTop_coordinate, map_one, map_one]
      rw [h1, one_mul]
      rfl

/-- `ρ_λ ≫ ρ_μ = ρ_{λμ}` (`λμ = (λ, μ) ≫ m`): on the parameter both send `t` to
`pr^♯(λ^♯T) · pr^♯(μ^♯T) · t` (`Gm_mul_left_appTop_coordinate`). -/
theorem jetThickening.rescaleBy_mul (mu : V ⟶ Gm k)
    (hlam : lam ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (hmu : mu ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (hprod : (CategoryTheory.Limits.pullback.lift lam mu (hlam.trans hmu.symm) ≫ GmMul k) ≫
        (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    jetThickening.rescaleBy (k := k) r V lam hlam ≫ jetThickening.rescaleBy (k := k) r V mu hmu =
      jetThickening.rescaleBy (k := k) r V
        (CategoryTheory.Limits.pullback.lift lam mu (hlam.trans hmu.symm) ≫ GmMul k) hprod := by
  apply CategoryTheory.Limits.pullback.hom_ext
  · exact (CategoryTheory.Category.assoc _ _ _).trans
      (((congrArg (jetThickening.rescaleBy (k := k) r V lam hlam ≫ ·)
        (jetThickening.rescaleBy_proj (k := k) r V mu hmu)).trans
        (jetThickening.rescaleBy_proj (k := k) r V lam hlam)).trans
        (jetThickening.rescaleBy_proj (k := k) r V _ hprod).symm)
  · have e1 : (jetThickening.rescaleBy (k := k) r V lam hlam ≫ jetThickening.rescaleBy (k := k) r V mu hmu) ≫
        (CategoryTheory.Limits.pullback.snd _ _ : jetThickening (k := k) r V ⟶ jetBase k r) =
        jetThickening.rescaleBy (k := k) r V lam hlam ≫ jetThickening.rescaleParam (k := k) r V mu hmu :=
      (CategoryTheory.Category.assoc _ _ _).trans
        (congrArg (jetThickening.rescaleBy (k := k) r V lam hlam ≫ ·) (jetThickening.rescaleBy_snd (k := k) r V mu hmu))
    refine e1.trans (Eq.trans ?_ (jetThickening.rescaleBy_snd (k := k) r V _ hprod).symm)
    letI : (jetThickening (k := k) r V).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨jetThickeningProj (k := k) r V ≫ (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    apply JetBase.hom_ext_of_over (k := k) r
    · exact (CategoryTheory.Category.assoc _ _ _).trans
        ((congrArg (jetThickening.rescaleBy (k := k) r V lam hlam ≫ ·)
          (jetThickening.rescaleBy_cond (k := k) r V mu hmu).symm).trans
          (jetThickening.rescaleBy_proj_assoc (k := k) r V lam hlam _))
    · exact (jetThickening.rescaleBy_cond (k := k) r V _ hprod).symm
    · rw [jetThickening.rescaleParam_appTop_parameter]
      have hR : (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫
            CategoryTheory.Limits.pullback.lift lam mu (hlam.trans hmu.symm) ≫ GmMul k).appTop.hom (GmCoordinate k) =
          (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ lam).appTop.hom (GmCoordinate k) *
          (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ mu).appTop.hom (GmCoordinate k) := by
        show (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop.hom
          ((CategoryTheory.Limits.pullback.lift lam mu (hlam.trans hmu.symm) ≫ GmMul k).appTop.hom (GmCoordinate k)) = _
        rw [Gm_mul_left_appTop_coordinate, map_mul]
        rfl
      have e2 : (jetThickening.rescaleBy (k := k) r V lam hlam).appTop.hom
          ((CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ mu).appTop.hom (GmCoordinate k)) =
          (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ mu).appTop.hom (GmCoordinate k) :=
        congrArg (fun m : jetThickening (k := k) r V ⟶ Gm k => m.appTop.hom (GmCoordinate k))
          (jetThickening.rescaleBy_proj_assoc (k := k) r V lam hlam mu)
      have e3 : (jetThickening.rescaleBy (k := k) r V lam hlam).appTop.hom
          ((CategoryTheory.Limits.pullback.snd (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop.hom (JetBase.parameter (k := k) r)) =
          (jetThickening.rescaleParam (k := k) r V lam hlam).appTop.hom (JetBase.parameter (k := k) r) :=
        congrArg (fun m : jetThickening (k := k) r V ⟶ jetBase k r => m.appTop.hom (JetBase.parameter (k := k) r))
          (jetThickening.rescaleBy_snd (k := k) r V lam hlam)
      have hL : (jetThickening.rescaleBy (k := k) r V lam hlam ≫
            jetThickening.rescaleParam (k := k) r V mu hmu).appTop.hom (JetBase.parameter (k := k) r) =
          (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ mu).appTop.hom (GmCoordinate k) *
          ((CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ lam).appTop.hom (GmCoordinate k) *
          (CategoryTheory.Limits.pullback.snd (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop.hom (JetBase.parameter (k := k) r)) := by
        show (jetThickening.rescaleBy (k := k) r V lam hlam).appTop.hom
          ((jetThickening.rescaleParam (k := k) r V mu hmu).appTop.hom (JetBase.parameter (k := k) r)) = _
        refine (congrArg (jetThickening.rescaleBy (k := k) r V lam hlam).appTop.hom
          (jetThickening.rescaleParam_appTop_parameter (k := k) r V mu hmu)).trans ?_
        refine (map_mul _ _ _).trans ?_
        rw [e2, e3, jetThickening.rescaleParam_appTop_parameter]
        rfl
      rw [hL, hR]
      exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm

end RescaleBy

/-- `jetThickeningMap` depends only on the morphism (the `IsOver` instance is a proof). -/
theorem jetThickeningMap_congr_hom {k : Type u} [Field k] (r : ℕ) {V V' : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [V'.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {g g' : V ⟶ V'} (e : g = g')
    [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [g'.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    jetThickeningMap (k := k) r g = jetThickeningMap (k := k) r g' := by
  subst e
  rfl

/-- Composites of `k`-morphisms are `k`-morphisms (explicit form, used for local instances). -/
theorem isOver_comp_of_isOver {k : Type u} [Field k] {X Y Z : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [hg : g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    (f ≫ g).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  ⟨(CategoryTheory.Category.assoc f g _).trans ((congrArg (f ≫ ·) hg.comp_over).trans hf.comp_over)⟩

/-- In `jetRescalingAction`, `λ` (the first projection of `𝔾_m ×_k J`) is a `k`-morphism:
`λ ≫ (𝔾_m → Spec k) = (W.left → Spec k)` (the `pullback.condition` of the two fiber products). -/

theorem jetRescalingAction_lam_over {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    let J := relativeJetScheme (k := k) Z s hs r
    let W : CategoryTheory.Over C := CategoryTheory.Over.mk
      (CategoryTheory.Limits.pullback.snd (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ J.hom)
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    let lam : W.left ⟶ Gm k := CategoryTheory.Limits.pullback.fst _ _
    lam ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (W.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  intro J W lam
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  show CategoryTheory.Limits.pullback.fst _ _ ≫ _ =
    (CategoryTheory.Limits.pullback.snd _ _ ≫ J.hom) ≫ _
  rw [CategoryTheory.Limits.pullback.condition, CategoryTheory.Category.assoc]

/-- First proof obligation of `jetRescalingAction` (the compatibility condition for `pullback.lift` into
`𝔾_m ×_k D_r`): `(pr ≫ λ) ≫ (𝔾_m → Spec k) = snd ≫ (D_r → Spec k)`. Both sides equal the structure morphism
`W ×_k D_r → Spec k` (the `pullback.condition` of the two fiber products). -/

theorem jetRescalingAction_lift_cond {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    let J := relativeJetScheme (k := k) Z s hs r
    let W : CategoryTheory.Over C := CategoryTheory.Over.mk
      (CategoryTheory.Limits.pullback.snd (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ J.hom)
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    let lam : W.left ⟶ Gm k := CategoryTheory.Limits.pullback.fst _ _
    (CategoryTheory.Limits.pullback.fst (W.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ lam) ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      CategoryTheory.Limits.pullback.snd (W.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  intro J W lam
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have h1 : lam ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (W.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    show CategoryTheory.Limits.pullback.fst _ _ ≫ _ = (CategoryTheory.Limits.pullback.snd _ _ ≫ J.hom) ≫ _
    rw [CategoryTheory.Limits.pullback.condition, CategoryTheory.Category.assoc]
  rw [CategoryTheory.Category.assoc, h1]
  exact CategoryTheory.Limits.pullback.condition

/-- Second proof obligation of `jetRescalingAction` (the `pullback.lift` compatibility condition for `ρ`):
`pr ≫ (W → Spec k) = τ ≫ (D_r → Spec k)`. Since `jetBaseRescaling` is a `k`-morphism (the coaction is a
`k`-algebra homomorphism, `AdjoinRoot.lift_of`, plus the compatibility of `pullbackSpecIso` with the projections),
`τ ≫ (D_r → Spec k) = lift(…) ≫ fst ≫ (𝔾_m → Spec k) = pr ≫ λ ≫ (𝔾_m → Spec k) = pr ≫ (W → Spec k)`. -/

theorem jetRescalingAction_rho_cond {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    let J := relativeJetScheme (k := k) Z s hs r
    let W : CategoryTheory.Over C := CategoryTheory.Over.mk
      (CategoryTheory.Limits.pullback.snd (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ J.hom)
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    let lam : W.left ⟶ Gm k := CategoryTheory.Limits.pullback.fst _ _
    let τ : jetThickening (k := k) r W.left ⟶ jetBase k r :=
      CategoryTheory.Limits.pullback.lift
        (CategoryTheory.Limits.pullback.fst (W.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ lam) (CategoryTheory.Limits.pullback.snd (W.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
        (jetRescalingAction_lift_cond (k := k) Z s hs r) ≫
        jetBaseRescaling k r
    CategoryTheory.Limits.pullback.fst (W.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ (W.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      τ ≫ (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  intro J W lam τ
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have h1 : lam ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (W.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    show CategoryTheory.Limits.pullback.fst _ _ ≫ _ = (CategoryTheory.Limits.pullback.snd _ _ ≫ J.hom) ≫ _
    rw [CategoryTheory.Limits.pullback.condition, CategoryTheory.Category.assoc]
  refine Eq.symm ?_
  refine (CategoryTheory.Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (jetBaseRescaling_over k r)).trans ?_
  refine (CategoryTheory.Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (CategoryTheory.Limits.pullback.lift_fst _ _ _)).trans ?_
  refine (CategoryTheory.Category.assoc _ _ _).trans ?_
  exact congrArg (_ ≫ ·) h1

/-- Third proof obligation of `jetRescalingAction`: `λ · φ₀ = ρ ≫ φ₀` is again a based jet.
The first condition follows from `ρ ≫ pr = pr` (`pullback.lift_fst`) and the first condition for `φ₀`; the second
needs `jetConstantTerm ≫ ρ = jetConstantTerm`, i.e. `t ↦ λt` fixes `t = 0`: the coaction followed by `t ↦ 0` sends
`t` to `λ ⊗ 0 = 0` (compatibility of `jetBaseRescaling` with `jetBaseZero`). -/

theorem jetRescalingAction_point_prop {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    let F := relativeJetFunctor (k := k) Z s hs r
    let J := relativeJetScheme (k := k) Z s hs r
    let e := relativeJetScheme.representableBy (k := k) Z s hs r
    let W : CategoryTheory.Over C := CategoryTheory.Over.mk
      (CategoryTheory.Limits.pullback.snd (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ J.hom)
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    let lam : W.left ⟶ Gm k := CategoryTheory.Limits.pullback.fst _ _
    let ρ : jetThickening (k := k) r W.left ⟶ jetThickening (k := k) r W.left :=
      jetThickening.rescaleBy (k := k) r W.left lam
        (jetRescalingAction_lam_over (k := k) Z s hs r)
    let x₀ : F.obj (Opposite.op W) :=
      e.homEquiv (CategoryTheory.Over.homMk (CategoryTheory.Limits.pullback.snd _ _) rfl : W ⟶ J)
    (ρ ≫ x₀.1) ≫ Z.hom = jetThickeningProj (k := k) r W.left ≫ W.hom ∧
      jetConstantTerm (k := k) r W.left ≫ (ρ ≫ x₀.1) = W.hom ≫ s := by
  intro F J e W lam ρ x₀
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have h := x₀.2
  constructor
  · rw [CategoryTheory.Category.assoc, h.1, ← CategoryTheory.Category.assoc]
    show (jetThickening.rescaleBy (k := k) r W.left lam (jetRescalingAction_lam_over (k := k) Z s hs r) ≫
      jetThickeningProj (k := k) r W.left) ≫ W.hom = _
    rw [jetThickening.rescaleBy_proj]
  · rw [← CategoryTheory.Category.assoc]
    show (jetConstantTerm (k := k) r W.left ≫
      jetThickening.rescaleBy (k := k) r W.left lam (jetRescalingAction_lam_over (k := k) Z s hs r)) ≫ x₀.1 = _
    rw [jetConstantTerm_comp_rescaleBy, h.2]

/-- The `act_over` axiom of `jetRescalingAction`: the action preserves the structure morphism to `C`. `act` is the
`.left` of a morphism `W ⟶ J` in `Over C`, so use `Over.w`. -/

theorem jetRescalingAction_act_over {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    let F := relativeJetFunctor (k := k) Z s hs r
    let J := relativeJetScheme (k := k) Z s hs r
    let e := relativeJetScheme.representableBy (k := k) Z s hs r
    let W : CategoryTheory.Over C := CategoryTheory.Over.mk
      (CategoryTheory.Limits.pullback.snd (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ J.hom)
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    let lam : W.left ⟶ Gm k := CategoryTheory.Limits.pullback.fst _ _
    let ρ : jetThickening (k := k) r W.left ⟶ jetThickening (k := k) r W.left :=
      jetThickening.rescaleBy (k := k) r W.left lam
        (jetRescalingAction_lam_over (k := k) Z s hs r)
    let x₀ : F.obj (Opposite.op W) :=
      e.homEquiv (CategoryTheory.Over.homMk (CategoryTheory.Limits.pullback.snd _ _) rfl : W ⟶ J)
    let x : F.obj (Opposite.op W) := ⟨ρ ≫ x₀.1, jetRescalingAction_point_prop (k := k) Z s hs r⟩
    let act : CategoryTheory.Limits.pullback
        (((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom)
        (J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ⟶ J.left := (e.homEquiv.symm x).left
    act ≫ J.hom = CategoryTheory.Limits.pullback.snd _ _ ≫ J.hom := by
  intro F J e W lam ρ x₀ x act
  exact CategoryTheory.Over.w (e.homEquiv.symm x)

/-- The `one_act` axiom of `jetRescalingAction`: the action is trivial at `λ = 1`. By naturality of `homEquiv`
(`homEquiv_comp`) this reduces to the equality of based jets `(e,𝟙)^*(ρ ≫ φ₀) =` universal jet; the pullback of `ρ`
along `λ = 1` is the identity (the coaction `t ↦ λ ⊗ t` is `t ↦ t` at `λ = 1`). The statement is for an arbitrary
compatibility proof `h` of the `pullback.lift` in the type of the field of `GroupSchemeAction`. -/

theorem jetRescalingAction_one_act {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    let F := relativeJetFunctor (k := k) Z s hs r
    let J := relativeJetScheme (k := k) Z s hs r
    let e := relativeJetScheme.representableBy (k := k) Z s hs r
    let W : CategoryTheory.Over C := CategoryTheory.Over.mk
      (CategoryTheory.Limits.pullback.snd (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ J.hom)
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    let lam : W.left ⟶ Gm k := CategoryTheory.Limits.pullback.fst _ _
    let ρ : jetThickening (k := k) r W.left ⟶ jetThickening (k := k) r W.left :=
      jetThickening.rescaleBy (k := k) r W.left lam
        (jetRescalingAction_lam_over (k := k) Z s hs r)
    let x₀ : F.obj (Opposite.op W) :=
      e.homEquiv (CategoryTheory.Over.homMk (CategoryTheory.Limits.pullback.snd _ _) rfl : W ⟶ J)
    let x : F.obj (Opposite.op W) := ⟨ρ ≫ x₀.1, jetRescalingAction_point_prop (k := k) Z s hs r⟩
    let act : CategoryTheory.Limits.pullback
        (((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom)
        (J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ⟶ J.left := (e.homEquiv.symm x).left
    ∀ h, CategoryTheory.Limits.pullback.lift
        ((J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ (CategoryTheory.MonObj.one :
          CategoryTheory.MonoidalCategory.tensorUnit _ ⟶ ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k)))).left)
        (CategoryTheory.CategoryStruct.id J.left) h ≫ act = CategoryTheory.CategoryStruct.id J.left := by
  intro F J e W lam ρ x₀ x act h
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : J.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  let snd : W.left ⟶ J.left := CategoryTheory.Limits.pullback.snd _ _
  let univ := relativeJetScheme.universalJet (k := k) Z s hs r
  let uL : J.left ⟶ W.left :=
    CategoryTheory.Limits.pullback.lift ((J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ GmOne k)
      (CategoryTheory.CategoryStruct.id J.left) h
  have hus : uL ≫ snd = CategoryTheory.CategoryStruct.id J.left := CategoryTheory.Limits.pullback.lift_snd _ _ h
  have hlf : uL ≫ lam = (J.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ GmOne k :=
    CategoryTheory.Limits.pullback.lift_fst _ _ h
  let u : J ⟶ W := CategoryTheory.Over.homMk uL
    (by
      show uL ≫ (snd ≫ J.hom) = J.hom
      exact (CategoryTheory.Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ J.hom) hus).trans (CategoryTheory.Category.id_comp _)))
  haveI hu : uL.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨CategoryTheory.Over.w_assoc u _⟩
  haveI hsnd : snd.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.Over.w_assoc (CategoryTheory.Over.homMk snd rfl : W ⟶ J) _⟩
  haveI husnd : (uL ≫ snd).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    isOver_comp_of_isOver (k := k) uL snd
  have hl : lam ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (W.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    jetRescalingAction_lam_over (k := k) Z s hs r
  have hlu : (uL ≫ lam) ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (J.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    rw [CategoryTheory.Category.assoc, hl]
    exact hu.comp_over
  have hone : ((J.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ GmOne k) ≫
      (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (J.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    rw [CategoryTheory.Category.assoc]
    exact (congrArg ((J.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ ·)
      (CategoryTheory.Over.w (CategoryTheory.MonObj.one : CategoryTheory.MonoidalCategory.tensorUnit _ ⟶
        (Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))))).trans (CategoryTheory.Category.comp_id _)
  have hcongr : jetThickening.rescaleBy (k := k) r J.left (uL ≫ lam) hlu = CategoryTheory.CategoryStruct.id _ :=
    (jetThickening.rescaleBy_congr (k := k) r J.left _ hlf hlu hone).trans
      (jetThickening.rescaleBy_one (k := k) r J.left hone)
  have hx : F.map u.op x = e.homEquiv (CategoryTheory.CategoryStruct.id J) := by
    apply Subtype.ext
    show jetThickeningMap (k := k) r uL ≫ (ρ ≫ (jetThickeningMap (k := k) r snd ≫ univ)) =
      jetThickeningMap (k := k) r (CategoryTheory.CategoryStruct.id J.left) ≫ univ
    have hnat := jetThickening.rescaleBy_naturality (k := k) r J.left uL lam hl hlu
    have hmap : jetThickeningMap (k := k) r uL ≫ jetThickeningMap (k := k) r snd =
        jetThickeningMap (k := k) r (CategoryTheory.CategoryStruct.id J.left) :=
      (jetThickeningMap_comp (k := k) r uL snd).symm.trans (jetThickeningMap_congr_hom (k := k) r hus)
    exact (CategoryTheory.Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (jetThickeningMap (k := k) r snd ≫ univ)) hnat).trans
      ((congrArg (fun q => (q ≫ jetThickeningMap (k := k) r uL) ≫ (jetThickeningMap (k := k) r snd ≫ univ)) hcongr).trans
      ((congrArg (· ≫ (jetThickeningMap (k := k) r snd ≫ univ)) (CategoryTheory.Category.id_comp _)).trans
      ((CategoryTheory.Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ univ) hmap)))))
  show (u ≫ e.homEquiv.symm x).left = (CategoryTheory.CategoryStruct.id J).left
  rw [e.comp_homEquiv_symm, hx, Equiv.symm_apply_apply]

/-- The `mul_act` axiom of `jetRescalingAction`: `(λμ) · j = λ · (μ · j)`. By naturality of `homEquiv` this reduces
to an equality of based jets, namely the coassociativity of `jetBaseRescaling` (the two decompositions of
`t ↦ λμ ⊗ t`). As above, stated for an arbitrary compatibility proof. -/

theorem jetRescalingAction_mul_act {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    let F := relativeJetFunctor (k := k) Z s hs r
    let J := relativeJetScheme (k := k) Z s hs r
    let e := relativeJetScheme.representableBy (k := k) Z s hs r
    let W : CategoryTheory.Over C := CategoryTheory.Over.mk
      (CategoryTheory.Limits.pullback.snd (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ J.hom)
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    let lam : W.left ⟶ Gm k := CategoryTheory.Limits.pullback.fst _ _
    let ρ : jetThickening (k := k) r W.left ⟶ jetThickening (k := k) r W.left :=
      jetThickening.rescaleBy (k := k) r W.left lam
        (jetRescalingAction_lam_over (k := k) Z s hs r)
    let x₀ : F.obj (Opposite.op W) :=
      e.homEquiv (CategoryTheory.Over.homMk (CategoryTheory.Limits.pullback.snd _ _) rfl : W ⟶ J)
    let x : F.obj (Opposite.op W) := ⟨ρ ≫ x₀.1, jetRescalingAction_point_prop (k := k) Z s hs r⟩
    let act : CategoryTheory.Limits.pullback
        (((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom)
        (J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ⟶ J.left := (e.homEquiv.symm x).left
    ∀ h1 h2 h3 h4,
      CategoryTheory.Limits.pullback.map (CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ≫ ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom)
          (J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom (J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
          (CategoryTheory.MonObj.mul : CategoryTheory.MonoidalCategory.tensorObj ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))) ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))) ⟶ ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k)))).left
          (CategoryTheory.CategoryStruct.id J.left)
          (CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of k))) h1 h2 ≫ act =
        CategoryTheory.Limits.pullback.lift
          (CategoryTheory.Limits.pullback.fst _ _ ≫ CategoryTheory.Limits.pullback.fst _ _)
          (CategoryTheory.Limits.pullback.lift
              (CategoryTheory.Limits.pullback.fst _ _ ≫ CategoryTheory.Limits.pullback.snd _ _)
              (CategoryTheory.Limits.pullback.snd _ _) h3 ≫ act) h4 ≫ act := by
  intro F J e W lam ρ x₀ x act h1 h2 h3 h4
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : J.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  let G : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    (Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))
  let mulL : CategoryTheory.Limits.pullback G.hom G.hom ⟶ Gm k := GmMul k
  let W₂ : CategoryTheory.Over C := CategoryTheory.Over.mk
    (CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.fst G.hom G.hom ≫ G.hom)
      (J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ J.hom)
  letI : W₂.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W₂.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  let snd : W.left ⟶ J.left := CategoryTheory.Limits.pullback.snd _ _
  let snd₂ : W₂.left ⟶ J.left := CategoryTheory.Limits.pullback.snd _ _
  let p : W₂.left ⟶ CategoryTheory.Limits.pullback G.hom G.hom := CategoryTheory.Limits.pullback.fst _ _
  let univ := relativeJetScheme.universalJet (k := k) Z s hs r
  let act' : W.left ⟶ J.left := (e.homEquiv.symm x).left
  have hact : act' ≫ J.hom = snd ≫ J.hom := CategoryTheory.Over.w (e.homEquiv.symm x)
  -- the three `C`-morphisms `W₂ → W`: `(λμ, j)`, `(μ, j)` and `(λ, μ·j)`
  let mL : W₂.left ⟶ W.left :=
    CategoryTheory.Limits.pullback.map _ _ _ _ mulL (CategoryTheory.CategoryStruct.id J.left)
      (CategoryTheory.CategoryStruct.id _) h1 h2
  have hm_snd : mL ≫ snd = snd₂ :=
    (CategoryTheory.Limits.pullback.lift_snd _ _ _).trans (CategoryTheory.Category.comp_id _)
  have hm_fst : mL ≫ lam = p ≫ mulL := CategoryTheory.Limits.pullback.lift_fst _ _ _
  let m : W₂ ⟶ W := CategoryTheory.Over.homMk mL
    (by
      show mL ≫ (snd ≫ J.hom) = snd₂ ≫ J.hom
      exact (CategoryTheory.Category.assoc _ _ _).symm.trans (congrArg (· ≫ J.hom) hm_snd))
  let wL : W₂.left ⟶ W.left :=
    CategoryTheory.Limits.pullback.lift (p ≫ CategoryTheory.Limits.pullback.snd G.hom G.hom) snd₂ h3
  have hw_snd : wL ≫ snd = snd₂ := CategoryTheory.Limits.pullback.lift_snd _ _ h3
  have hw_fst : wL ≫ lam = p ≫ CategoryTheory.Limits.pullback.snd G.hom G.hom :=
    CategoryTheory.Limits.pullback.lift_fst _ _ h3
  let w : W₂ ⟶ W := CategoryTheory.Over.homMk wL
    (by
      show wL ≫ (snd ≫ J.hom) = snd₂ ≫ J.hom
      exact (CategoryTheory.Category.assoc _ _ _).symm.trans (congrArg (· ≫ J.hom) hw_snd))
  let vL : W₂.left ⟶ W.left :=
    CategoryTheory.Limits.pullback.lift (p ≫ CategoryTheory.Limits.pullback.fst G.hom G.hom) (wL ≫ act') h4
  have hv_snd : vL ≫ snd = wL ≫ act' := CategoryTheory.Limits.pullback.lift_snd _ _ h4
  have hv_fst : vL ≫ lam = p ≫ CategoryTheory.Limits.pullback.fst G.hom G.hom :=
    CategoryTheory.Limits.pullback.lift_fst _ _ h4
  let v : W₂ ⟶ W := CategoryTheory.Over.homMk vL
    (by
      show vL ≫ (snd ≫ J.hom) = snd₂ ≫ J.hom
      exact (CategoryTheory.Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ J.hom) hv_snd).trans
        ((CategoryTheory.Category.assoc _ _ _).trans
        ((congrArg (wL ≫ ·) hact).trans
        ((CategoryTheory.Category.assoc _ _ _).symm.trans (congrArg (· ≫ J.hom) hw_snd))))))
  haveI hm : mL.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨CategoryTheory.Over.w_assoc m _⟩
  haveI hw : wL.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨CategoryTheory.Over.w_assoc w _⟩
  haveI hv : vL.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨CategoryTheory.Over.w_assoc v _⟩
  haveI hsnd : snd.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.Over.w_assoc (CategoryTheory.Over.homMk snd rfl : W ⟶ J) _⟩
  haveI hsnd₂ : snd₂.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.Over.w_assoc (CategoryTheory.Over.homMk snd₂ rfl : W₂ ⟶ J) _⟩
  haveI hactO : act'.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.Over.w_assoc (e.homEquiv.symm x) _⟩
  haveI := isOver_comp_of_isOver (k := k) mL snd
  haveI := isOver_comp_of_isOver (k := k) vL snd
  haveI := isOver_comp_of_isOver (k := k) wL snd
  haveI := isOver_comp_of_isOver (k := k) wL act'
  have hl : lam ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (W.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    jetRescalingAction_lam_over (k := k) Z s hs r
  have hlm : (mL ≫ lam) ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (W₂.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    rw [CategoryTheory.Category.assoc, hl]
    exact hm.comp_over
  have hlv : (vL ≫ lam) ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (W₂.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    rw [CategoryTheory.Category.assoc, hl]
    exact hv.comp_over
  have hlw : (wL ≫ lam) ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (W₂.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    rw [CategoryTheory.Category.assoc, hl]
    exact hw.comp_over
  have hprod : (p ≫ mulL) ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (W₂.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    (congrArg (· ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) hm_fst).symm.trans hlm
  have hff : (p ≫ CategoryTheory.Limits.pullback.fst G.hom G.hom) ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (W₂.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    (congrArg (· ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) hv_fst).symm.trans hlv
  have hfs : (p ≫ CategoryTheory.Limits.pullback.snd G.hom G.hom) ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (W₂.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    (congrArg (· ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) hw_fst).symm.trans hlw
  have hlift : CategoryTheory.Limits.pullback.lift (p ≫ CategoryTheory.Limits.pullback.fst G.hom G.hom)
      (p ≫ CategoryTheory.Limits.pullback.snd G.hom G.hom) (hff.trans hfs.symm) = p :=
    CategoryTheory.Limits.pullback.hom_ext (CategoryTheory.Limits.pullback.lift_fst _ _ _)
      (CategoryTheory.Limits.pullback.lift_snd _ _ _)
  have hlm' : (CategoryTheory.Limits.pullback.lift (p ≫ CategoryTheory.Limits.pullback.fst G.hom G.hom)
      (p ≫ CategoryTheory.Limits.pullback.snd G.hom G.hom) (hff.trans hfs.symm) ≫ mulL) ≫
      (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (W₂.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    (congrArg (fun q => (q ≫ mulL) ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) hlift).trans hprod
  have hact_univ : jetThickeningMap (k := k) r act' ≫ univ = ρ ≫ (jetThickeningMap (k := k) r snd ≫ univ) :=
    congrArg Subtype.val (e.homEquiv.apply_symm_apply x)
  have hnat_m := jetThickening.rescaleBy_naturality (k := k) r W₂.left mL lam hl hlm
  have hnat_v := jetThickening.rescaleBy_naturality (k := k) r W₂.left vL lam hl hlv
  have hnat_w := jetThickening.rescaleBy_naturality (k := k) r W₂.left wL lam hl hlw
  have hmap_m : jetThickeningMap (k := k) r mL ≫ jetThickeningMap (k := k) r snd =
      jetThickeningMap (k := k) r snd₂ :=
    (jetThickeningMap_comp (k := k) r mL snd).symm.trans (jetThickeningMap_congr_hom (k := k) r hm_snd)
  have hmap_w : jetThickeningMap (k := k) r wL ≫ jetThickeningMap (k := k) r snd =
      jetThickeningMap (k := k) r snd₂ :=
    (jetThickeningMap_comp (k := k) r wL snd).symm.trans (jetThickeningMap_congr_hom (k := k) r hw_snd)
  have hmap_v : jetThickeningMap (k := k) r vL ≫ jetThickeningMap (k := k) r snd =
      jetThickeningMap (k := k) r wL ≫ jetThickeningMap (k := k) r act' :=
    (jetThickeningMap_comp (k := k) r vL snd).symm.trans
      ((jetThickeningMap_congr_hom (k := k) r hv_snd).trans (jetThickeningMap_comp (k := k) r wL act'))
  have hL : (F.map m.op x).1 =
      jetThickening.rescaleBy (k := k) r W₂.left (p ≫ mulL) hprod ≫ (jetThickeningMap (k := k) r snd₂ ≫ univ) := by
    show jetThickeningMap (k := k) r mL ≫ (ρ ≫ (jetThickeningMap (k := k) r snd ≫ univ)) = _
    exact (CategoryTheory.Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (jetThickeningMap (k := k) r snd ≫ univ)) hnat_m).trans
      ((congrArg (fun q => (q ≫ jetThickeningMap (k := k) r mL) ≫ (jetThickeningMap (k := k) r snd ≫ univ))
          (jetThickening.rescaleBy_congr (k := k) r W₂.left _ hm_fst hlm hprod)).trans
      ((CategoryTheory.Category.assoc _ _ _).trans
      (congrArg (jetThickening.rescaleBy (k := k) r W₂.left (p ≫ mulL) hprod ≫ ·)
        ((CategoryTheory.Category.assoc _ _ _).symm.trans (congrArg (· ≫ univ) hmap_m))))))
  have hB : jetThickeningMap (k := k) r vL ≫ (jetThickeningMap (k := k) r snd ≫ univ) =
      jetThickening.rescaleBy (k := k) r W₂.left (p ≫ CategoryTheory.Limits.pullback.snd G.hom G.hom) hfs ≫
        (jetThickeningMap (k := k) r snd₂ ≫ univ) :=
    (CategoryTheory.Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ univ) hmap_v).trans
    ((CategoryTheory.Category.assoc _ _ _).trans
    ((congrArg (jetThickeningMap (k := k) r wL ≫ ·) hact_univ).trans
    ((CategoryTheory.Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (jetThickeningMap (k := k) r snd ≫ univ)) hnat_w).trans
    ((congrArg (fun q => (q ≫ jetThickeningMap (k := k) r wL) ≫ (jetThickeningMap (k := k) r snd ≫ univ))
        (jetThickening.rescaleBy_congr (k := k) r W₂.left _ hw_fst hlw hfs)).trans
    ((CategoryTheory.Category.assoc _ _ _).trans
    (congrArg (jetThickening.rescaleBy (k := k) r W₂.left (p ≫ CategoryTheory.Limits.pullback.snd G.hom G.hom) hfs ≫ ·)
      ((CategoryTheory.Category.assoc _ _ _).symm.trans (congrArg (· ≫ univ) hmap_w))))))))))
  have hC : jetThickening.rescaleBy (k := k) r W₂.left (p ≫ CategoryTheory.Limits.pullback.fst G.hom G.hom) hff ≫
      (jetThickening.rescaleBy (k := k) r W₂.left (p ≫ CategoryTheory.Limits.pullback.snd G.hom G.hom) hfs ≫
        (jetThickeningMap (k := k) r snd₂ ≫ univ)) =
      jetThickening.rescaleBy (k := k) r W₂.left (p ≫ mulL) hprod ≫ (jetThickeningMap (k := k) r snd₂ ≫ univ) :=
    (CategoryTheory.Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (jetThickeningMap (k := k) r snd₂ ≫ univ))
      (jetThickening.rescaleBy_mul (k := k) r W₂.left (p ≫ CategoryTheory.Limits.pullback.fst G.hom G.hom)
        (p ≫ CategoryTheory.Limits.pullback.snd G.hom G.hom) hff hfs hlm')).trans
    (congrArg (· ≫ (jetThickeningMap (k := k) r snd₂ ≫ univ))
      (jetThickening.rescaleBy_congr (k := k) r W₂.left _ (congrArg (· ≫ mulL) hlift) hlm' hprod)))
  have hR : (F.map v.op x).1 =
      jetThickening.rescaleBy (k := k) r W₂.left (p ≫ mulL) hprod ≫ (jetThickeningMap (k := k) r snd₂ ≫ univ) := by
    show jetThickeningMap (k := k) r vL ≫ (ρ ≫ (jetThickeningMap (k := k) r snd ≫ univ)) = _
    exact (CategoryTheory.Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (jetThickeningMap (k := k) r snd ≫ univ)) hnat_v).trans
      ((congrArg (fun q => (q ≫ jetThickeningMap (k := k) r vL) ≫ (jetThickeningMap (k := k) r snd ≫ univ))
          (jetThickening.rescaleBy_congr (k := k) r W₂.left _ hv_fst hlv hff)).trans
      ((CategoryTheory.Category.assoc _ _ _).trans
      ((congrArg (jetThickening.rescaleBy (k := k) r W₂.left (p ≫ CategoryTheory.Limits.pullback.fst G.hom G.hom) hff ≫ ·)
        hB).trans hC))))
  have hx : F.map m.op x = F.map v.op x := Subtype.ext (hL.trans hR.symm)
  show (m ≫ e.homEquiv.symm x).left = (v ≫ e.homEquiv.symm x).left
  rw [e.comp_homEquiv_symm, e.comp_homEquiv_symm, hx]

/-- The `𝔾_m`-rescaling action on the relative jet scheme, constructed by Yoneda from the representability data
`relativeJetScheme.representableBy`: `W := 𝔾_m ×_k J` (over `C` via the second projection), `λ :=` the first
projection; pulling back the universal based jet along `W → J` gives `φ₀ : W ×_k D_r → Z`, and precomposing with
`ρ_λ : W ×_k D_r → W ×_k D_r` (`t ↦ λt`, given by `jetBaseRescaling`) yields the based jet `λ · φ₀`, whose
corresponding morphism `W ⟶ J` is the action. -/

noncomputable def jetRescalingAction {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    GmActionOver k (relativeJetScheme (k := k) Z s hs r) :=
  let F := relativeJetFunctor (k := k) Z s hs r
  let J := relativeJetScheme (k := k) Z s hs r
  let e := relativeJetScheme.representableBy (k := k) Z s hs r
  let W : CategoryTheory.Over C := CategoryTheory.Over.mk
    (CategoryTheory.Limits.pullback.snd (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ J.hom)
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  let lam : W.left ⟶ Gm k := CategoryTheory.Limits.pullback.fst _ _
  let ρ : jetThickening (k := k) r W.left ⟶ jetThickening (k := k) r W.left :=
    jetThickening.rescaleBy (k := k) r W.left lam
      (jetRescalingAction_lam_over (k := k) Z s hs r)
  let x₀ : F.obj (Opposite.op W) :=
    e.homEquiv (CategoryTheory.Over.homMk (CategoryTheory.Limits.pullback.snd _ _) rfl : W ⟶ J)
  let x : F.obj (Opposite.op W) := ⟨ρ ≫ x₀.1, jetRescalingAction_point_prop (k := k) Z s hs r⟩
  { act := (e.homEquiv.symm x).left
    act_over := jetRescalingAction_act_over (k := k) Z s hs r
    one_act := jetRescalingAction_one_act (k := k) Z s hs r (GroupSchemeAction.oneAct_cond _ _)
    mul_act := jetRescalingAction_mul_act (k := k) Z s hs r (GroupSchemeAction.mulAct_cond₁ _)
      (GroupSchemeAction.mulAct_cond₂ _) (GroupSchemeAction.mulAct_cond₃ _ _)
      (GroupSchemeAction.mulAct_cond₄ _ _ _ (jetRescalingAction_act_over (k := k) Z s hs r)) }

end
