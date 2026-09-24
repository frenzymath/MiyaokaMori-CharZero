import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.GmActionOnJetBase
import MiyaokaMori.AlgebraicGeometry.Morphisms.GroupSchemeAction
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetBaseScheme
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetConstantTerm
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetBaseHomExt
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetRescalingActionConstruction
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetThickening
import MiyaokaMori.AlgebraicGeometry.Morphisms.MultiplicativeGroupScheme
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetFunctor
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetRepresentableBy
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetScheme

/-! # Extension of the rescaling action to the affine line

The `𝔾_m`-rescaling action `t ↦ λt` on the relative jet scheme `J = J_r^s(Z/C)` (`jetRescalingAction`, §2 of the
paper) extends to an action of the multiplicative monoid `𝔸¹ = Spec k[λ]`: the coaction
`k[t]/(t^{r+1}) → k[λ] ⊗_k k[t]/(t^{r+1})`, `t ↦ λ ⊗ t`, is well defined because `(λ ⊗ t)^{r+1} = 0`. This module

* builds the `𝔸¹`-version of every piece of the construction of `jetRescalingAction`
  (`jetBaseRescalingA1`, `jetThickening.rescaleByA1`, `affineLineRescalingAct`);
* proves that restricting along `𝔾_m ↪ 𝔸¹` gives back `jetRescalingAction`
  (`affineLineRescalingAct_restrict`), hence `jetRescalingAction_isNonnegative'`;
* proves that the value at `λ = 0` is the constant jet (`affineLineJet.zeroSection_comp_act`:
  `(0, id) ≫ act' = π ≫ c`, where `c = constantJet` is the constant-jet section `C → J`).

These are the geometric inputs of `weightZero_constantJet` (`JetGradingNonnegative`): a weight-`0` function on `J` is
the pullback of its constant term.

Source: §2 of the paper (`S_m` consists of functions homogeneous of weight `m` under parameter rescaling, and
`S_0 = O_C`). The extension of the action to `𝔸¹` is the standard fact behind "nonnegative grading" (the coaction
lands in `O[λ]`, not `O[λ^{±1}]`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## The affine line `A¹ = Spec k[λ]` and its origin -/

/-- The origin `0 : Spec k → A¹` (`λ ↦ 0`), `Spec` of evaluation at `0`. -/
noncomputable def affineLineZero (k : Type u) [Field k] :
    AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))

/-- `0 : Spec k → A¹` is a section of the structure morphism. -/
theorem affineLineZero_comp_structure (k : Type u) [Field k] :
    affineLineZero k ≫ (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘
      AlgebraicGeometry.Spec (CommRingCat.of k)) = CategoryTheory.CategoryStruct.id _ := by
  show AlgebraicGeometry.Spec.map _ ≫ AlgebraicGeometry.Spec.map _ = _
  rw [← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h : (Polynomial.evalRingHom (0 : k)).comp (algebraMap k (Polynomial k)) = RingHom.id k := by
    ext a
    simp
  rw [h]
  simp

/-- The open immersion `i : G_m ↪ A¹`, `Spec` of `k[λ] → k[λ^{±1}]` (`Polynomial.toLaurentAlg`).
Declared with the target `Spec k[λ]` so that all statements below elaborate `Polynomial k` uniformly. -/
noncomputable def affineLineOfGm (k : Type u) [Field k] :
    Gm k ⟶ AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Polynomial.toLaurentAlg (R := k)).toRingHom)

/-! ## `t ↦ λ ⊗ t` on the jet base, with `λ` the coordinate of `A¹` -/

/-- `(λ ⊗ t)^{r+1} = 0`: well-definedness of the `A¹`-coaction
(same proof as `jetBaseRescaling.coaction_wellDefined`). -/
theorem jetBaseRescalingA1.coaction_wellDefined (k : Type u) [Field k] (r : ℕ) :
    Polynomial.eval₂ (algebraMap k (TensorProduct k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)))
      (TensorProduct.tmul k (Polynomial.X : Polynomial k)
        (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1))))
      ((Polynomial.X : Polynomial k) ^ (r + 1)) = 0 := by
  have h : (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1))) ^ (r + 1) = 0 := by
    have := AdjoinRoot.eval₂_root ((Polynomial.X : Polynomial k) ^ (r + 1))
    rwa [Polynomial.eval₂_pow, Polynomial.eval₂_X] at this
  rw [Polynomial.eval₂_pow, Polynomial.eval₂_X, Algebra.TensorProduct.tmul_pow, h,
    TensorProduct.tmul_zero]

/-- The coaction `k[t]/(t^{r+1}) → k[λ] ⊗_k k[t]/(t^{r+1})`, `t ↦ λ ⊗ t`. -/
noncomputable def jetBaseRescalingA1.coaction (k : Type u) [Field k] (r : ℕ) :
    MiyaokaMori.Jet.TruncatedJetRing k r →+* TensorProduct k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r) :=
  AdjoinRoot.lift (algebraMap k (TensorProduct k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)))
    (TensorProduct.tmul k (Polynomial.X : Polynomial k)
      (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1))))
    (jetBaseRescalingA1.coaction_wellDefined k r)

/-- `A¹ ×_k D_r → D_r`, `(λ, t) ↦ λt`. -/
noncomputable def jetBaseRescalingA1 (k : Type u) [Field k] (r : ℕ) :
    CategoryTheory.Limits.pullback
      (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ⟶ jetBase k r :=
  (AlgebraicGeometry.pullbackSpecIso k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)).hom ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (jetBaseRescalingA1.coaction k r))

/-- `jetBaseRescalingA1` is a `k`-morphism (same proof as `jetBaseRescaling_over`). -/
theorem jetBaseRescalingA1_over (k : Type u) [Field k] (r : ℕ) :
    jetBaseRescalingA1 k r ≫ (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      CategoryTheory.Limits.pullback.fst
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  have hco : CommRingCat.ofHom (algebraMap k (MiyaokaMori.Jet.TruncatedJetRing k r)) ≫
      CommRingCat.ofHom (jetBaseRescalingA1.coaction k r) =
      CommRingCat.ofHom (algebraMap k (TensorProduct k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r))) := by
    ext c
    show jetBaseRescalingA1.coaction k r (AdjoinRoot.of _ c) = _
    unfold jetBaseRescalingA1.coaction
    exact AdjoinRoot.lift_of (jetBaseRescalingA1.coaction_wellDefined k r)
  have key : (AlgebraicGeometry.pullbackSpecIso k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)).hom ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (jetBaseRescalingA1.coaction k r)) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (MiyaokaMori.Jet.TruncatedJetRing k r))) =
      CategoryTheory.Limits.pullback.fst _ _ ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) := by
    rw [← AlgebraicGeometry.Spec.map_comp, hco]
    exact AlgebraicGeometry.pullbackSpecIso_hom_base k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)
  exact (CategoryTheory.Category.assoc _ _ _).trans key

/-- `G_m ↪ A¹` (`Spec.map toLaurentAlg`) is a `Spec k`-morphism, stated with the structure morphism
`Gm k ↘ Spec k` (the same statement as `GroupSchemeAction.isNonnegative_cond₁`, which uses `asOver`). -/
theorem Gm_toAffineLine_cond (k : Type u) [Field k] :
    (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫
        CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of k)) =
      affineLineOfGm k ≫
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  GroupSchemeAction.isNonnegative_cond₁

/-- Transport of `pullback.map` along `Spec φ` (`φ : S →ₐ[R] S'`) through `pullbackSpecIso`:
`(Spec φ ×_R 𝟙) ≫ pullbackSpecIso R S T = pullbackSpecIso R S' T ≫ Spec (φ ⊗ id)`.
Stated purely in Mathlib's `Spec.map (ofHom (algebraMap _ _))` form so that `pullback.hom_ext`
together with `pullbackSpecIso_inv_fst/snd` closes it by `simp`; instances of it for our
`↘`-written pullbacks (`specOverSpec`) are obtained by `exact` (definitional unfolding). -/
theorem pullback_map_pullbackSpecIso_hom (R S S' T : Type u) [CommRing R] [CommRing S] [CommRing S']
    [CommRing T] [Algebra R S] [Algebra R S'] [Algebra R T] (φ : S →ₐ[R] S')
    (e₁ : AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S')) ≫
        CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of R)) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (e₂ : AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R T)) ≫
        CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of R)) =
      CategoryTheory.CategoryStruct.id _ ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R T))) :
    CategoryTheory.Limits.pullback.map
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S')))
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R T)))
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R T)))
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ.toRingHom))
        (CategoryTheory.CategoryStruct.id _) (CategoryTheory.CategoryStruct.id _) e₁ e₂ ≫
      (AlgebraicGeometry.pullbackSpecIso R S T).hom =
    (AlgebraicGeometry.pullbackSpecIso R S' T).hom ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map φ (AlgHom.id R T)).toRingHom) := by
  rw [← CategoryTheory.Iso.eq_comp_inv]
  apply CategoryTheory.Limits.pullback.hom_ext
  · simp only [CategoryTheory.Limits.pullback.lift_fst, CategoryTheory.Category.assoc,
      AlgebraicGeometry.pullbackSpecIso_inv_fst, ← AlgebraicGeometry.Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    rw [← AlgebraicGeometry.pullbackSpecIso_hom_fst R S' T, CategoryTheory.Category.assoc,
      ← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
  · simp only [CategoryTheory.Limits.pullback.lift_snd, CategoryTheory.Category.comp_id,
      CategoryTheory.Category.assoc, AlgebraicGeometry.pullbackSpecIso_inv_snd,
      ← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← AlgebraicGeometry.pullbackSpecIso_hom_snd R S' T]
    congr 3
    ext t
    simp

/-- The ring identity behind `jetBaseRescaling_eq_A1`: `(toLaurent ⊗ id) ∘ coactionA1 = coaction`
(both send `t ↦ λ ⊗ t`, and both are `k`-algebra maps). -/
theorem jetBaseRescaling_coaction_eq_map_coactionA1 (k : Type u) [Field k] (r : ℕ) :
    CommRingCat.ofHom (jetBaseRescalingA1.coaction k r) ≫
        CommRingCat.ofHom (Algebra.TensorProduct.map (Polynomial.toLaurentAlg (R := k))
          (AlgHom.id k (MiyaokaMori.Jet.TruncatedJetRing k r))).toRingHom =
      CommRingCat.ofHom (jetBaseRescaling.coaction k r) := by
  apply CommRingCat.hom_ext
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext
  · intro a
    show Algebra.TensorProduct.map (Polynomial.toLaurentAlg (R := k)) (AlgHom.id k (MiyaokaMori.Jet.TruncatedJetRing k r))
        (jetBaseRescalingA1.coaction k r (AdjoinRoot.of _ a)) =
      jetBaseRescaling.coaction k r (AdjoinRoot.of _ a)
    unfold jetBaseRescalingA1.coaction jetBaseRescaling.coaction
    rw [AdjoinRoot.lift_of, AdjoinRoot.lift_of]
    exact AlgHom.commutes _ a
  · show Algebra.TensorProduct.map (Polynomial.toLaurentAlg (R := k)) (AlgHom.id k (MiyaokaMori.Jet.TruncatedJetRing k r))
        (jetBaseRescalingA1.coaction k r (AdjoinRoot.root _)) =
      jetBaseRescaling.coaction k r (AdjoinRoot.root _)
    unfold jetBaseRescalingA1.coaction jetBaseRescaling.coaction
    rw [AdjoinRoot.lift_root, AdjoinRoot.lift_root, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Polynomial.toLaurentAlg_apply, Polynomial.toLaurent_X]

/-- **Leaf.** The `G_m`-rescaling of the jet base factors through the `A¹`-rescaling along
`G_m ↪ A¹` (`Spec.map toLaurentAlg`): `jetBaseRescaling = (i ×_k 𝟙) ≫ jetBaseRescalingA1`.

Proof. Both sides are morphisms `G_m ×_k D_r → D_r = Spec k[t]/(t^{r+1})`.  Write
`e = pullbackSpecIso k k[λ^{±1}] k[t]/(t^{r+1})`, `e' = pullbackSpecIso k k[λ] k[t]/(t^{r+1})`,
`m = Algebra.TensorProduct.map toLaurentAlg (AlgHom.id)` : `k[λ] ⊗ k[t]/(t^{r+1}) → k[λ^{±1}] ⊗ k[t]/(t^{r+1})`.
1. `(i ×_k 𝟙) ≫ e'.hom = e.hom ≫ Spec.map m`: after composing with `e'.inv` on the right this is
   an equality of morphisms into the pullback `A¹ ×_k D_r`, checked on the two projections
   (`pullback.hom_ext`): with `pullbackSpecIso_inv_fst/snd` both sides become
   `fst ≫ Spec.map toLaurentAlg` and `snd` respectively, using `m ∘ includeLeft = includeLeft ∘ toLaurentAlg`
   and `m ∘ includeRight = includeRight` (`Algebra.TensorProduct.map_tmul`).
2. `Spec.map m ≫ Spec.map (coactionA1) = Spec.map (coaction)`: `Spec.map_comp` and the ring identity
   `m ∘ coactionA1 = coaction` — both are ring maps out of `AdjoinRoot (X^{r+1})`; by
   `AdjoinRoot.algHom_ext` (or `Ideal.Quotient.ringHom_ext` + `Polynomial.ringHom_ext`) it suffices
   to compare on the root `t`: `m (λ ⊗ t) = toLaurent λ ⊗ t = T 1 ⊗ t` (`Polynomial.toLaurent_X`),
   and both are `k`-algebra maps (`AdjoinRoot.lift_of`).
Edge cases: `r = 0` (`t = 0`, both coactions are the structure map); none else. -/
theorem jetBaseRescaling_eq_A1 (k : Type u) [Field k] (r : ℕ) :
    jetBaseRescaling k r =
      CategoryTheory.Limits.pullback.map (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (affineLineOfGm k)
          (CategoryTheory.CategoryStruct.id _) (CategoryTheory.CategoryStruct.id _)
          (Gm_toAffineLine_cond k)
          (by rw [CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp]) ≫
        jetBaseRescalingA1 k r := by
  have hA : CategoryTheory.Limits.pullback.map (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (affineLineOfGm k)
        (CategoryTheory.CategoryStruct.id _) (CategoryTheory.CategoryStruct.id _)
        (Gm_toAffineLine_cond k)
        (by rw [CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp]) ≫
        (AlgebraicGeometry.pullbackSpecIso k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)).hom =
      (AlgebraicGeometry.pullbackSpecIso k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)).hom ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map (Polynomial.toLaurentAlg (R := k))
            (AlgHom.id k (MiyaokaMori.Jet.TruncatedJetRing k r))).toRingHom) :=
    pullback_map_pullbackSpecIso_hom k (Polynomial k) (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)
      (Polynomial.toLaurentAlg (R := k)) _ _
  -- `rw` is unusable here (the `↘`-pullback and Mathlib's `Spec.map algebraMap`-pullback agree only
  -- at default transparency); assemble in term mode instead.
  unfold jetBaseRescaling jetBaseRescalingA1
  refine Eq.symm ?_
  refine (CategoryTheory.Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun m => m ≫ AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (jetBaseRescalingA1.coaction k r))) hA).trans ?_
  refine (CategoryTheory.Category.assoc _ _ _).trans ?_
  refine congrArg (fun m => (AlgebraicGeometry.pullbackSpecIso k (LaurentPolynomial k)
    (MiyaokaMori.Jet.TruncatedJetRing k r)).hom ≫ m) ?_
  exact (AlgebraicGeometry.Spec.map_comp _ _).symm.trans
    (congrArg AlgebraicGeometry.Spec.map (jetBaseRescaling_coaction_eq_map_coactionA1 k r))

/-! ## `ρ_λ` for a scalar `λ : V → A¹` (copies of `jetThickening.rescaleParam` / `rescaleBy`) -/

section RescaleByA1

variable {k : Type u} [Field k] (r : ℕ) (V : AlgebraicGeometry.Scheme.{u})
  [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
  (lam : V ⟶ AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)))

/-- `pullback.lift` compatibility for `τ_λ : V ×_k D_r → A¹ ×_k D_r`. -/
theorem jetThickening.rescaleParamA1_cond
    (hlam : lam ≫ (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ lam) ≫
      (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
    CategoryTheory.Limits.pullback.snd (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫
      (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  rw [CategoryTheory.Category.assoc, hlam]
  exact CategoryTheory.Limits.pullback.condition

/-- `τ_λ : V ×_k D_r ⟶ D_r`, `(v, t) ↦ λ(v) t`. -/
noncomputable def jetThickening.rescaleParamA1
    (hlam : lam ≫ (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) : jetThickening (k := k) r V ⟶ jetBase k r :=
  CategoryTheory.Limits.pullback.lift
      (CategoryTheory.Limits.pullback.fst _ _ ≫ lam) (CategoryTheory.Limits.pullback.snd _ _)
      (jetThickening.rescaleParamA1_cond (k := k) r V lam hlam) ≫
    jetBaseRescalingA1 k r

/-- `pullback.lift` compatibility for `ρ_λ`. -/
theorem jetThickening.rescaleByA1_cond
    (hlam : lam ≫ (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
    jetThickening.rescaleParamA1 (k := k) r V lam hlam ≫
      (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  unfold jetThickening.rescaleParamA1
  refine Eq.symm ?_
  refine (CategoryTheory.Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (jetBaseRescalingA1_over k r)).trans ?_
  refine (CategoryTheory.Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (CategoryTheory.Limits.pullback.lift_fst _ _ _)).trans ?_
  refine (CategoryTheory.Category.assoc _ _ _).trans ?_
  exact congrArg (_ ≫ ·) hlam

/-- `ρ_λ : V ×_k D_r ⟶ V ×_k D_r`, `(v, t) ↦ (v, λ(v) t)`. -/
noncomputable def jetThickening.rescaleByA1
    (hlam : lam ≫ (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    jetThickening (k := k) r V ⟶ jetThickening (k := k) r V :=
  CategoryTheory.Limits.pullback.lift (CategoryTheory.Limits.pullback.fst _ _)
    (jetThickening.rescaleParamA1 (k := k) r V lam hlam)
    (jetThickening.rescaleByA1_cond (k := k) r V lam hlam)

@[reassoc]
theorem jetThickening.rescaleByA1_proj
    (hlam : lam ≫ (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    jetThickening.rescaleByA1 (k := k) r V lam hlam ≫ jetThickeningProj (k := k) r V =
      jetThickeningProj (k := k) r V :=
  CategoryTheory.Limits.pullback.lift_fst _ _ _

@[reassoc]
theorem jetThickening.rescaleByA1_snd
    (hlam : lam ≫ (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    jetThickening.rescaleByA1 (k := k) r V lam hlam ≫
        CategoryTheory.Limits.pullback.snd (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      jetThickening.rescaleParamA1 (k := k) r V lam hlam :=
  CategoryTheory.Limits.pullback.lift_snd _ _ _

/-- `ρ_λ` depends only on `λ` (the hypothesis `hlam` is a proof). -/
theorem jetThickening.rescaleByA1_congr {lam' : V ⟶ AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k))}
    (h : lam = lam')
    (hlam : lam ≫ (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (hlam' : lam' ≫ (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    jetThickening.rescaleByA1 (k := k) r V lam hlam = jetThickening.rescaleByA1 (k := k) r V lam' hlam' := by
  subst h
  rfl

/-- The coordinate `λ ∈ Γ(A¹, O)` of the affine line `A¹ = Spec k[λ]`. -/
noncomputable def affineLineCoordinate : Γ(AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)), ⊤) :=
  (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom Polynomial.X

/-- The comorphism of `(a, b) ↦ a·b : W → A¹ ×_k D_r → D_r` on the parameter:
`t ↦ a^♯(λ) · b^♯(t)`.

Proof. `(lift a b ≫ e.hom ≫ Spec.map coactionA1).appTop = (Spec.map coactionA1).appTop ≫ e.hom.appTop ≫ (lift a b).appTop`
(`Scheme.comp_appTop`).  `(Spec.map coactionA1).appTop (ΓSpecIso.inv t) = ΓSpecIso.inv (coactionA1 t)`
(`Scheme.ΓSpecIso_inv_naturality`) and `coactionA1 t = λ ⊗ t = (λ ⊗ 1) * (1 ⊗ t)`
(`AdjoinRoot.lift_root`, `Algebra.TensorProduct.tmul_mul_tmul`).  For `e = pullbackSpecIso`,
`e.hom.appTop (ΓSpecIso.inv (x ⊗ 1)) = fst.appTop (ΓSpecIso.inv x)` and
`e.hom.appTop (ΓSpecIso.inv (1 ⊗ y)) = snd.appTop (ΓSpecIso.inv y)` (apply `appTop` to
`pullbackSpecIso_hom_fst`/`_snd` and use `ΓSpecIso_inv_naturality` for `Spec.map includeLeft/Right`).
Finally `lift a b ≫ fst = a`, `lift a b ≫ snd = b` (`pullback.lift_fst/snd`), and `appTop` of a
morphism is a ring map (`map_mul`).  Here `jetBase k r = Spec k[t]/(t^{r+1})` with `t = jetProjection X`
(`Jet.TruncatedJetRing k r` is an abbreviation of `AdjoinRoot (X^{r+1})`, and `AdjoinRoot.root = jetProjection X`,
`Jet.jetProjection_X`).
Edge cases: `r = 0` (`t = 0`, both sides `0`). -/
theorem jetBaseRescalingA1_lift_appTop_parameter {W : AlgebraicGeometry.Scheme.{u}}
    (a : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k))) (b : W ⟶ jetBase k r)
    (hab : a ≫ (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      b ≫ (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    (CategoryTheory.Limits.pullback.lift a b hab ≫ jetBaseRescalingA1 k r).appTop.hom (JetBase.parameter (k := k) r) =
      a.appTop.hom (affineLineCoordinate (k := k)) * b.appTop.hom (JetBase.parameter (k := k) r) := by
  have h1 : (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (jetBaseRescalingA1.coaction k r))).appTop.hom (JetBase.parameter (k := k) r) =
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (TensorProduct k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)))).inv.hom
        (TensorProduct.tmul k (Polynomial.X : Polynomial k) (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1)))) := by
    have h := congrArg (fun φ : CommRingCat.of (MiyaokaMori.Jet.TruncatedJetRing k r) ⟶
        Γ(AlgebraicGeometry.Spec (CommRingCat.of (TensorProduct k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r))), ⊤) =>
        φ.hom (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1))))
      (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (jetBaseRescalingA1.coaction k r)))
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at h
    simp only [RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    show (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (jetBaseRescalingA1.coaction k r))).appTop.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (MiyaokaMori.Jet.TruncatedJetRing k r))).inv.hom
        (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1)))) = _
    rw [← h]
    show (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (TensorProduct k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)))).inv.hom
      ((jetBaseRescalingA1.coaction k r) (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1)))) = _
    unfold jetBaseRescalingA1.coaction
    rw [AdjoinRoot.lift_root]
  have h2 : (AlgebraicGeometry.pullbackSpecIso k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)).hom.appTop.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (TensorProduct k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)))).inv.hom
        (TensorProduct.tmul k (Polynomial.X : Polynomial k) 1)) =
      (AlgebraicGeometry.Scheme.Hom.appTop (CategoryTheory.Limits.pullback.fst
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).hom (affineLineCoordinate (k := k)) := by
    have h := congrArg (fun m : CategoryTheory.Limits.pullback _ _ ⟶ AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) =>
        m.appTop.hom (affineLineCoordinate (k := k)))
      (AlgebraicGeometry.pullbackSpecIso_hom_fst k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r))
    refine Eq.trans ?_ h
    have hn := congrArg (fun φ : CommRingCat.of (Polynomial k) ⟶
        Γ(AlgebraicGeometry.Spec (CommRingCat.of (TensorProduct k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r))), ⊤) =>
        φ.hom Polynomial.X)
      (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Polynomial k →+* TensorProduct k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r))))
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at hn
    simp only [RingHom.comp_apply, CommRingCat.hom_ofHom, Algebra.TensorProduct.includeLeftRingHom_apply] at hn
    show _ = (AlgebraicGeometry.pullbackSpecIso k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)).hom.appTop.hom
      ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom Polynomial.X))
    rw [← hn]
  have h3 : (AlgebraicGeometry.pullbackSpecIso k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)).hom.appTop.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (TensorProduct k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)))).inv.hom
        (TensorProduct.tmul k 1 (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1))))) =
      (AlgebraicGeometry.Scheme.Hom.appTop (CategoryTheory.Limits.pullback.snd
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).hom (JetBase.parameter (k := k) r) := by
    have h := congrArg (fun m : CategoryTheory.Limits.pullback _ _ ⟶ AlgebraicGeometry.Spec (CommRingCat.of (MiyaokaMori.Jet.TruncatedJetRing k r)) =>
        m.appTop.hom ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (MiyaokaMori.Jet.TruncatedJetRing k r))).inv.hom
          (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1)))))
      (AlgebraicGeometry.pullbackSpecIso_hom_snd k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r))
    refine Eq.trans ?_ h
    have hn := congrArg (fun φ : CommRingCat.of (MiyaokaMori.Jet.TruncatedJetRing k r) ⟶
        Γ(AlgebraicGeometry.Spec (CommRingCat.of (TensorProduct k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r))), ⊤) =>
        φ.hom (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1))))
      (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : MiyaokaMori.Jet.TruncatedJetRing k r →ₐ[k] TensorProduct k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)).toRingHom))
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at hn
    simp only [RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
    show _ = (AlgebraicGeometry.pullbackSpecIso k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)).hom.appTop.hom
      ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight).toRingHom)).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (MiyaokaMori.Jet.TruncatedJetRing k r))).inv.hom (AdjoinRoot.root _)))
    rw [← hn]
    rfl
  have htm : (TensorProduct.tmul k (Polynomial.X : Polynomial k) (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1))) :
      TensorProduct k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)) =
      TensorProduct.tmul k (Polynomial.X : Polynomial k) 1 * TensorProduct.tmul k 1 (AdjoinRoot.root _) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h4 := congrArg (fun m : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) => m.appTop.hom (affineLineCoordinate (k := k)))
    (CategoryTheory.Limits.pullback.lift_fst a b hab)
  have h5 := congrArg (fun m : W ⟶ jetBase k r => m.appTop.hom (JetBase.parameter (k := k) r))
    (CategoryTheory.Limits.pullback.lift_snd a b hab)
  show (CategoryTheory.Limits.pullback.lift a b hab).appTop.hom
    ((AlgebraicGeometry.pullbackSpecIso k (Polynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)).hom.appTop.hom
      ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom (jetBaseRescalingA1.coaction k r))).appTop.hom (JetBase.parameter (k := k) r))) = _
  rw [h1, htm, map_mul, map_mul, h2, h3]
  refine (map_mul (CategoryTheory.Limits.pullback.lift a b hab).appTop.hom _ _).trans ?_
  exact congrArg₂ (· * ·) h4 h5

/-- `τ'_λ` on the parameter: `t ↦ pr^♯(λ) · t`. -/
theorem jetThickening.rescaleParamA1_appTop_parameter
    (hlam : lam ≫ (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    (jetThickening.rescaleParamA1 (k := k) r V lam hlam).appTop.hom (JetBase.parameter (k := k) r) =
      (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ lam).appTop.hom (affineLineCoordinate (k := k)) *
        (CategoryTheory.Limits.pullback.snd (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop.hom (JetBase.parameter (k := k) r) := by
  delta jetThickening.rescaleParamA1 jetThickening
  exact jetBaseRescalingA1_lift_appTop_parameter (k := k) r _ _ _

/-- The lift `(λ₀, t) : V ×_k D_r → G_m ×_k D_r` followed by `G_m ↪ A¹` is the lift of `(λ₀ ≫ i, t)`. -/
theorem jetThickening.liftGm_comp_map (lam₀ : V ⟶ Gm k)
    (hlam₀ : lam₀ ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (hlam : (lam₀ ≫ affineLineOfGm k) ≫
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    CategoryTheory.Limits.pullback.lift
        (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ lam₀)
        (CategoryTheory.Limits.pullback.snd _ _) (jetThickening.rescaleParam_cond (k := k) r V lam₀ hlam₀) ≫
      CategoryTheory.Limits.pullback.map (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (affineLineOfGm k)
        (CategoryTheory.CategoryStruct.id _) (CategoryTheory.CategoryStruct.id _)
        (Gm_toAffineLine_cond k)
        (by rw [CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp]) =
    CategoryTheory.Limits.pullback.lift
      (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫
        lam₀ ≫ affineLineOfGm k)
      (CategoryTheory.Limits.pullback.snd _ _) (jetThickening.rescaleParamA1_cond (k := k) r V _ hlam) := by
  apply CategoryTheory.Limits.pullback.hom_ext
  · rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.lift_fst,
      CategoryTheory.Limits.pullback.lift_fst, CategoryTheory.Limits.pullback.lift_fst_assoc,
      CategoryTheory.Category.assoc]
  · rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.lift_snd,
      CategoryTheory.Limits.pullback.lift_snd, CategoryTheory.Category.comp_id,
      CategoryTheory.Limits.pullback.lift_snd]

/-- `τ_λ = τ'_{λ ≫ i}`: the `G_m`-rescaling parameter map is the `A¹` one along `G_m ↪ A¹`. -/
theorem jetThickening.rescaleParam_eq_rescaleParamA1 (lam₀ : V ⟶ Gm k)
    (hlam₀ : lam₀ ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (hlam : (lam₀ ≫ affineLineOfGm k) ≫
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    jetThickening.rescaleParam (k := k) r V lam₀ hlam₀ =
      jetThickening.rescaleParamA1 (k := k) r V
        (lam₀ ≫ affineLineOfGm k) hlam := by
  delta jetThickening.rescaleParam jetThickening.rescaleParamA1
  refine (congrArg (fun m => CategoryTheory.CategoryStruct.comp
    (CategoryTheory.Limits.pullback.lift
      (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ lam₀)
      (CategoryTheory.Limits.pullback.snd _ _) (jetThickening.rescaleParam_cond (k := k) r V lam₀ hlam₀)) m)
    (jetBaseRescaling_eq_A1 k r)).trans ?_
  refine (CategoryTheory.Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ jetBaseRescalingA1 k r) (jetThickening.liftGm_comp_map (k := k) r V lam₀ hlam₀ hlam)

/-- A `k`-morphism `λ₀ : V → G_m` composed with `G_m ↪ A¹` is a `k`-morphism to `A¹`. -/
theorem Gm_lam_over_A1 (lam₀ : V ⟶ Gm k)
    (hlam₀ : lam₀ ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    (lam₀ ≫ affineLineOfGm k) ≫
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  rw [CategoryTheory.Category.assoc, ← Gm_toAffineLine_cond, CategoryTheory.Category.comp_id, hlam₀]

/-- The `G_m`-rescaling is the `A¹`-rescaling along `G_m ↪ A¹`. -/
theorem jetThickening.rescaleBy_eq_rescaleByA1 (lam₀ : V ⟶ Gm k)
    (hlam₀ : lam₀ ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (hlam : (lam₀ ≫ affineLineOfGm k) ≫
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    jetThickening.rescaleBy (k := k) r V lam₀ hlam₀ =
      jetThickening.rescaleByA1 (k := k) r V
        (lam₀ ≫ affineLineOfGm k) hlam := by
  apply CategoryTheory.Limits.pullback.hom_ext
  · show jetThickening.rescaleBy (k := k) r V lam₀ hlam₀ ≫ jetThickeningProj (k := k) r V =
      jetThickening.rescaleByA1 (k := k) r V _ hlam ≫ jetThickeningProj (k := k) r V
    rw [jetThickening.rescaleBy_proj, jetThickening.rescaleByA1_proj]
  · show jetThickening.rescaleBy (k := k) r V lam₀ hlam₀ ≫ CategoryTheory.Limits.pullback.snd _ _ =
      jetThickening.rescaleByA1 (k := k) r V _ hlam ≫ CategoryTheory.Limits.pullback.snd _ _
    rw [jetThickening.rescaleBy_snd, jetThickening.rescaleByA1_snd]
    exact jetThickening.rescaleParam_eq_rescaleParamA1 (k := k) r V lam₀ hlam₀ hlam

/-- `0 : Spec k → A¹` kills the coordinate `λ`. -/
theorem affineLineZero_appTop_X :
    (affineLineZero k).appTop.hom (affineLineCoordinate (k := k)) = 0 := by
  have h := congrArg (fun φ : CommRingCat.of (Polynomial k) ⟶ Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤) =>
      φ.hom Polynomial.X)
    (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at h
  simp only [RingHom.comp_apply, CommRingCat.hom_ofHom, Polynomial.coe_evalRingHom,
    Polynomial.eval_X, map_zero] at h
  exact h.symm

/-- `ρ_0 = pr ≫ (constant term)`: rescaling by `λ = 0` (through `V → Spec k → A¹`) is the
projection followed by the constant-term section. -/
theorem jetThickening.rescaleByA1_zero
    (hlam : ((V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ affineLineZero k) ≫
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    jetThickening.rescaleByA1 (k := k) r V ((V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ affineLineZero k) hlam =
      jetThickeningProj (k := k) r V ≫ jetConstantTerm (k := k) r V := by
  apply CategoryTheory.Limits.pullback.hom_ext
  · show jetThickening.rescaleByA1 (k := k) r V _ hlam ≫ jetThickeningProj (k := k) r V =
      (jetThickeningProj (k := k) r V ≫ jetConstantTerm (k := k) r V) ≫ jetThickeningProj (k := k) r V
    rw [jetThickening.rescaleByA1_proj, CategoryTheory.Category.assoc, jetConstantTerm_comp_proj,
      CategoryTheory.Category.comp_id]
  · show jetThickening.rescaleByA1 (k := k) r V _ hlam ≫ CategoryTheory.Limits.pullback.snd _ _ =
      jetThickeningProj (k := k) r V ≫ (jetConstantTerm (k := k) r V ≫ CategoryTheory.Limits.pullback.snd _ _)
    rw [jetThickening.rescaleByA1_snd, jetConstantTerm_comp_snd]
    letI : (jetThickening (k := k) r V).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨jetThickeningProj (k := k) r V ≫ (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    apply JetBase.hom_ext_of_over (k := k) r
    · exact (jetThickening.rescaleByA1_cond (k := k) r V _ hlam).symm
    · rw [CategoryTheory.Category.assoc, CategoryTheory.Category.assoc, jetBaseZero_comp_structure,
        CategoryTheory.Category.comp_id]
      rfl
    · rw [jetThickening.rescaleParamA1_appTop_parameter]
      have h1 : (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫
            (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ affineLineZero k).appTop.hom
            (affineLineCoordinate (k := k)) = 0 := by
        show (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop.hom
            ((V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop.hom
              ((affineLineZero k).appTop.hom (affineLineCoordinate (k := k)))) = 0
        rw [affineLineZero_appTop_X, map_zero, map_zero]
      rw [h1, zero_mul]
      symm
      show (jetThickeningProj (k := k) r V).appTop.hom
        ((V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop.hom
          ((jetBaseZero k r).appTop.hom (JetBase.parameter (k := k) r))) = 0
      rw [JetBase.zero_appTop_parameter, map_zero, map_zero]

/-- `ρ_λ` fixes `t = 0`: `(constant term) ≫ ρ_λ = (constant term)`. -/
theorem jetConstantTerm_comp_rescaleByA1
    (hlam : lam ≫ (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    jetConstantTerm (k := k) r V ≫ jetThickening.rescaleByA1 (k := k) r V lam hlam =
      jetConstantTerm (k := k) r V := by
  apply CategoryTheory.Limits.pullback.hom_ext
  · show jetConstantTerm (k := k) r V ≫ (jetThickening.rescaleByA1 (k := k) r V lam hlam ≫
        jetThickeningProj (k := k) r V) = jetConstantTerm (k := k) r V ≫ jetThickeningProj (k := k) r V
    rw [jetThickening.rescaleByA1_proj]
  · show jetConstantTerm (k := k) r V ≫ (jetThickening.rescaleByA1 (k := k) r V lam hlam ≫
        CategoryTheory.Limits.pullback.snd _ _) = jetConstantTerm (k := k) r V ≫ CategoryTheory.Limits.pullback.snd _ _
    rw [jetThickening.rescaleByA1_snd, jetConstantTerm_comp_snd]
    apply JetBase.hom_ext_of_over (k := k) r
    · rw [CategoryTheory.Category.assoc, ← jetThickening.rescaleByA1_cond (k := k) r V lam hlam]
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
        ((jetThickening.rescaleParamA1 (k := k) r V lam hlam).appTop.hom (JetBase.parameter (k := k) r)) = 0
      refine (congrArg (jetConstantTerm (k := k) r V).appTop.hom
        (jetThickening.rescaleParamA1_appTop_parameter (k := k) r V lam hlam)).trans ?_
      refine (map_mul _ _ _).trans ?_
      rw [h2, mul_zero]

/-- `jetThickeningMap` depends only on the morphism (the `IsOver` instance is a proof).
Kept under its original name for downstream users (`JetGradingNonnegative`); the lemma itself now lives
upstream as `jetThickeningMap_congr_hom` (`JetRescalingActionConstruction.lean`). -/
theorem jetThickeningMap_congr {V' : AlgebraicGeometry.Scheme.{u}}
    [V'.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {g g' : V ⟶ V'} (e : g = g')
    [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [g'.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    jetThickeningMap (k := k) r g = jetThickeningMap (k := k) r g' :=
  jetThickeningMap_congr_hom (k := k) r e

/-- `ρ'_λ` is natural in the base: `(g × 𝟙) ≫ ρ'_λ = ρ'_{g ≫ λ} ≫ (g × 𝟙)`. -/
theorem jetThickening.rescaleByA1_naturality {V' : AlgebraicGeometry.Scheme.{u}}
    [V'.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (g : V ⟶ V')
    [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (lam' : V' ⟶ AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)))
    (hlam' : lam' ≫ (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V' ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (hlam : (g ≫ lam') ≫ (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    jetThickeningMap (k := k) r g ≫ jetThickening.rescaleByA1 (k := k) r V' lam' hlam' =
      jetThickening.rescaleByA1 (k := k) r V (g ≫ lam') hlam ≫ jetThickeningMap (k := k) r g := by
  have hl : CategoryTheory.Limits.pullback.map (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (V' ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) g
        (CategoryTheory.CategoryStruct.id _) (CategoryTheory.CategoryStruct.id _) (by simp) (by simp) ≫
      CategoryTheory.Limits.pullback.lift
        (CategoryTheory.Limits.pullback.fst (V' ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ lam')
        (CategoryTheory.Limits.pullback.snd _ _) (jetThickening.rescaleParamA1_cond (k := k) r V' lam' hlam') =
      CategoryTheory.Limits.pullback.lift
        (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ g ≫ lam')
        (CategoryTheory.Limits.pullback.snd _ _) (jetThickening.rescaleParamA1_cond (k := k) r V (g ≫ lam') hlam) := by
    apply CategoryTheory.Limits.pullback.hom_ext
    · rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.lift_fst,
        CategoryTheory.Limits.pullback.lift_fst, CategoryTheory.Limits.pullback.lift_fst_assoc,
        CategoryTheory.Category.assoc]
    · rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.lift_snd,
        CategoryTheory.Limits.pullback.lift_snd, CategoryTheory.Limits.pullback.lift_snd,
        CategoryTheory.Category.comp_id]
  have helper : jetThickeningMap (k := k) r g ≫ jetThickening.rescaleParamA1 (k := k) r V' lam' hlam' =
      jetThickening.rescaleParamA1 (k := k) r V (g ≫ lam') hlam := by
    delta jetThickeningMap jetThickening.rescaleParamA1 jetThickening
    rw [← CategoryTheory.Category.assoc, hl]
  apply CategoryTheory.Limits.pullback.hom_ext
  · show (jetThickeningMap (k := k) r g ≫ jetThickening.rescaleByA1 (k := k) r V' lam' hlam') ≫
        jetThickeningProj (k := k) r V' =
      (jetThickening.rescaleByA1 (k := k) r V (g ≫ lam') hlam ≫ jetThickeningMap (k := k) r g) ≫
        jetThickeningProj (k := k) r V'
    rw [CategoryTheory.Category.assoc, jetThickening.rescaleByA1_proj, jetThickeningMap_proj,
      CategoryTheory.Category.assoc, jetThickeningMap_proj, jetThickening.rescaleByA1_proj_assoc]
  · exact ((CategoryTheory.Category.assoc _ _ _).trans
      ((congrArg (jetThickeningMap (k := k) r g ≫ ·) (jetThickening.rescaleByA1_snd (k := k) r V' lam' hlam')).trans
        helper)).trans
      (((CategoryTheory.Category.assoc _ _ _).trans
        ((congrArg (jetThickening.rescaleByA1 (k := k) r V (g ≫ lam') hlam ≫ ·) (jetThickeningMap_snd (k := k) r g)).trans
          (jetThickening.rescaleByA1_snd (k := k) r V (g ≫ lam') hlam))).symm)

end RescaleByA1


/-! ## The `A¹`-rescaling action on the relative jet scheme -/

section AffineLineJet

variable {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C)
    [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)

/-- `W' := A¹ ×_k J` as a `C`-scheme (via the second projection and `π : J → C`). -/
noncomputable def affineLineJet : CategoryTheory.Over C :=
  CategoryTheory.Over.mk
    (CategoryTheory.Limits.pullback.snd
      (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫
      (relativeJetScheme (k := k) Z s hs r).hom)

/-- `λ : W' → A¹`, the first projection. -/
noncomputable def affineLineJet.lam :
    (affineLineJet (k := k) Z s hs r).left ⟶ AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) :=
  CategoryTheory.Limits.pullback.fst _ _

/-- `λ` is a `k`-morphism for the `k`-structure `W'.hom ≫ (C ↘ k)` of `W'.left`. -/
theorem affineLineJet.lam_over :
    letI : (affineLineJet (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(affineLineJet (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    affineLineJet.lam (k := k) Z s hs r ≫
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      ((affineLineJet (k := k) Z s hs r).left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  letI : (affineLineJet (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(affineLineJet (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  show CategoryTheory.Limits.pullback.fst _ _ ≫ _ =
    (CategoryTheory.Limits.pullback.snd _ _ ≫ (relativeJetScheme (k := k) Z s hs r).hom) ≫ _
  rw [CategoryTheory.Limits.pullback.condition, CategoryTheory.Category.assoc]

/-- `ρ' : W' ×_k D_r → W' ×_k D_r`, `t ↦ λt`. -/
noncomputable def affineLineJet.rescale :
    letI : (affineLineJet (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(affineLineJet (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    jetThickening (k := k) r (affineLineJet (k := k) Z s hs r).left ⟶
      jetThickening (k := k) r (affineLineJet (k := k) Z s hs r).left :=
  letI : (affineLineJet (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(affineLineJet (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  jetThickening.rescaleByA1 (k := k) r _ (affineLineJet.lam (k := k) Z s hs r)
    (affineLineJet.lam_over (k := k) Z s hs r)

/-- `x₀'`: the universal based jet pulled back along `pr₂' : W' → J`. -/
noncomputable def affineLineJet.universalPullback :
    (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op (affineLineJet (k := k) Z s hs r)) :=
  (relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv
    (CategoryTheory.Over.homMk (CategoryTheory.Limits.pullback.snd _ _) rfl :
      affineLineJet (k := k) Z s hs r ⟶ relativeJetScheme (k := k) Z s hs r)

/-- `ρ' ≫ x₀'` is again a based jet: it lies over `C` because `ρ'` preserves the projection, and its
constant term is `s` because `ρ'` fixes `t = 0` (`jetConstantTerm_comp_rescaleByA1`). -/
theorem affineLineJet.point_prop :
    letI : (affineLineJet (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(affineLineJet (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    (affineLineJet.rescale (k := k) Z s hs r ≫ (affineLineJet.universalPullback (k := k) Z s hs r).1) ≫ Z.hom =
        jetThickeningProj (k := k) r (affineLineJet (k := k) Z s hs r).left ≫
          (affineLineJet (k := k) Z s hs r).hom ∧
      jetConstantTerm (k := k) r (affineLineJet (k := k) Z s hs r).left ≫
          (affineLineJet.rescale (k := k) Z s hs r ≫ (affineLineJet.universalPullback (k := k) Z s hs r).1) =
        (affineLineJet (k := k) Z s hs r).hom ≫ s := by
  letI : (affineLineJet (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(affineLineJet (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have h := (affineLineJet.universalPullback (k := k) Z s hs r).2
  constructor
  · rw [CategoryTheory.Category.assoc, h.1, ← CategoryTheory.Category.assoc]
    show (jetThickening.rescaleByA1 (k := k) r _ _ _ ≫ jetThickeningProj (k := k) r _) ≫ _ = _
    rw [jetThickening.rescaleByA1_proj]
  · rw [← CategoryTheory.Category.assoc]
    show (jetConstantTerm (k := k) r _ ≫ jetThickening.rescaleByA1 (k := k) r _ _ _) ≫ _ = _
    rw [jetConstantTerm_comp_rescaleByA1, h.2]

/-- The based jet `ρ' ≫ x₀'` over `W'`. -/
noncomputable def affineLineJet.basedJet :
    (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op (affineLineJet (k := k) Z s hs r)) :=
  ⟨affineLineJet.rescale (k := k) Z s hs r ≫ (affineLineJet.universalPullback (k := k) Z s hs r).1,
    affineLineJet.point_prop (k := k) Z s hs r⟩

/-- The `A¹`-rescaling action `act' : A¹ ×_k J → J` (the `C`-morphism corresponding to the based
jet `ρ' ≫ x₀'` under representability). -/
noncomputable def affineLineRescalingAct :
    CategoryTheory.Limits.pullback
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ⟶
      (relativeJetScheme (k := k) Z s hs r).left :=
  ((relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv.symm
    (affineLineJet.basedJet (k := k) Z s hs r)).left

/-- `act'` is over `C`. -/
theorem affineLineRescalingAct_over :
    affineLineRescalingAct (k := k) Z s hs r ≫ (relativeJetScheme (k := k) Z s hs r).hom =
      CategoryTheory.Limits.pullback.snd _ _ ≫ (relativeJetScheme (k := k) Z s hs r).hom :=
  CategoryTheory.Over.w _

/-- `j : G_m ×_k J → A¹ ×_k J` (the map of `GroupSchemeAction.IsNonnegative`). -/
noncomputable def affineLineJet.fromGm :
    CategoryTheory.Limits.pullback (((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom)
        ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ⟶
      (affineLineJet (k := k) Z s hs r).left :=
  CategoryTheory.Limits.pullback.map _ _ _ _
    (affineLineOfGm k)
    (CategoryTheory.CategoryStruct.id _) (CategoryTheory.CategoryStruct.id _)
    GroupSchemeAction.isNonnegative_cond₁
    (GroupSchemeAction.isNonnegative_cond₂ (relativeJetScheme (k := k) Z s hs r))

theorem affineLineJet.fromGm_comp_snd :
    affineLineJet.fromGm (k := k) Z s hs r ≫ CategoryTheory.Limits.pullback.snd _ _ =
      CategoryTheory.Limits.pullback.snd _ _ :=
  (CategoryTheory.Limits.pullback.lift_snd _ _ _).trans (CategoryTheory.Category.comp_id _)

theorem affineLineJet.fromGm_comp_lam :
    affineLineJet.fromGm (k := k) Z s hs r ≫ affineLineJet.lam (k := k) Z s hs r =
      CategoryTheory.Limits.pullback.fst _ _ ≫
        affineLineOfGm k :=
  CategoryTheory.Limits.pullback.lift_fst _ _ _

/-- The zero section `(0, id) : J → A¹ ×_k J`. -/
noncomputable def affineLineJet.zeroSection :
    (relativeJetScheme (k := k) Z s hs r).left ⟶ (affineLineJet (k := k) Z s hs r).left :=
  CategoryTheory.Limits.pullback.lift
    (((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫
      affineLineZero k)
    (CategoryTheory.CategoryStruct.id _)
    (by rw [CategoryTheory.Category.assoc, affineLineZero_comp_structure, CategoryTheory.Category.comp_id,
      CategoryTheory.Category.id_comp])

theorem affineLineJet.zeroSection_comp_snd :
    affineLineJet.zeroSection (k := k) Z s hs r ≫ CategoryTheory.Limits.pullback.snd _ _ =
      CategoryTheory.CategoryStruct.id _ :=
  CategoryTheory.Limits.pullback.lift_snd _ _ _

theorem affineLineJet.zeroSection_comp_lam :
    affineLineJet.zeroSection (k := k) Z s hs r ≫ affineLineJet.lam (k := k) Z s hs r =
      ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫
        affineLineZero k :=
  CategoryTheory.Limits.pullback.lift_fst _ _ _


/-! ### Restriction to `G_m` -/

/-- `j` as a `C`-morphism `W = G_m ×_k J → W' = A¹ ×_k J` (`W` as in `jetRescalingAction`). -/
noncomputable def affineLineJet.fromGmOver :
    CategoryTheory.Over.mk
        (CategoryTheory.Limits.pullback.snd (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫
          (relativeJetScheme (k := k) Z s hs r).hom) ⟶
      affineLineJet (k := k) Z s hs r :=
  CategoryTheory.Over.homMk (affineLineJet.fromGm (k := k) Z s hs r)
    ((CategoryTheory.Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (relativeJetScheme (k := k) Z s hs r).hom) (affineLineJet.fromGm_comp_snd (k := k) Z s hs r)))

/-- Restricting the `A¹`-action along `G_m ↪ A¹` gives back the `G_m`-action `jetRescalingAction`:
`j ≫ act' = act`.  Proof: by naturality of the representing bijection (`comp_homEquiv_symm`) it
suffices that the based jet `j^*(ρ' ≫ x₀')` equals `ρ ≫ x₀`; `(j × 𝟙) ≫ ρ' = ρ'_{j ≫ λ'} ≫ (j × 𝟙)`
(`rescaleByA1_naturality`), `j ≫ λ' = λ ≫ i` and `ρ'_{λ ≫ i} = ρ` (`rescaleBy_eq_rescaleByA1`), and
`(j × 𝟙) ≫ (pr₂' × 𝟙) = (pr₂ × 𝟙)` (`jetThickeningMap_comp`, `j ≫ pr₂' = pr₂`). -/
theorem affineLineRescalingAct_restrict :
    affineLineJet.fromGm (k := k) Z s hs r ≫ affineLineRescalingAct (k := k) Z s hs r =
      (jetRescalingAction (k := k) Z s hs r).act := by
  let F := relativeJetFunctor (k := k) Z s hs r
  let J := relativeJetScheme (k := k) Z s hs r
  let e := relativeJetScheme.representableBy (k := k) Z s hs r
  let W : CategoryTheory.Over C := CategoryTheory.Over.mk
    (CategoryTheory.Limits.pullback.snd (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ J.hom)
  let W' : CategoryTheory.Over C := affineLineJet (k := k) Z s hs r
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : W'.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W'.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : J.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  let lam : W.left ⟶ Gm k := CategoryTheory.Limits.pullback.fst _ _
  let ρ : jetThickening (k := k) r W.left ⟶ jetThickening (k := k) r W.left :=
    jetThickening.rescaleBy (k := k) r W.left lam (jetRescalingAction_lam_over (k := k) Z s hs r)
  let x₀ : F.obj (Opposite.op W) :=
    e.homEquiv (CategoryTheory.Over.homMk (CategoryTheory.Limits.pullback.snd _ _) rfl : W ⟶ J)
  let x : F.obj (Opposite.op W) := ⟨ρ ≫ x₀.1, jetRescalingAction_point_prop (k := k) Z s hs r⟩
  let jO : W ⟶ W' := affineLineJet.fromGmOver (k := k) Z s hs r
  let j : W.left ⟶ W'.left := affineLineJet.fromGm (k := k) Z s hs r
  let snd' : W'.left ⟶ J.left := CategoryTheory.Limits.pullback.snd _ _
  let snd : W.left ⟶ J.left := CategoryTheory.Limits.pullback.snd _ _
  haveI hj : j.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨CategoryTheory.Over.w_assoc jO _⟩
  haveI hsnd' : snd'.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.Over.w_assoc (CategoryTheory.Over.homMk snd' rfl : W' ⟶ J) _⟩
  haveI hsnd : snd.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.Over.w_assoc (CategoryTheory.Over.homMk snd rfl : W ⟶ J) _⟩
  haveI hjsnd : (j ≫ snd').IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(CategoryTheory.Category.assoc j snd' _).trans ((congrArg (j ≫ ·) hsnd'.comp_over).trans hj.comp_over)⟩
  have hjs : j ≫ snd' = snd := affineLineJet.fromGm_comp_snd (k := k) Z s hs r
  have hlam : (j ≫ affineLineJet.lam (k := k) Z s hs r) ≫
      (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (W.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    rw [CategoryTheory.Category.assoc, affineLineJet.lam_over]
    exact hj.comp_over
  have hx : F.map jO.op (affineLineJet.basedJet (k := k) Z s hs r) = x := by
    apply Subtype.ext
    show jetThickeningMap (k := k) r j ≫ (affineLineJet.rescale (k := k) Z s hs r ≫
        (jetThickeningMap (k := k) r snd' ≫ relativeJetScheme.universalJet (k := k) Z s hs r)) =
      ρ ≫ (jetThickeningMap (k := k) r snd ≫ relativeJetScheme.universalJet (k := k) Z s hs r)
    have hnat := jetThickening.rescaleByA1_naturality (k := k) r W.left j
      (affineLineJet.lam (k := k) Z s hs r) (affineLineJet.lam_over (k := k) Z s hs r) hlam
    have hcongr : jetThickening.rescaleByA1 (k := k) r W.left (j ≫ affineLineJet.lam (k := k) Z s hs r) hlam = ρ :=
      (jetThickening.rescaleByA1_congr (k := k) r W.left _ (affineLineJet.fromGm_comp_lam (k := k) Z s hs r) hlam
        (Gm_lam_over_A1 (k := k) W.left lam (jetRescalingAction_lam_over (k := k) Z s hs r))).trans
      (jetThickening.rescaleBy_eq_rescaleByA1 (k := k) r W.left lam
        (jetRescalingAction_lam_over (k := k) Z s hs r) _).symm
    have hmap : jetThickeningMap (k := k) r j ≫ jetThickeningMap (k := k) r snd' = jetThickeningMap (k := k) r snd :=
      (jetThickeningMap_comp (k := k) r j snd').symm.trans
        (jetThickeningMap_congr_hom (k := k) r hjs)
    exact (CategoryTheory.Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (jetThickeningMap (k := k) r snd' ≫ relativeJetScheme.universalJet (k := k) Z s hs r)) hnat).trans
      ((congrArg (fun m => (m ≫ jetThickeningMap (k := k) r j) ≫
          (jetThickeningMap (k := k) r snd' ≫ relativeJetScheme.universalJet (k := k) Z s hs r)) hcongr).trans
      ((CategoryTheory.Category.assoc _ _ _).trans
      ((congrArg (ρ ≫ ·) (CategoryTheory.Category.assoc _ _ _).symm).trans
      (congrArg (fun m => ρ ≫ (m ≫ relativeJetScheme.universalJet (k := k) Z s hs r)) hmap)))))
  show (jO ≫ e.homEquiv.symm (affineLineJet.basedJet (k := k) Z s hs r)).left = (e.homEquiv.symm x).left
  rw [e.comp_homEquiv_symm, hx]

/-- The `G_m`-action `jetRescalingAction` is nonnegative: it extends to `A¹` (witness `act'`), and the
extension is a morphism over `C` (`affineLineRescalingAct_over`; the second component of
`GroupSchemeAction.IsNonnegative`). -/
theorem jetRescalingAction_isNonnegative' :
    (jetRescalingAction (k := k) Z s hs r).IsNonnegative :=
  ⟨affineLineRescalingAct (k := k) Z s hs r, affineLineRescalingAct_restrict (k := k) Z s hs r,
    affineLineRescalingAct_over (k := k) Z s hs r⟩

/-! ### The universal jet is based -/

/-- The universal based jet is based: its constant term is `π ≫ s` (from `toBasedJet_prop` at `𝟙 J`). -/
theorem relativeJetScheme.jetConstantTerm_comp_universalJet :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    jetConstantTerm (k := k) r (relativeJetScheme (k := k) Z s hs r).left ≫
        relativeJetScheme.universalJet (k := k) Z s hs r =
      (relativeJetScheme (k := k) Z s hs r).hom ≫ s := by
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have h := (relativeJetScheme.toBasedJet_prop (k := k) Z s hs r _
    (CategoryTheory.CategoryStruct.id (relativeJetScheme (k := k) Z s hs r))).2
  refine Eq.trans ?_ h
  exact congrArg (jetConstantTerm (k := k) r (relativeJetScheme (k := k) Z s hs r).left ≫ ·)
    ((CategoryTheory.Category.id_comp _).symm.trans
      (congrArg (· ≫ relativeJetScheme.universalJet (k := k) Z s hs r) (jetThickeningMap_id (k := k) r).symm))

end AffineLineJet

end
