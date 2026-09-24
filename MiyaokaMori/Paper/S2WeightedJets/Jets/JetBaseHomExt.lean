import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetBaseClosedPoint
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetBaseScheme

/-! # Extensionality for morphisms into the jet base

Morphisms into the jet base `D_r = Spec k[t]/(t^{r+1})` over `k` are determined by the image of the
parameter `t`, and the comorphism of a morphism into `Spec (A ⊗_k B)` built from `pullback.lift`
multiplies the two components on pure tensors.

* `Spec_map_appTop_ΓSpecIso_inv`: `(Spec.map f).appTop (ΓSpecIso.inv x) = ΓSpecIso.inv (f x)`
  (pointwise form of `Scheme.ΓSpecIso_inv_naturality`).
* `pullbackSpecIso_lift_appTop_tmul`: for `a : W → Spec A`, `b : W → Spec B` over `k`,
  `(lift a b ≫ pullbackSpecIso).appTop (x ⊗ y) = a^♯(x) · b^♯(y)`.
* `JetBase.parameter`, `JetBase.hom_ext_of_over`: `t ∈ Γ(D_r, O)` and the extensionality principle.
* `JetBase.zero_appTop_parameter`: `t ↦ 0` kills `t`.

Source: standard (`Spec` is fully faithful, `Polynomial.ringHom_ext`); §2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Pointwise `ΓSpecIso` naturality: `(Spec.map f).appTop (ΓSpecIso.inv x) = ΓSpecIso.inv (f x)`. -/
theorem Spec_map_appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (f : R ⟶ S) (x : R) :
    (AlgebraicGeometry.Spec.map f).appTop.hom ((AlgebraicGeometry.Scheme.ΓSpecIso R).inv.hom x) =
      (AlgebraicGeometry.Scheme.ΓSpecIso S).inv.hom (f.hom x) := by
  have h := congrArg (fun φ : R ⟶ Γ(AlgebraicGeometry.Spec S, ⊤) => φ.hom x)
    (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality f)
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at h
  simp only [RingHom.comp_apply] at h
  exact h.symm

section SpecTensor

variable {k : Type u} [Field k] {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- The comorphism of `(a, b) : W → Spec A ×_k Spec B ≅ Spec (A ⊗_k B)` on a pure tensor:
`(x ⊗ y) ↦ a^♯(x) · b^♯(y)`.

Proof. `pullbackSpecIso_hom_fst/snd` say `e.hom ≫ Spec.map includeLeft = fst` and
`e.hom ≫ Spec.map includeRight = snd`; applying `appTop` and `Spec_map_appTop_ΓSpecIso_inv` gives
`e.hom.appTop (ΓSpecIso.inv (x ⊗ 1)) = fst.appTop (ΓSpecIso.inv x)` and similarly for `1 ⊗ y`.
Then `x ⊗ y = (x ⊗ 1) * (1 ⊗ y)` (`Algebra.TensorProduct.tmul_mul_tmul`), `appTop` of a morphism is a
ring map (`map_mul`), and `lift a b ≫ fst = a`, `lift a b ≫ snd = b`. -/
theorem pullbackSpecIso_lift_appTop_tmul {W : AlgebraicGeometry.Scheme.{u}}
    (a : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) (b : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of B))
    (hab : a ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      b ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k B))) (x : A) (y : B) :
    (CategoryTheory.Limits.pullback.lift a b hab ≫ (AlgebraicGeometry.pullbackSpecIso k A B).hom).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (TensorProduct k A B))).inv.hom
          (TensorProduct.tmul k x y)) =
      a.appTop.hom ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x) *
        b.appTop.hom ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom y) := by
  have h2 : (AlgebraicGeometry.pullbackSpecIso k A B).hom.appTop.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (TensorProduct k A B))).inv.hom
        (TensorProduct.tmul k x 1)) =
      (CategoryTheory.Limits.pullback.fst (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x) := by
    have h := congrArg (fun m : CategoryTheory.Limits.pullback _ _ ⟶ AlgebraicGeometry.Spec (CommRingCat.of A) =>
        m.appTop.hom ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x))
      (AlgebraicGeometry.pullbackSpecIso_hom_fst k A B)
    refine Eq.trans ?_ h
    show _ = (AlgebraicGeometry.pullbackSpecIso k A B).hom.appTop.hom
      ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* TensorProduct k A B))).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x))
    rw [Spec_map_appTop_ΓSpecIso_inv]
    rfl
  have h3 : (AlgebraicGeometry.pullbackSpecIso k A B).hom.appTop.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (TensorProduct k A B))).inv.hom
        (TensorProduct.tmul k 1 y)) =
      (CategoryTheory.Limits.pullback.snd (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom y) := by
    have h := congrArg (fun m : CategoryTheory.Limits.pullback _ _ ⟶ AlgebraicGeometry.Spec (CommRingCat.of B) =>
        m.appTop.hom ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom y))
      (AlgebraicGeometry.pullbackSpecIso_hom_snd k A B)
    refine Eq.trans ?_ h
    show _ = (AlgebraicGeometry.pullbackSpecIso k A B).hom.appTop.hom
      ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[k] TensorProduct k A B).toRingHom)).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom y))
    rw [Spec_map_appTop_ΓSpecIso_inv]
    rfl
  have htm : (TensorProduct.tmul k x y : TensorProduct k A B) =
      TensorProduct.tmul k x 1 * TensorProduct.tmul k 1 y := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h4 := congrArg (fun m : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of A) =>
      m.appTop.hom ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x))
    (CategoryTheory.Limits.pullback.lift_fst a b hab)
  have h5 := congrArg (fun m : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of B) =>
      m.appTop.hom ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom y))
    (CategoryTheory.Limits.pullback.lift_snd a b hab)
  show (CategoryTheory.Limits.pullback.lift a b hab).appTop.hom
    ((AlgebraicGeometry.pullbackSpecIso k A B).hom.appTop.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (TensorProduct k A B))).inv.hom
        (TensorProduct.tmul k x y))) = _
  rw [htm, map_mul, map_mul, h2, h3]
  refine (map_mul (CategoryTheory.Limits.pullback.lift a b hab).appTop.hom _ _).trans ?_
  exact congrArg₂ (· * ·) h4 h5

end SpecTensor

namespace JetBase

variable {k : Type u} [Field k] (r : ℕ)

/-- The parameter `t ∈ Γ(D_r, O)` of the jet base `D_r = Spec k[t]/(t^{r+1})`. -/
noncomputable def parameter : Γ(jetBase k r, ⊤) :=
  (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r))).inv.hom
    (MiyaokaMori.Jet.jetProjection k r Polynomial.X)

/-- `f.appTop` on `algebraMap a` for a `k`-morphism `f : W → D_r` (naturality of `ΓSpecIso`). -/
theorem appTop_algebraMap {W : AlgebraicGeometry.Scheme.{u}}
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (f : W ⟶ jetBase k r)
    (hf : f ≫ (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) (a : k) :
    f.appTop.hom ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r))).inv.hom
        (algebraMap k (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r) a)) =
      (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a) := by
  have h := congrArg (fun φ : CommRingCat.of k ⟶
      Γ(AlgebraicGeometry.Spec (CommRingCat.of (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r)), ⊤) => φ.hom a)
    (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r))))
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at h
  simp only [RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  rw [h]
  exact congrArg (fun m : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of k) =>
    m.appTop.hom ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)) hf

/-- Morphisms `W → D_r = Spec k[t]/(t^{r+1})` over `k` are determined by the image of the
parameter `t` in `Γ(W, ⊤)`.

Proof. By `AlgebraicGeometry.ext_to_Spec` it suffices to compare the ring maps
`k[t]/(t^{r+1}) → Γ(W, ⊤)` (`ΓSpecIso.inv ≫ f.appTop`).  Both are `k`-algebra maps: composing
`f ≫ (D_r ↘ k) = W ↘ k` with `appTop` and `Scheme.ΓSpecIso_inv_naturality` shows that on
`algebraMap k _ a` both give `(W ↘ k).appTop (ΓSpecIso.inv a)`.  By `Ideal.Quotient.ringHom_ext` and
`Polynomial.ringHom_ext` (`k[t]/(t^{r+1}) = k[X] ⧸ (X^{r+1})`, `Jet.TruncatedJetRing`) a
ring map out of it is determined by its values on the constants and on `X`, i.e. on `t`; the
hypothesis `h` is exactly the agreement on `t = parameter`.
Edge cases: `W = ∅` (`Γ = 0`, trivial); `r = 0` (`t = 0`, only constants). -/
theorem hom_ext_of_over {W : AlgebraicGeometry.Scheme.{u}}
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (f g : W ⟶ jetBase k r)
    (hf : f ≫ (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (hg : g ≫ (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (h : f.appTop.hom (JetBase.parameter (k := k) r) = g.appTop.hom (JetBase.parameter (k := k) r)) :
    f = g := by
  apply AlgebraicGeometry.ext_to_Spec
  rw [AlgebraicGeometry.Scheme.Γ_map, AlgebraicGeometry.Scheme.Γ_map]
  apply CommRingCat.hom_ext
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext
  · intro a
    show f.appTop.hom ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r))).inv.hom
        (algebraMap k (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r) a)) =
      g.appTop.hom ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r))).inv.hom
        (algebraMap k (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r) a))
    rw [JetBase.appTop_algebraMap (k := k) r f hf, JetBase.appTop_algebraMap (k := k) r g hg]
  · exact h

/-- `t ↦ 0 : Spec k → D_r` kills the parameter `t`. -/
theorem zero_appTop_parameter :
    (jetBaseZero k r).appTop.hom (JetBase.parameter (k := k) r) = 0 := by
  have h := congrArg (fun φ : CommRingCat.of (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r) ⟶
        Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤) => φ.hom (MiyaokaMori.Jet.jetProjection k r Polynomial.X))
    (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon (R := k) r)))
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at h
  simp only [RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  rw [MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon_projection, Polynomial.eval_X, map_zero] at h
  exact h.symm

end JetBase

end
