import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialConstants
import Mathlib.RingTheory.PolynomialAlgebra

/-! # The scheme-theoretic fibre over an affine chart is `Spec` of a tensor product

Glue for the coordinate ring of a fibre of a total space; everything here is stated for an arbitrary
morphism of schemes `f : X ⟶ Y`.

Setting: `f : X ⟶ Y`, `y ∈ Y`, `V ∋ y` an affine open with `f ⁻¹ᵁ V` affine (e.g. `f` an affine morphism),
`R := Γ(Y, V)`, `A := Γ(X, f ⁻¹ᵁ V)` (an `R`-algebra via `f.app V`), `κ := κ(y)` (an `R`-algebra via
evaluation at `y`), `F := f.fiber y = X ×_Y Spec κ`, `i := f.fiberι y`, `π := f.fiberToSpecResidueField y`.

* `Scheme.Hom.top_le_fiberι_preimage`: `i` lands in `f ⁻¹ᵁ V`, so functions on `f ⁻¹ᵁ V` restrict to `F`
  (`i.appLE (f ⁻¹ᵁ V) ⊤ _ : A → Γ(F, O)`).
* `Scheme.fromSpecResidueField_eq_specMap_evaluation`: `Spec κ → Y` factors as `Spec κ → Spec R → Y`,
  `Spec` of the evaluation map followed by `hV.fromSpec` (Mathlib `fromSpecStalk`, `germ_residue`).
* `Scheme.Hom.isPullback_fromSpec_specMap_app`: `Spec A → X` is the base change of `Spec R → Y` along `f`
  (both are open immersions with the right ranges: Mathlib `IsOpenImmersion.isPullback`,
  `IsAffineOpen.SpecMap_appLE_fromSpec`, `range_fromSpec`).
* `Scheme.Hom.fiber_exists_tensorProduct_ringEquiv`: **`Γ(F, O) ≅ A ⊗_R κ`**, sending `a ⊗ 1` to the
  restriction of `a` and `1 ⊗ c` to the constant `c` (`fiberResidueConstants`). Proof: paste the pullback
  square `Spec (A ⊗_R κ) = Spec A ×_{Spec R} Spec κ` (Mathlib `isPullback_SpecMap_of_isPushout`,
  `CommRingCat.isPushout_tensorProduct`) with the previous square; the pasted square identifies `F` with
  `Spec (A ⊗_R κ)` (`IsPullback.isoPullback`) compatibly with `i` and `π`; take global sections
  (`ΓSpecIso`, `ΓSpecIso_inv_naturality`, `IsAffineOpen.fromSpec_app_self`).
* `Scheme.Hom.range_fiberι_subset_range_ι`, `Scheme.Hom.appTop_ι_appLE_eq_appLE`: the fiber inclusion lifts
  through the open subscheme `f ⁻¹ᵁ V` (`IsOpenImmersion.lift`), and restricting a function through that lift
  is restricting it along the fiber inclusion.
* `Scheme.Hom.fiber_exists_polynomial_ringEquiv`: if moreover `A = R[x]` is a polynomial ring on `x ∈ A`
  (`Polynomial.aeval x` bijective), then **`Γ(F, O) ≅ κ[t]`** with `C c ↦ const c` and `t ↦ x|_F`
  (polynomial rings commute with base change: Mathlib `Polynomial.polyEquivTensor`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X Y : AlgebraicGeometry.Scheme.{u}}

/-- The fiber inclusion `f.fiberι y : f.fiber y ⟶ X` lands in `f ⁻¹ᵁ V` for every open `V ∋ y`
(`Scheme.Hom.range_fiberι`). -/
theorem Hom.top_le_fiberι_preimage (f : X ⟶ Y) (y : Y) {V : Y.Opens} (hy : y ∈ V) :
    (⊤ : (f.fiber y).Opens) ≤ f.fiberι y ⁻¹ᵁ (f ⁻¹ᵁ V) := by
  intro x _
  have hx : f.fiberι y x ∈ f ⁻¹' {y} := (f.range_fiberι y) ▸ Set.mem_range_self x
  show f (f.fiberι y x) ∈ V
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
  rw [hx]
  exact hy

/-- `Spec κ(y) → Y` through an affine open neighbourhood `V ∋ y`: it is `Spec` of the evaluation map
`Γ(Y, V) → κ(y)` followed by `hV.fromSpec : Spec Γ(Y, V) → Y`
(Mathlib: `fromSpecResidueField = Spec.map residue ≫ fromSpecStalk`,
`IsAffineOpen.fromSpecStalk = Spec.map germ ≫ fromSpec`, `germ ≫ residue = evaluation`). -/
theorem fromSpecResidueField_eq_specMap_evaluation (y : Y) {V : Y.Opens} (hV : IsAffineOpen V)
    (hy : y ∈ V) :
    Y.fromSpecResidueField y = AlgebraicGeometry.Spec.map (Y.evaluation V y hy) ≫ hV.fromSpec := by
  rw [AlgebraicGeometry.Scheme.fromSpecResidueField, ← hV.fromSpecStalk_eq_fromSpecStalk hy,
    IsAffineOpen.fromSpecStalk, ← Category.assoc, ← AlgebraicGeometry.Spec.map_comp]
  rfl

/-- `Spec Γ(X, f ⁻¹ᵁ V) → X` is the base change of `Spec Γ(Y, V) → Y` along `f` (for `V`, `f ⁻¹ᵁ V`
affine): both are open immersions, the square commutes (`IsAffineOpen.SpecMap_appLE_fromSpec`) and the
ranges match (`IsAffineOpen.range_fromSpec`), so Mathlib's `IsOpenImmersion.isPullback` applies. -/
theorem Hom.isPullback_fromSpec_specMap_app (f : X ⟶ Y) {V : Y.Opens} (hV : IsAffineOpen V)
    (hA : IsAffineOpen (f ⁻¹ᵁ V)) :
    IsPullback hA.fromSpec (AlgebraicGeometry.Spec.map (f.app V)) f hV.fromSpec := by
  refine (AlgebraicGeometry.IsOpenImmersion.isPullback (AlgebraicGeometry.Spec.map (f.app V))
    hA.fromSpec hV.fromSpec f ?_ ?_).flip
  · rw [← AlgebraicGeometry.Scheme.Hom.appLE_eq_app]
    exact (hV.SpecMap_appLE_fromSpec f hA le_rfl).symm
  · rw [hV.opensRange_fromSpec, hA.opensRange_fromSpec]

/-- `appLE` between the top opens is `appTop` (private copy of `RelativeProjEvaluationScalar.appLE_top_top`). -/
private theorem Hom.appLE_top_top (w : X ⟶ Y) (e : (⊤ : X.Opens) ≤ w ⁻¹ᵁ ⊤) :
    w.appLE ⊤ ⊤ e = w.appTop := by
  have h2 : X.presheaf.map (homOfLE e).op = 𝟙 Γ(X, ⊤) := X.presheaf.map_id (op ⊤)
  show w.app ⊤ ≫ X.presheaf.map (homOfLE e).op = w.app ⊤
  exact (congrArg (fun g => w.app ⊤ ≫ g) h2).trans (Category.comp_id _)

/-- `appLE` depends on the morphism only up to equality of morphisms (the inequality proof is a Prop). -/
private theorem Hom.appLE_congr_hom {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
    (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h
  rfl

/-- The fiber inclusion lands in the open subscheme `f ⁻¹ᵁ V` (set-theoretic form, for `IsOpenImmersion.lift`). -/
theorem Hom.range_fiberι_subset_range_ι (f : X ⟶ Y) (y : Y) {V : Y.Opens} (hy : y ∈ V) :
    Set.range (f.fiberι y) ⊆ Set.range (f ⁻¹ᵁ V).ι := by
  rw [f.range_fiberι y, AlgebraicGeometry.Scheme.Opens.range_ι]
  intro x hx
  show f x ∈ V
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
  rw [hx]
  exact hy

/-- **Restriction through a lift into an open subscheme.** If `j : W ⟶ U` lifts `i : W ⟶ X` through
`U.ι` (`j ≫ U.ι = i`), then restricting a function `a ∈ Γ(X, U)` first to the open subscheme `U`
(`U.ι.appLE U ⊤`) and then along `j` is its restriction along `i` (`appLE_comp_appLE`). -/
theorem Hom.appTop_ι_appLE_eq_appLE {W : AlgebraicGeometry.Scheme.{u}} {U : X.Opens}
    (j : W ⟶ U.toScheme) (i : W ⟶ X) (hj : j ≫ U.ι = i) (e₁ : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U)
    (e : (⊤ : W.Opens) ≤ i ⁻¹ᵁ U) (a : Γ(X, U)) :
    j.appTop.hom ((U.ι.appLE U ⊤ e₁).hom a) = (i.appLE U ⊤ e).hom a := by
  have e₂ : (⊤ : W.Opens) ≤ j ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have h := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE j U.ι U ⊤ ⊤ e₁ e₂
  rw [AlgebraicGeometry.Scheme.Hom.appLE_top_top, AlgebraicGeometry.Scheme.Hom.appLE_congr_hom hj U ⊤ _ e]
    at h
  have h' := congrArg (fun g => g.hom a) h
  simpa only [CommRingCat.comp_apply] using h'

/-- Global functions of `Spec Γ(X, U)`, restricted along `w ≫ hU.fromSpec` from `U`: the composite
`Γ(X, U) → Γ(W, ⊤)` is `ΓSpecIso⁻¹` followed by `w^♯` (`IsAffineOpen.fromSpec_app_self`). -/
theorem Hom.comp_fromSpec_appLE_top {W : AlgebraicGeometry.Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (w : W ⟶ AlgebraicGeometry.Spec Γ(X, U))
    (e : (⊤ : W.Opens) ≤ (w ≫ hU.fromSpec) ⁻¹ᵁ U) :
    (w ≫ hU.fromSpec).appLE U ⊤ e = (AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, U)).inv ≫ w.appTop := by
  have e₂ : (⊤ : W.Opens) ≤ w ⁻¹ᵁ (hU.fromSpec ⁻¹ᵁ U) := e
  calc (w ≫ hU.fromSpec).appLE U ⊤ e
      = hU.fromSpec.app U ≫ w.appLE (hU.fromSpec ⁻¹ᵁ U) ⊤ e₂ :=
        AlgebraicGeometry.Scheme.Hom.comp_appLE _ _ _ _ _
    _ = ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, U)).inv ≫
          (AlgebraicGeometry.Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op) ≫
            w.appLE (hU.fromSpec ⁻¹ᵁ U) ⊤ e₂ := by
        rw [hU.fromSpec_app_self]
    _ = (AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, U)).inv ≫
          ((AlgebraicGeometry.Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op ≫
            w.appLE (hU.fromSpec ⁻¹ᵁ U) ⊤ e₂) := Category.assoc _ _ _
    _ = (AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, U)).inv ≫ w.appLE ⊤ ⊤ _ := by
        rw [AlgebraicGeometry.Scheme.Hom.map_appLE]
    _ = (AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, U)).inv ≫ w.appTop := by
        rw [AlgebraicGeometry.Scheme.Hom.appLE_top_top]

/-- **The scheme-theoretic fiber over an affine chart is `Spec` of a tensor product**
(Stacks 01JT / Hartshorne II Ex. 3.10).

For `f : X ⟶ Y`, `y ∈ V` affine with `f ⁻¹ᵁ V` affine, `R := Γ(Y, V)`, `A := Γ(X, f ⁻¹ᵁ V)`,
`κ := κ(y)`: there is a ring isomorphism `A ⊗_R κ ≃ Γ(f.fiber y, O)` sending `a ⊗ 1` to the restriction of
`a` along `f.fiberι y` and `1 ⊗ c` to the constant `c` (`fiberResidueConstants`).

Proof: `Spec (A ⊗_R κ) = Spec A ×_{Spec R} Spec κ` (`isPullback_SpecMap_of_isPushout`,
`CommRingCat.isPushout_tensorProduct`); `Spec A = X ×_Y Spec R` (`isPullback_fromSpec_specMap_app`);
pasting (`IsPullback.paste_horiz`) and `Spec κ → Y = Spec κ → Spec R → Y`
(`fromSpecResidueField_eq_specMap_evaluation`) give `Spec (A ⊗_R κ) = X ×_Y Spec κ = f.fiber y`
(`IsPullback.isoPullback`), with `fiberι ↔ Spec (a ↦ a ⊗ 1) ≫ fromSpec` and
`fiberToSpecResidueField ↔ Spec (c ↦ 1 ⊗ c)`. Global sections (`ΓSpecIso`) give the ring isomorphism; the two
formulas are `ΓSpecIso_inv_naturality` and `comp_fromSpec_appLE_top`. -/
theorem Hom.fiber_exists_tensorProduct_ringEquiv (f : X ⟶ Y) (y : Y) {V : Y.Opens}
    (hV : IsAffineOpen V) (hy : y ∈ V) (hA : IsAffineOpen (f ⁻¹ᵁ V)) :
    letI : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
    letI : Algebra Γ(Y, V) (Y.residueField y : Type u) := (Y.evaluation V y hy).hom.toAlgebra
    ∃ e : Γ(X, f ⁻¹ᵁ V) ⊗[Γ(Y, V)] (Y.residueField y : Type u) ≃+* Γ(f.fiber y, ⊤),
      (∀ a : Γ(X, f ⁻¹ᵁ V), e (a ⊗ₜ 1) =
        (f.fiberι y).appLE (f ⁻¹ᵁ V) ⊤ (f.top_le_fiberι_preimage y hy) a) ∧
      (∀ c : (Y.residueField y : Type u), e (1 ⊗ₜ c) = f.fiberResidueConstants y c) := by
  let _ : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  let _ : Algebra Γ(Y, V) (Y.residueField y : Type u) := (Y.evaluation V y hy).hom.toAlgebra
  -- the left square `Spec (A ⊗ κ) = Spec A ×_{Spec R} Spec κ`
  have hL := AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(Y, V) Γ(X, f ⁻¹ᵁ V) (Y.residueField y : Type u))
  have h1 : CommRingCat.ofHom (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) = f.app V := rfl
  have h2 : CommRingCat.ofHom (algebraMap Γ(Y, V) (Y.residueField y : Type u)) =
    Y.evaluation V y hy := rfl
  rw [h1, h2] at hL
  -- paste with the right square `Spec A = X ×_Y Spec R`
  have hP := hL.paste_horiz (f.isPullback_fromSpec_specMap_app hV hA)
  rw [← AlgebraicGeometry.Scheme.fromSpecResidueField_eq_specMap_evaluation y hV hy] at hP
  let θ : AlgebraicGeometry.Spec (CommRingCat.of
      (Γ(X, f ⁻¹ᵁ V) ⊗[Γ(Y, V)] (Y.residueField y : Type u))) ≅ f.fiber y := hP.isoPullback
  have hθ1 := hP.isoPullback_hom_fst
  have hθ2 := hP.isoPullback_hom_snd
  -- the ring isomorphism on global sections
  let ψ : CommRingCat.of (Γ(X, f ⁻¹ᵁ V) ⊗[Γ(Y, V)] (Y.residueField y : Type u)) ≅ Γ(f.fiber y, ⊤) :=
    (AlgebraicGeometry.Scheme.ΓSpecIso _).symm ≪≫
      { hom := θ.inv.appTop
        inv := θ.hom.appTop
        hom_inv_id := by
          rw [← AlgebraicGeometry.Scheme.Hom.comp_appTop, Iso.hom_inv_id,
            AlgebraicGeometry.Scheme.Hom.id_appTop]
        inv_hom_id := by
          rw [← AlgebraicGeometry.Scheme.Hom.comp_appTop, Iso.inv_hom_id,
            AlgebraicGeometry.Scheme.Hom.id_appTop] }
  refine ⟨ψ.commRingCatIsoToRingEquiv, fun a => ?_, fun c => ?_⟩
  · -- `a ⊗ 1 ↦ a|_F`
    have hi : f.fiberι y = (θ.inv ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)) ≫
          hA.fromSpec :=
      ((Iso.inv_hom_id_assoc θ (f.fiberι y)).symm.trans (congrArg (fun g => θ.inv ≫ g) hθ1)).trans
        (Category.assoc _ _ _).symm
    have e' : (⊤ : (f.fiber y).Opens) ≤ ((θ.inv ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)) ≫
          hA.fromSpec) ⁻¹ᵁ (f ⁻¹ᵁ V) := hi ▸ f.top_le_fiberι_preimage y hy
    have key : (f.fiberι y).appLE (f ⁻¹ᵁ V) ⊤ (f.top_le_fiberι_preimage y hy) =
        (AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, f ⁻¹ᵁ V)).inv ≫
          (θ.inv ≫ AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)).appTop :=
      (AlgebraicGeometry.Scheme.Hom.appLE_congr_hom hi _ _ _ e').trans
        (AlgebraicGeometry.Scheme.Hom.comp_fromSpec_appLE_top hA _ e')
    rw [key, AlgebraicGeometry.Scheme.Hom.comp_appTop, ← Category.assoc,
      ← AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality]
    rfl
  · -- `1 ⊗ c ↦ const c`
    have hπ := (Iso.inv_hom_id_assoc θ (f.fiberToSpecResidueField y)).symm.trans
      (congrArg (fun g => θ.inv ≫ g) hθ2)
    change _ = ((AlgebraicGeometry.Scheme.ΓSpecIso (Y.residueField y)).inv ≫
      (f.fiberToSpecResidueField y).appTop).hom c
    rw [hπ, AlgebraicGeometry.Scheme.Hom.comp_appTop, ← Category.assoc,
      ← AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality]
    rfl

/-- **The fiber over an affine chart on which `X` is the affine line: `Γ(F, O) = κ(y)[t]`.**
If `A := Γ(X, f ⁻¹ᵁ V)` is the polynomial ring over `R := Γ(Y, V)` on `x ∈ A` (`Polynomial.aeval x`
bijective), then `Γ(f.fiber y, O) ≅ κ(y)[t]` with `C c ↦ const c` and `t ↦ x|_F`.
Proof: `κ[t] ≅ κ ⊗_R R[t]` (Mathlib `Polynomial.polyEquivTensor`), `R[t] ≅ A` (`aeval x`), `κ ⊗_R A ≅ A ⊗_R κ`
(`Algebra.TensorProduct.comm`), `A ⊗_R κ ≅ Γ(F, O)` (`fiber_exists_tensorProduct_ringEquiv`). -/
theorem Hom.fiber_exists_polynomial_ringEquiv (f : X ⟶ Y) (y : Y) {V : Y.Opens}
    (hV : IsAffineOpen V) (hy : y ∈ V) (hA : IsAffineOpen (f ⁻¹ᵁ V)) (x : Γ(X, f ⁻¹ᵁ V))
    (hx : letI : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
      Function.Bijective (Polynomial.aeval x : Polynomial Γ(Y, V) →ₐ[Γ(Y, V)] Γ(X, f ⁻¹ᵁ V))) :
    ∃ φ : Polynomial (Y.residueField y : Type u) ≃+* Γ(f.fiber y, ⊤),
      (∀ c : (Y.residueField y : Type u), φ (Polynomial.C c) = f.fiberResidueConstants y c) ∧
      φ Polynomial.X = (f.fiberι y).appLE (f ⁻¹ᵁ V) ⊤ (f.top_le_fiberι_preimage y hy) x := by
  let _ : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  let _ : Algebra Γ(Y, V) (Y.residueField y : Type u) := (Y.evaluation V y hy).hom.toAlgebra
  obtain ⟨e, he1, he2⟩ := f.fiber_exists_tensorProduct_ringEquiv y hV hy hA
  let e₁ := polyEquivTensor Γ(Y, V) (Y.residueField y : Type u)
  let e₂ := Algebra.TensorProduct.congr (AlgEquiv.refl : (Y.residueField y : Type u) ≃ₐ[Γ(Y, V)] (Y.residueField y : Type u))
    (AlgEquiv.ofBijective (Polynomial.aeval x) hx)
  let e₃ := Algebra.TensorProduct.comm Γ(Y, V) (Y.residueField y : Type u) Γ(X, f ⁻¹ᵁ V)
  refine ⟨((e₁.trans e₂).trans e₃).toRingEquiv.trans e, fun c => ?_, ?_⟩
  · have h1 : e₁ (Polynomial.C c) = c ⊗ₜ 1 := by
      rw [polyEquivTensor_apply, Polynomial.eval₂_C]
      rfl
    have h2 : e₂ (c ⊗ₜ 1) = c ⊗ₜ 1 := by
      rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
      rfl
    rw [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply, h1,
      h2, Algebra.TensorProduct.comm_tmul, he2]
  · have h1 : e₁ Polynomial.X = 1 ⊗ₜ Polynomial.X := by
      rw [polyEquivTensor_apply, Polynomial.eval₂_X]
    have h2 : e₂ (1 ⊗ₜ Polynomial.X) = 1 ⊗ₜ x := by
      rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
      simp only [AlgEquiv.coe_toAlgHom, AlgEquiv.ofBijective_apply, Polynomial.aeval_X]
    rw [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply, h1,
      h2, Algebra.TensorProduct.comm_tmul, he1]

end AlgebraicGeometry.Scheme

end
