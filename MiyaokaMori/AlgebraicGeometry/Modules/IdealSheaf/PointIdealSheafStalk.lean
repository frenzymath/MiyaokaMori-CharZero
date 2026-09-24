import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.PointIdealSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdealEqMapGerm
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdealBasic

/-! # The stalk of a point ideal sheaf

The stalk ideal of `pointIdealSheaf x q` at `x` is `q` (when `q` is `𝔪_x`-primary).

References: input to Stacks 0AHH; Atiyah–Macdonald Prop 3.11(i) (contraction followed by
extension of an ideal in a localization).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- If `𝔪_xⁿ ≤ q` then `(pointIdealSheaf x q)_x = q`.

Proof sketch: let `g := Spec.map (mk q) ≫ X.fromSpecStalk x : Spec(O_{X,x}/q) → X`.
(1) Since `𝔪ⁿ ≤ q`, every point of `Spec(O_{X,x}/q)` maps to the closed point `𝔪`, so the source
    has at most one point (empty if `q = ⊤`), `g` is quasi-compact, and `g⁻¹U = ⊤` for every affine
    open `U ∋ x` (`Scheme.fromSpecStalk_closedPoint`).
(2) `stalkIdeal_eq_map_germ` gives `(g.ker)_x = (g.ker)(U)·O_{X,x}`, and `Scheme.Hom.ker_apply`
    gives `(g.ker)(U) = ker(g.app U)`.
(3) The restriction `Γ(g⁻¹U) → Γ(⊤)` is an isomorphism, so `ker(g.app U) = ker(g.appLE U ⊤)`, and
    `g.appLE U ⊤ = germ_x ≫ mk q ≫ (ΓSpecIso _).inv`; hence the kernel is `q.comap germ_x`.
(4) `germ_x : Γ(U) → O_{X,x}` is the localization at a prime (`IsAffineOpen.isLocalization_stalk`),
    and in a localization `(q.comap).map = q` (`IsLocalization.map_under`).
The case `q = ⊤` needs no separate treatment: then `O/q = 0` and `Spec` is empty. -/
theorem AlgebraicGeometry.Scheme.pointIdealSheaf_stalkIdeal
    (X : AlgebraicGeometry.Scheme.{u}) (x : X)
    (q : Ideal (X.presheaf.stalk x)) (n : ℕ)
    (hq : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n ≤ q) :
    (X.pointIdealSheaf x q).stalkIdeal x = q := by
  set φ : CommRingCat.of (X.presheaf.stalk x) ⟶ CommRingCat.of (X.presheaf.stalk x ⧸ q) :=
    CommRingCat.ofHom (Ideal.Quotient.mk q) with hφ
  -- (1) every point of `Spec (O_{X,x} ⧸ q)` maps to the closed point of `Spec O_{X,x}`
  have hpt : ∀ P : AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.stalk x ⧸ q)),
      AlgebraicGeometry.Spec.map φ P = IsLocalRing.closedPoint (X.presheaf.stalk x) := by
    intro P
    rw [AlgebraicGeometry.Spec.map_apply]
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (Ideal.Quotient.mk q) P.asIdeal = IsLocalRing.maximalIdeal _
    have : P.asIdeal.IsPrime := P.isPrime
    have : (Ideal.comap (Ideal.Quotient.mk q) P.asIdeal).IsPrime := Ideal.comap_isPrime _ _
    apply le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime _)
    apply Ideal.IsPrime.le_of_pow_le (n := n)
    calc IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n ≤ q := hq
      _ = RingHom.ker (Ideal.Quotient.mk q) := Ideal.mk_ker.symm
      _ ≤ Ideal.comap (Ideal.Quotient.mk q) P.asIdeal := Ideal.ker_le_comap _
  -- the source has at most one point, hence the composite is quasi-compact
  have hsub : Subsingleton (AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.stalk x ⧸ q))) := by
    refine ⟨fun P Q ↦ ?_⟩
    have h : AlgebraicGeometry.Spec.map φ P = AlgebraicGeometry.Spec.map φ Q := by
      rw [hpt P, hpt Q]
    rw [AlgebraicGeometry.Spec.map_apply, AlgebraicGeometry.Spec.map_apply] at h
    exact PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective h
  have hqc : AlgebraicGeometry.QuasiCompact (AlgebraicGeometry.Spec.map φ ≫ X.fromSpecStalk x) :=
    ⟨fun U _ _ ↦ (Set.subsingleton_of_subsingleton).isCompact⟩
  -- (2) an affine open `U ∋ x`; the composite lands in `U`
  obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
  have e : (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.stalk x ⧸ q))).Opens) ≤
      (AlgebraicGeometry.Spec.map φ ≫ X.fromSpecStalk x) ⁻¹ᵁ U.1 := by
    intro P _
    show (AlgebraicGeometry.Spec.map φ ≫ X.fromSpecStalk x) P ∈ U.1
    rw [AlgebraicGeometry.Scheme.Hom.comp_apply, hpt P,
      AlgebraicGeometry.Scheme.fromSpecStalk_closedPoint]
    exact hxU
  -- (3) reduce to the kernel of `g.app U`
  rw [(X.pointIdealSheaf x q).stalkIdeal_eq_map_germ x U hxU]
  unfold AlgebraicGeometry.Scheme.pointIdealSheaf
  rw [AlgebraicGeometry.Scheme.Hom.ker_apply]
  -- (4) ker (g.app U) = ker (g.appLE U.1 ⊤ e): the restriction Γ(g⁻¹U) → Γ(⊤) is an iso
  have hres : Function.Injective
      (((AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.stalk x ⧸ q))).presheaf.map
        (homOfLE e).op).hom) := by
    have hcomp : (AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.stalk x ⧸ q))).presheaf.map
        (homOfLE e).op ≫
        (AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.stalk x ⧸ q))).presheaf.map
        (homOfLE le_top).op = 𝟙 _ := by
      rw [← Functor.map_comp, ← op_comp]
      have : homOfLE (le_top : (AlgebraicGeometry.Spec.map φ ≫ X.fromSpecStalk x) ⁻¹ᵁ U.1 ≤ ⊤) ≫
          homOfLE e = 𝟙 _ := Subsingleton.elim _ _
      rw [this, op_id]
      exact CategoryTheory.Functor.map_id _ _
    intro a b hab
    have := congrArg (fun f => (CommRingCat.Hom.hom f) a) hcomp
    have := congrArg (fun f => (CommRingCat.Hom.hom f) b) hcomp
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at *
    rw [← ‹_ = a›, ← ‹_ = b›, hab]
  have hkerLE : RingHom.ker ((AlgebraicGeometry.Spec.map φ ≫ X.fromSpecStalk x).appLE U.1 ⊤ e).hom =
      RingHom.ker ((AlgebraicGeometry.Spec.map φ ≫ X.fromSpecStalk x).app U.1).hom := by
    rw [AlgebraicGeometry.Scheme.Hom.appLE, CommRingCat.hom_comp,
      RingHom.ker_comp_of_injective _ hres]
  rw [← hkerLE]
  -- (5) compute `g.appLE U ⊤ e = germ ≫ mk ≫ (ΓSpecIso _).inv`
  have e' : (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.stalk x ⧸ q))).Opens) ≤
      AlgebraicGeometry.Spec.map φ ⁻¹ᵁ (X.fromSpecStalk x ⁻¹ᵁ U.1) := e
  have happ : (AlgebraicGeometry.Spec.map φ ≫ X.fromSpecStalk x).appLE U.1 ⊤ e =
      X.presheaf.germ U.1 x hxU ≫ φ ≫ (AlgebraicGeometry.Scheme.ΓSpecIso _).inv := by
    have h1 := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE (AlgebraicGeometry.Spec.map φ)
      (X.fromSpecStalk x) U.1 _ ⊤ le_rfl e'
    rw [AlgebraicGeometry.Scheme.Hom.appLE_eq_app, AlgebraicGeometry.Scheme.fromSpecStalk_app hxU]
      at h1
    simp only [Category.assoc] at h1
    rw [AlgebraicGeometry.Scheme.Hom.map_appLE] at h1
    rw [← h1, AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality]
    congr 2
  rw [happ, CommRingCat.hom_comp, CommRingCat.hom_comp, ← RingHom.comap_ker,
    RingHom.ker_comp_of_injective _
      (ConcreteCategory.bijective_of_isIso (AlgebraicGeometry.Scheme.ΓSpecIso _).inv).1,
    hφ, CommRingCat.hom_ofHom, Ideal.mk_ker]
  -- (6) contraction then extension along a localization is the identity
  let _ : Algebra Γ(X, U.1) (X.presheaf.stalk x) := (X.presheaf.germ U.1 x hxU).hom.toAlgebra
  have := U.2.isLocalization_stalk ⟨x, hxU⟩
  exact IsLocalization.map_under (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) q

end
