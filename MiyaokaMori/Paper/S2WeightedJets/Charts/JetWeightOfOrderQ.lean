import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetLocalGradedRingEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecSections
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetScheme

/-! # The jet coordinates of order `q` have weight `q`

Compatibility of the local coordinates with the rescaling of the jet parameter: on an affine open
`U` on which `E = s^*T_{Z/C}` is trivial, the isomorphism `J_k^s|_U ≅ 𝔸_U^{(n+1)k}` of
`jet_local_coordinates` can be chosen `𝔾_m`-equivariantly, so that the coordinate `x_{i,q}` of order
`q` lies in `S_q(U)`, i.e. has weight `q` (§2.2 of the paper: "rescaling the jet parameter assigns
weight `q` to the coefficient of order `q`").

The geometric content is `jetLocalGradedRingEquiv`. The isomorphism `φ` is built directly from the
graded ring isomorphism: given
`e : 𝒮(U) = J_r(B_U, ε_U) ≃+* Γ(U)[x_{i,q}]` (grading: `a ∈ 𝒮_m(U) ↔ e a` is weighted homogeneous
of weight `m` for `x_{i,q} ↦ q+1`; structure map: `e (unit a) = C a`), put
`φ := preimageIsoSpec ≪≫ Spec.mapIso e.symm ≪≫ (AffineSpace.isoOfIsAffine).symm`.
(1) `φ` lies over `U`: `isoOfIsAffine_inv_over` writes `𝔸_U ↘ U` as `Spec(C) ≫ isoSpec.inv`,
`e.symm ∘ C = unit ∘ topIso` (from `e (unit a) = C a`) gives
`Spec.map e.symm ≫ Spec.map C = Spec.map unit`, and `chart_hom` / `resLE_comp_ι` give
`preimageIsoSpec.hom ≫ chartToOpen = relativeSpec.hom ∣_ U`.
(2) Weights of the coordinates:
`φ.hom.appTop (coord (i,q)) = preimageIsoSpec.hom.appTop (ΓSpecIso.inv (e.symm X_{i,q}))`
(`isoOfIsAffine_inv_appTop_coord` + `ΓSpecIso_inv_naturality`), and `sectionsPreimageEquiv`
sends it by definition back to `e.symm X_{i,q}`; hence `e (…) = X_{i,q}`, which is weighted
homogeneous of weight `q+1` (`isWeightedHomogeneous_X`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Local coordinates on the based jet scheme compatible with the weights: over an affine open `U`
trivializing `E`, `J_k^s|_U ≅ 𝔸_U^{(n+1)k}` over `U`, with the coordinate of order `q` lying in the
graded piece of weight `q + 1` (indices starting at `0`). -/
theorem jetCoordinate_weight {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    [C.toScheme.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C.toScheme ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C.toScheme)
    [AlgebraicGeometry.IsClosedImmersion s]
    (Zx : Z.left.Opens) (hsZx : ∀ c, s.base c ∈ Zx) (n : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom)] (r : ℕ)
    (U : C.toScheme.affineOpens)
    /- An affine open `U` on which `E = s^*T_{Z/C}` is trivial (the hypothesis of
       `jet_local_coordinates`). -/
    (htriv : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.1.ι).obj (coneTangentBundle Z.hom s hs) ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) (ULift.{u} (Fin (n + 1))))) :
    ∃ φ : ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1).toScheme ≅
        AlgebraicGeometry.AffineSpace (ULift.{u} (Fin (n + 1) × Fin r)) U.1.toScheme,
      /- `φ` is an isomorphism of `U`-schemes (compatible with the projections to `U`), as in the
         conclusion of `jet_local_coordinates`. -/
      φ.hom ≫ (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin (n + 1) × Fin r)) U.1.toScheme ↘ U.1.toScheme) =
          (relativeJetScheme (k := k) Z s hs r).hom ∣_ U.1 ∧
      ∀ (i : Fin (n + 1)) (q : Fin r),
        (jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.sectionsPreimageEquiv
            (AlgebraicGeometry.Scheme.affineSite U)
            (φ.hom.appTop (AlgebraicGeometry.AffineSpace.coord U.1.toScheme ⟨(i, q)⟩)) ∈
          (jetGradedAffineAlgebra Z s hs r).grading
            (AlgebraicGeometry.Scheme.affineSite U) ((q : ℕ) + 1) := by
  obtain ⟨e, hegrade, heunit⟩ := jetLocalGradedRingEquiv Z s hs Zx hsZx n r U htriv
  let A := (jetGradedAffineAlgebra Z s hs r).toAffineAlgebra
  let V := AlgebraicGeometry.Scheme.affineSite U
  have hbase :
      CommRingCat.ofHom (MvPolynomial.C : Γ(U.1.toScheme, ⊤) →+*
          MvPolynomial (ULift.{u} (Fin (n + 1) × Fin r)) Γ(U.1.toScheme, ⊤)) ≫
        CommRingCat.ofHom e.symm.toRingHom =
      U.1.topIso.hom ≫ A.unit.app (op V) := by
    ext a
    change e.symm (MvPolynomial.C a) =
      A.unitHom V (U.1.topIso.hom.hom a)
    apply e.injective
    rw [RingEquiv.apply_symm_apply, heunit]
  have hpoly :
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫
            U.1.toScheme.isoSpec.inv =
        AlgebraicGeometry.Spec.map (A.unit.app (op V)) ≫ U.2.isoSpec.inv := by
    dsimp only [V] at hbase ⊢
    let fC := CommRingCat.ofHom
      (MvPolynomial.C : Γ(U.1.toScheme, ⊤) →+*
        MvPolynomial (ULift.{u} (Fin (n + 1) × Fin r)) Γ(U.1.toScheme, ⊤))
    let fe := CommRingCat.ofHom e.symm.toRingHom
    let fu := A.unit.app (op (AlgebraicGeometry.Scheme.affineSite U))
    have hleft := AlgebraicGeometry.Spec.map_comp fC fe
    have hright := AlgebraicGeometry.Spec.map_comp U.1.topIso.hom fu
    calc
      AlgebraicGeometry.Spec.map fe ≫ AlgebraicGeometry.Spec.map fC ≫
            U.1.toScheme.isoSpec.inv =
          (AlgebraicGeometry.Spec.map fe ≫ AlgebraicGeometry.Spec.map fC) ≫
            U.1.toScheme.isoSpec.inv := (Category.assoc _ _ _).symm
      _ = AlgebraicGeometry.Spec.map (fC ≫ fe) ≫ U.1.toScheme.isoSpec.inv :=
        congrArg (fun g ↦ g ≫ U.1.toScheme.isoSpec.inv) hleft.symm
      _ = AlgebraicGeometry.Spec.map (U.1.topIso.hom ≫ fu) ≫
            U.1.toScheme.isoSpec.inv := by rw [hbase]
      _ = (AlgebraicGeometry.Spec.map fu ≫
            AlgebraicGeometry.Spec.map U.1.topIso.hom) ≫
            U.1.toScheme.isoSpec.inv :=
        congrArg (fun g ↦ g ≫ U.1.toScheme.isoSpec.inv) hright
      _ = AlgebraicGeometry.Spec.map fu ≫
            (AlgebraicGeometry.Spec.map U.1.topIso.hom ≫
              U.1.toScheme.isoSpec.inv) := Category.assoc _ _ _
      _ = AlgebraicGeometry.Spec.map fu ≫ U.2.isoSpec.inv := by rfl
  have hpre :
      (A.preimageIsoSpec V).hom ≫ A.chartToOpen V =
        A.relativeSpec.hom ∣_ V.toOpens := by
    have hchart :
        (A.preimageIsoSpec V).hom ≫ A.chart V =
          (A.relativeSpec.hom ⁻¹ᵁ V.toOpens).ι := by
      have eqToIso_hom_ι {X : AlgebraicGeometry.Scheme} {W W' : X.Opens}
          (h : W = W') :
          (eqToIso (congrArg AlgebraicGeometry.Scheme.Opens.toScheme h)).hom ≫ W'.ι =
            W.ι := by
        subst W'
        simp
      change ((eqToIso (congrArg AlgebraicGeometry.Scheme.Opens.toScheme
          (A.preimage_eq_opensRange V)) ≪≫ (A.chart V).isoOpensRange.symm).hom ≫
        A.chart V) = _
      rw [Iso.trans_hom, Iso.symm_hom, Category.assoc,
        AlgebraicGeometry.Scheme.Hom.isoOpensRange_inv_comp]
      exact eqToIso_hom_ι (A.preimage_eq_opensRange V)
    apply (cancel_mono V.toOpens.ι).mp
    calc
      ((A.preimageIsoSpec V).hom ≫ A.chartToOpen V) ≫ V.toOpens.ι =
          (A.preimageIsoSpec V).hom ≫ A.chart V ≫ A.relativeSpec.hom := by
        simp only [Category.assoc, A.chart_hom]
      _ = (A.relativeSpec.hom ⁻¹ᵁ V.toOpens).ι ≫ A.relativeSpec.hom := by
        rw [← Category.assoc, hchart]
      _ = (A.relativeSpec.hom ∣_ V.toOpens) ≫ V.toOpens.ι := by
        rw [← AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict]
        exact (AlgebraicGeometry.Scheme.Hom.resLE_comp_ι _ _).symm
  let φ : ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1).toScheme ≅
      AlgebraicGeometry.AffineSpace (ULift.{u} (Fin (n + 1) × Fin r)) U.1.toScheme :=
    A.preimageIsoSpec V ≪≫ AlgebraicGeometry.Scheme.Spec.mapIso e.symm.toCommRingCatIso.op ≪≫
      (AlgebraicGeometry.AffineSpace.isoOfIsAffine
        (ULift.{u} (Fin (n + 1) × Fin r)) U.1.toScheme).symm
  refine ⟨φ, ?_, ?_⟩
  · change ((A.preimageIsoSpec V).hom ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
        (AlgebraicGeometry.AffineSpace.isoOfIsAffine
          (ULift.{u} (Fin (n + 1) × Fin r)) U.1.toScheme).inv) ≫
        (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin (n + 1) × Fin r)) U.1.toScheme ↘
          U.1.toScheme) =
      A.relativeSpec.hom ∣_ V.toOpens
    rw [Category.assoc, Category.assoc, AlgebraicGeometry.AffineSpace.isoOfIsAffine_inv_over,
      ← hpre]
    exact congrArg (fun g ↦ (A.preimageIsoSpec V).hom ≫ g) hpoly
  · intro i q
    apply (hegrade ((q : ℕ) + 1) _).mpr
    let j : ULift.{u} (Fin (n + 1) × Fin r) := ⟨(i, q)⟩
    let P := A.preimageIsoSpec V
    let fe : CommRingCat.of (MvPolynomial (ULift.{u} (Fin (n + 1) × Fin r)) Γ(U.1.toScheme, ⊤)) ⟶
        A.sections V := CommRingCat.ofHom e.symm.toRingHom
    let ι := AlgebraicGeometry.AffineSpace.isoOfIsAffine
      (ULift.{u} (Fin (n + 1) × Fin r)) U.1.toScheme
    change MvPolynomial.IsWeightedHomogeneous _
      (e (A.sectionsPreimageEquiv V
        ((P.hom ≫ AlgebraicGeometry.Spec.map fe ≫ ι.inv).appTop
          (AlgebraicGeometry.AffineSpace.coord U.1.toScheme j)))) _
    have hcoord : e (A.sectionsPreimageEquiv V
        ((P.hom ≫ AlgebraicGeometry.Spec.map fe ≫ ι.inv).appTop
          (AlgebraicGeometry.AffineSpace.coord U.1.toScheme j))) = MvPolynomial.X j := by
      have h1 : (P.hom ≫ AlgebraicGeometry.Spec.map fe ≫ ι.inv).appTop
            (AlgebraicGeometry.AffineSpace.coord U.1.toScheme j) =
          P.hom.appTop ((AlgebraicGeometry.Spec.map fe).appTop
            (ι.inv.appTop (AlgebraicGeometry.AffineSpace.coord U.1.toScheme j))) := rfl
      have h2 : (AlgebraicGeometry.Spec.map fe).appTop
            (ι.inv.appTop (AlgebraicGeometry.AffineSpace.coord U.1.toScheme j)) =
          (AlgebraicGeometry.Scheme.ΓSpecIso (A.sections V)).inv (fe (MvPolynomial.X j)) := by
        rw [AlgebraicGeometry.AffineSpace.isoOfIsAffine_inv_appTop_coord,
          ← CommRingCat.comp_apply, ← AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality,
          CommRingCat.comp_apply]
      rw [h1, h2]
      have hΨ : P.hom.appTop ((AlgebraicGeometry.Scheme.ΓSpecIso (A.sections V)).inv
            (fe (MvPolynomial.X j))) =
          (A.sectionsPreimageEquiv V).symm (e.symm (MvPolynomial.X j)) := rfl
      rw [hΨ, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    rw [hcoord]
    exact MvPolynomial.isWeightedHomogeneous_X Γ(U.1.toScheme, ⊤)
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) ↦ (iq.down.2 : ℕ) + 1) j

end
