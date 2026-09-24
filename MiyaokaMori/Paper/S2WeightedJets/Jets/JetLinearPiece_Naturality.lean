import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetLinearPiece_Derivation
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetRepresentableByUniversalJet
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetRepresentableByCoeff

/-! # The linear piece of the jet algebra: naturality of the local coefficient maps `θ_U`

For affine `V ≤ U`, `Γ(L, V ≤ U) ∘ θ_U = θ_V ∘ Γ(sec^*Ω, V ≤ U)` (used in `DeformedJetAlgebraFiberAtZero_LinearPieceDual`).
Notation as in `JetLinearPiece_Defs` / `JetLinearPiece_Derivation`.

* **Chart readings are natural for arbitrary affine `V ≤ U`.** The chart identification `χ_U : J_r(B_U, ε_U) ≃+* Γ(π⁻¹U, O_J)` is
  only known to be natural along *basic-open* inclusions (`relativeJetScheme.chartSections_comp_map`; the morphisms of
  `C.AffineZariskiSite` are basic-open inclusions). For an arbitrary affine `V ≤ U` we use the **global universal jet**
  `u : J ×_k D_r → Z` (`relativeJetScheme.universalJet`): on `π⁻¹U`, `u^♯ = universalJetSections U`
  (`universalJet_appLE_chartOpen`) and the `t^{q+1}`-coefficient of `u^♯ b` is `chartSections U (d_q b)`
  (`coeff_universalJetSections`). So `χ_U (d_q b) = jetCoordSection U b := coeff_{q+1} (u^♯ b)` (`chartEquiv_coeffClass`), a
  formula in terms of the global morphism `u` and hence natural in the open (`Scheme.Hom.appLE_map`, `map_appLE`,
  `jetThickening.coeff_restrict`): `jetCoordSection_restrict`.
* Consequences: `σ(d_q b)|_V = σ(d_q (b|_V))` (`coeffSection_restrict`, by injectivity of `js_V` and of `χ_V`, and naturality of
  `kernel.ι`), `[d_q b]|_V = [d_q (b|_V)]` (`coeffDerivationFun_restrict`, naturality of `cokernel.π`), and
  `((db)|_sec)|_V = (d(b|_V))|_sec` (`omegaSection_restrict`: `pullbackSectionsOn_restrict` + `d_map`).
* **The `(db)|_sec` span `Γ(U, sec^*Ω_{Z/C})`** (`span_omegaSection_eq_top`): `Φ : A ⊗_B Γ(π⁻¹U, Ω) → Γ(U, sec^*Ω)` is surjective
  (01I9) and `Γ(π⁻¹U, Ω) = Ω[B⁄A]` is spanned over `B` by the `d b` (`KaehlerDifferential.span_range_derivation`, 01UT), while
  `Φ(a ⊗ b' • db) = a • ε(b') • (db)|_sec` (`pullbackSectionsOn_smul_native`).
* **Naturality** (`coeffMap_restrict`): both sides are additive and `A`-semilinear along `Γ(C,U) → Γ(C,V)`, and agree on the
  generators `(db)|_sec` by the three restriction lemmas (`Submodule.span_induction`).

Source: §2 of the paper, eq. (2.7); Stacks 01I9, 01UT, 00RM. Edge cases: `V = ⊥` (zero modules);
`U = V` (identities).

Note that `chartEquiv_eq_chartSections` + `chartSections_comp_map` cover only basic-open inclusions `V ⟶ U` in
`AffineZariskiSite` (Mathlib: `U ≤ V ↔ ∃ f, basicOpen f = U`), while the gluing lemma needs all affine `V ≤ U`; the
universal-jet formula above supplies the missing naturality.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct ChangeOfRings

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- The transpose `S ⊗_R X → Y` of an `R`-linear map `g : X → Y` sends `s ⊗ x` to `s • g x`. -/
theorem ModuleCat.extendRestrictScalarsAdj_homEquiv_symm_apply_tmul {R : Type u} {S : Type u} [CommRing R]
    [CommRing S] (f : R →+* S) {X : ModuleCat.{u} R} {Y : ModuleCat.{u} S}
    (g : X ⟶ (ModuleCat.restrictScalars f).obj Y) (s : S) (x : X) :
    (((ModuleCat.extendRestrictScalarsAdj f).homEquiv X Y).symm g) (s ⊗ₜ[R,f] x) = s • g x := by
  letI := f.toAlgebra
  have h1 : s ⊗ₜ[R] (x : X) = s • (1 : S) ⊗ₜ[R] x := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  change (((ModuleCat.extendRestrictScalarsAdj f).homEquiv X Y).symm g) (s ⊗ₜ[R] x) = s • g x
  rw [h1, map_smul, ModuleCat.extendRestrictScalarsAdj_homEquiv_symm_apply_one_tmul]

section CoefficientHom

variable {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) (r : ℕ)

namespace jetLinearPiece

/-- A morphism of `O_X`-modules commutes with restriction (elementwise). -/
private theorem app_map' {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {W W' : X.Opens}
    (h : W' ≤ W) (x : Γ(M, W)) :
    φ.app W' (M.presheaf.map (homOfLE h).op x) = N.presheaf.map (homOfLE h).op (φ.app W x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x

/-- The jet scheme `J` as a scheme over `k` (through `C`), as needed by `jetThickening`. -/
@[instance_reducible] def jetOver : (relativeJetScheme (k := k) Z sec hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  ⟨(relativeJetScheme (k := k) Z sec hs r).hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩

/-- `pr⁻¹(π⁻¹W) = u⁻¹(π⁻¹W)` for the universal jet `u` (`universalJet_comp_hom`). -/
theorem universalJet_preimage_eq (W : C.toScheme.Opens) :
    letI := jetOver Z sec hs r
    jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z sec hs r).left ⁻¹ᵁ
        ((relativeJetScheme (k := k) Z sec hs r).hom ⁻¹ᵁ W) =
      relativeJetScheme.universalJet (k := k) Z sec hs r ⁻¹ᵁ (Z.hom ⁻¹ᵁ W) := by
  letI := jetOver Z sec hs r
  rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, ← AlgebraicGeometry.Scheme.Hom.comp_preimage,
    relativeJetScheme.universalJet_comp_hom]

variable (q : Fin r)

/-- **The `(q+1)`-st jet coordinate of `b`** as a function on `π⁻¹W`, for any open `W ⊆ C`: the `t^{q+1}`-coefficient of the
universal jet `u^♯ b`. On an affine `U` this is `χ_U (d_q b)` (`chartEquiv_coeffClass`); being defined through the global `u`,
it is natural in `W` (`jetCoordSection_restrict`). -/
def jetCoordSection (W : C.toScheme.Opens) (b : Γ(Z.left, Z.hom ⁻¹ᵁ W)) :
    Γ((relativeJetScheme (k := k) Z sec hs r).left, (relativeJetScheme (k := k) Z sec hs r).hom ⁻¹ᵁ W) :=
  letI := jetOver Z sec hs r
  jetThickening.coeff (k := k) r (relativeJetScheme (k := k) Z sec hs r).left
    ((relativeJetScheme (k := k) Z sec hs r).hom ⁻¹ᵁ W) (q.1 + 1) q.2
    (((relativeJetScheme.universalJet (k := k) Z sec hs r).appLE (Z.hom ⁻¹ᵁ W)
      (jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z sec hs r).left ⁻¹ᵁ
        ((relativeJetScheme (k := k) Z sec hs r).hom ⁻¹ᵁ W))
      (le_of_eq (universalJet_preimage_eq Z sec hs r W))).hom b)

/-- Naturality of the jet coordinate in the open. -/
theorem jetCoordSection_restrict {W W' : C.toScheme.Opens} (h : W' ≤ W) (b : Γ(Z.left, Z.hom ⁻¹ᵁ W)) :
    ((relativeJetScheme (k := k) Z sec hs r).left.presheaf.map (homOfLE
        (show (relativeJetScheme (k := k) Z sec hs r).hom ⁻¹ᵁ W' ≤ (relativeJetScheme (k := k) Z sec hs r).hom ⁻¹ᵁ W from
          (TopologicalSpace.Opens.map _).monotone h)).op).hom (jetCoordSection Z sec hs r q W b) =
      jetCoordSection Z sec hs r q W' ((Z.left.presheaf.map (homOfLE
        (show Z.hom ⁻¹ᵁ W' ≤ Z.hom ⁻¹ᵁ W from (TopologicalSpace.Opens.map _).monotone h)).op).hom b) := by
  letI := jetOver Z sec hs r
  unfold jetCoordSection
  refine (jetThickening.coeff_restrict (k := k) r (relativeJetScheme (k := k) Z sec hs r).left
    ((TopologicalSpace.Opens.map _).monotone h) (q.1 + 1) q.2 _).symm.trans ?_
  refine congrArg (jetThickening.coeff (k := k) r (relativeJetScheme (k := k) Z sec hs r).left _ (q.1 + 1) q.2) ?_
  have h1 := congrArg (fun φ => φ.hom b) (AlgebraicGeometry.Scheme.Hom.appLE_map
    (relativeJetScheme.universalJet (k := k) Z sec hs r) (le_of_eq (universalJet_preimage_eq Z sec hs r W))
    (homOfLE (show jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z sec hs r).left ⁻¹ᵁ
        ((relativeJetScheme (k := k) Z sec hs r).hom ⁻¹ᵁ W') ≤
      jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z sec hs r).left ⁻¹ᵁ
        ((relativeJetScheme (k := k) Z sec hs r).hom ⁻¹ᵁ W) from
      fun _ hx => (TopologicalSpace.Opens.map _).monotone h hx)).op)
  have h2 := congrArg (fun φ => φ.hom b) (AlgebraicGeometry.Scheme.Hom.map_appLE
    (relativeJetScheme.universalJet (k := k) Z sec hs r) (le_of_eq (universalJet_preimage_eq Z sec hs r W'))
    (homOfLE (show Z.hom ⁻¹ᵁ W' ≤ Z.hom ⁻¹ᵁ W from (TopologicalSpace.Opens.map _).monotone h)).op)
  exact h1.trans h2.symm

/-- On an affine `U`, the chart reading of `d_q b` is the jet coordinate: `χ_U (d_q b) = jetCoordSection U b`. -/
theorem chartEquiv_coeffClass (U : C.toScheme.affineOpens) (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1)) :
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    relativeJetScheme.chartEquiv (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U)
        (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z sec hs U.1) r (q.1 + 1) b) =
      jetCoordSection Z sec hs r q U.1 b := by
  letI := jetOver Z sec hs r
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  have hU := relativeJetScheme.hom_preimage_chartOpen (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U)
  refine (relativeJetScheme.chartEquiv_eq_chartSections (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U)
    hU _).trans ?_
  have h1 := relativeJetScheme.coeff_universalJetSections (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U)
    (q.1 + 1) q.2 b
  have h2 : relativeJetScheme.universalJetSections (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U) b =
      ((relativeJetScheme.universalJet (k := k) Z sec hs r).appLE (Z.hom ⁻¹ᵁ U.1)
        (jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z sec hs r).left ⁻¹ᵁ
          relativeJetScheme.chartOpen (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U))
        (relativeJetScheme.universalJet_preimage_le (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U))).hom b :=
    (congrArg (fun φ => φ.hom b)
      (relativeJetScheme.universalJet_appLE_chartOpen (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U))).symm
  rw [h2] at h1
  have h3 : (CategoryTheory.eqToHom hU).op = (homOfLE (le_of_eq hU)).op :=
    congrArg Quiver.Hom.op (Subsingleton.elim _ _)
  refine Eq.trans (congrArg ((relativeJetScheme (k := k) Z sec hs r).left.presheaf.map
    (CategoryTheory.eqToHom hU).op).hom h1.symm) ?_
  rw [h3]
  unfold jetCoordSection
  refine (jetThickening.coeff_restrict (k := k) r (relativeJetScheme (k := k) Z sec hs r).left (le_of_eq hU)
    (q.1 + 1) q.2 _).symm.trans ?_
  refine congrArg (jetThickening.coeff (k := k) r (relativeJetScheme (k := k) Z sec hs r).left _ (q.1 + 1) q.2) ?_
  exact congrArg (fun φ => φ.hom b) (AlgebraicGeometry.Scheme.Hom.appLE_map
    (relativeJetScheme.universalJet (k := k) Z sec hs r)
    (relativeJetScheme.universalJet_preimage_le (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U))
    (homOfLE (show jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z sec hs r).left ⁻¹ᵁ
        ((relativeJetScheme (k := k) Z sec hs r).hom ⁻¹ᵁ U.1) ≤
      jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z sec hs r).left ⁻¹ᵁ
        relativeJetScheme.chartOpen (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U) from
      fun _ hx => (le_of_eq hU) hx)).op)

/-- `σ(d_q b)|_V = σ(d_q (b|_V))` for affine `V ≤ U`. -/
theorem coeffSection_restrict (U V : C.toScheme.affineOpens) (h : V.1 ≤ U.1) (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1)) :
    ((jetGradedAlgebra (k := k) Z sec hs r).1.part (q.1 + 1)).presheaf.map (homOfLE h).op
        (coeffSection Z sec hs r U q b) =
      coeffSection Z sec hs r V q ((Z.left.presheaf.map (homOfLE
        (show Z.hom ⁻¹ᵁ V.1 ≤ Z.hom ⁻¹ᵁ U.1 from (TopologicalSpace.Opens.map _).monotone h)).op).hom b) := by
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  letI := relativeJetScheme.sectionsAlgebra Z V.1
  apply jetSection_injective Z sec hs r V (q.1 + 1)
  rw [jetSection_coeffSection]
  apply (relativeJetScheme.chartEquiv (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite V)).injective
  refine Eq.trans ?_ (chartEquiv_coeffClass Z sec hs r q V _).symm
  refine (RingEquiv.apply_symm_apply
    (relativeJetScheme.chartEquiv (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite V))
    (GroupSchemeAction.weightPartιApp (jetRescalingAction (k := k) Z sec hs r) (q.1 + 1) V.1
      (((jetGradedAlgebra (k := k) Z sec hs r).1.part (q.1 + 1)).presheaf.map (homOfLE h).op
        (coeffSection Z sec hs r U q b)))).trans ?_
  -- `ι_U (σ(d_q b)) = χ_U (d_q b) = jetCoordSection U b`
  have hU : GroupSchemeAction.weightPartιApp (jetRescalingAction (k := k) Z sec hs r) (q.1 + 1) U.1
      (coeffSection Z sec hs r U q b) = jetCoordSection Z sec hs r q U.1 b := by
    refine Eq.trans ?_ (chartEquiv_coeffClass Z sec hs r q U b)
    refine Eq.trans ?_ (congrArg (relativeJetScheme.chartEquiv (k := k) Z sec hs r (AlgebraicGeometry.Scheme.affineSite U))
      (jetSection_coeffSection Z sec hs r U q b))
    exact (RingEquiv.apply_symm_apply _ _).symm
  -- `ι_V (x|_V) = (ι_U x)|_{π⁻¹V}`
  have hnat := app_map' (CategoryTheory.Limits.kernel.ι
    (GroupSchemeAction.weightDefect (jetRescalingAction (k := k) Z sec hs r) (q.1 + 1))) h
    (coeffSection Z sec hs r U q b)
  refine Eq.trans hnat ?_
  refine Eq.trans ?_ (jetCoordSection_restrict Z sec hs r q h b)
  exact congrArg _ hU

/-- `[d_q b]|_V = [d_q (b|_V)]` for affine `V ≤ U`. -/
theorem coeffDerivationFun_restrict (U V : C.toScheme.affineOpens) (h : V.1 ≤ U.1) (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1)) :
    (CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2).presheaf.map
        (homOfLE h).op (coeffDerivationFun Z sec hs r U q b) =
      coeffDerivationFun Z sec hs r V q ((Z.left.presheaf.map (homOfLE
        (show Z.hom ⁻¹ᵁ V.1 ≤ Z.hom ⁻¹ᵁ U.1 from (TopologicalSpace.Opens.map _).monotone h)).op).hom b) := by
  unfold coeffDerivationFun
  refine (app_map' (CategoryTheory.Limits.cokernel.π
    ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2) h _).symm.trans ?_
  exact congrArg _ (coeffSection_restrict Z sec hs r q U V h b)

/-- `((db)|_sec)|_{W'} = (d(b|_{π⁻¹W'}))|_sec` for opens `W' ≤ W`. -/
theorem omegaSection_restrict {W W' : C.toScheme.Opens} (h : W' ≤ W) (b : Γ(Z.left, Z.hom ⁻¹ᵁ W)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback sec).obj (AlgebraicGeometry.Omega Z.hom)).presheaf.map (homOfLE h).op
        (omegaSection Z sec hs W b) =
      omegaSection Z sec hs W' ((Z.left.presheaf.map (homOfLE
        (show Z.hom ⁻¹ᵁ W' ≤ Z.hom ⁻¹ᵁ W from (TopologicalSpace.Opens.map _).monotone h)).op).hom b) := by
  unfold omegaSection
  refine (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_restrict sec (AlgebraicGeometry.Omega Z.hom)
    (relativeJetScheme.section_preimage_le Z sec hs W) (relativeJetScheme.section_preimage_le Z sec hs W')
    ((TopologicalSpace.Opens.map _).monotone h) h _).trans ?_
  exact congrArg _ ((AlgebraicGeometry.Omega.universalDerivation Z.hom).d_map
    (homOfLE (show Z.hom ⁻¹ᵁ W' ≤ Z.hom ⁻¹ᵁ W from (TopologicalSpace.Opens.map _).monotone h)).op b).symm

/-- **The sections `(db)|_sec` span `Γ(U, sec^*Ω_{Z/C})`** over `Γ(C, U)` for affine `U`. -/
theorem span_omegaSection_eq_top (U : C.toScheme.affineOpens) :
    Submodule.span Γ(C.toScheme, U.1) (Set.range (omegaSection Z sec hs U.1)) = ⊤ := by
  letI := chartAlgebra Z U
  rw [eq_top_iff]
  rintro y -
  set N := Submodule.span Γ(C.toScheme, U.1) (Set.range (omegaSection Z sec hs U.1)) with hN
  -- every section `ω` of `Ω_{Z/C}` on `π⁻¹U` has `ω|_sec ∈ N`
  have hω : ∀ ω : Γ(AlgebraicGeometry.Omega Z.hom, Z.hom ⁻¹ᵁ U.1),
      AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn sec (AlgebraicGeometry.Omega Z.hom) (Z.hom ⁻¹ᵁ U.1) U.1
        (relativeJetScheme.section_preimage_le Z sec hs U.1) ω ∈ N := by
    intro ω
    have hmem : AlgebraicGeometry.Omega_appIso Z.hom U.2 (U.2.preimage Z.hom) le_rfl ω ∈
        Submodule.span Γ(Z.left, Z.hom ⁻¹ᵁ U.1) (Set.range (KaehlerDifferential.D Γ(C.toScheme, U.1) Γ(Z.left, Z.hom ⁻¹ᵁ U.1))) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    have key : ∀ z ∈ Submodule.span Γ(Z.left, Z.hom ⁻¹ᵁ U.1)
        (Set.range (KaehlerDifferential.D Γ(C.toScheme, U.1) Γ(Z.left, Z.hom ⁻¹ᵁ U.1))),
        AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn sec (AlgebraicGeometry.Omega Z.hom) (Z.hom ⁻¹ᵁ U.1) U.1
          (relativeJetScheme.section_preimage_le Z sec hs U.1)
          ((AlgebraicGeometry.Omega_appIso Z.hom U.2 (U.2.preimage Z.hom) le_rfl).symm z) ∈ N := by
      intro z hz
      refine Submodule.span_induction (p := fun z _ =>
        AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn sec (AlgebraicGeometry.Omega Z.hom) (Z.hom ⁻¹ᵁ U.1) U.1
          (relativeJetScheme.section_preimage_le Z sec hs U.1)
          ((AlgebraicGeometry.Omega_appIso Z.hom U.2 (U.2.preimage Z.hom) le_rfl).symm z) ∈ N) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨c, rfl⟩
        have hd : (AlgebraicGeometry.Omega_appIso Z.hom U.2 (U.2.preimage Z.hom) le_rfl).symm
            (KaehlerDifferential.D Γ(C.toScheme, U.1) Γ(Z.left, Z.hom ⁻¹ᵁ U.1) c) =
            (AlgebraicGeometry.Omega.universalDerivation Z.hom).d (X := Opposite.op (Z.hom ⁻¹ᵁ U.1)) c :=
          (LinearEquiv.symm_apply_eq _).mpr (AlgebraicGeometry.Omega_appIso_d Z.hom U.2 (U.2.preimage Z.hom) le_rfl c).symm
        rw [hd]
        exact Submodule.subset_span ⟨c, rfl⟩
      · rw [map_zero, map_zero]
        exact Submodule.zero_mem N
      · intro z₁ z₂ _ _ h₁ h₂
        rw [map_add, map_add]
        exact Submodule.add_mem N h₁ h₂
      · intro b' z _ hz'
        rw [map_smul, AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_smul_native]
        exact Submodule.smul_mem N _ hz'
    have := key _ hmem
    rwa [LinearEquiv.symm_apply_apply] at this
  -- `y = Φ t` for some `t ∈ A ⊗_B Γ(π⁻¹U, Ω)`
  haveI := baseChangeHom_isIso Z sec hs U
  obtain ⟨t, rfl⟩ := ((CategoryTheory.ConcreteCategory.bijective_of_isIso (baseChangeHom Z sec hs U)).2 y)
  induction t using TensorProduct.induction_on with
  | zero =>
    have h0 : (baseChangeHom Z sec hs U) 0 = 0 := map_zero _
    exact (congrArg (· ∈ N) h0).mpr (Submodule.zero_mem N)
  | tmul a ω =>
    have h1 := ModuleCat.extendRestrictScalarsAdj_homEquiv_symm_apply_tmul (augRingHom Z sec hs U)
      (AlgebraicGeometry.Scheme.Modules.pullbackSectionsNative sec (AlgebraicGeometry.Omega Z.hom) (Z.hom ⁻¹ᵁ U.1) U.1
        (relativeJetScheme.section_preimage_le Z sec hs U.1)) a ω
    exact (congrArg (· ∈ N) h1).mpr (Submodule.smul_mem N a (hω ω))
  | add t₁ t₂ h₁ h₂ =>
    have hadd : (baseChangeHom Z sec hs U) (t₁ + t₂) =
        (baseChangeHom Z sec hs U) t₁ + (baseChangeHom Z sec hs U) t₂ := map_add _ _ _
    exact (congrArg (· ∈ N) hadd).mpr (Submodule.add_mem N h₁ h₂)

/-- **Naturality of the local coefficient maps**: for affine `V ≤ U`, `Γ(L, V ≤ U) ∘ θ_U = θ_V ∘ Γ(sec^*Ω, V ≤ U)`. -/
theorem coeffMap_restrict (U V : C.toScheme.affineOpens) (h : V.1 ≤ U.1)
    (m : Γ((AlgebraicGeometry.Scheme.Modules.pullback sec).obj (AlgebraicGeometry.Omega Z.hom), U.1)) :
    (CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2).presheaf.map
        (homOfLE h).op (coeffMap Z sec hs r U q m) =
      coeffMap Z sec hs r V q
        (((AlgebraicGeometry.Scheme.Modules.pullback sec).obj (AlgebraicGeometry.Omega Z.hom)).presheaf.map
          (homOfLE h).op m) := by
  have hm : m ∈ Submodule.span Γ(C.toScheme, U.1) (Set.range (omegaSection Z sec hs U.1)) := by
    rw [span_omegaSection_eq_top]
    trivial
  refine Submodule.span_induction (p := fun m _ =>
    (CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2).presheaf.map
        (homOfLE h).op (coeffMap Z sec hs r U q m) =
      coeffMap Z sec hs r V q
        (((AlgebraicGeometry.Scheme.Modules.pullback sec).obj (AlgebraicGeometry.Omega Z.hom)).presheaf.map
          (homOfLE h).op m)) ?_ ?_ ?_ ?_ hm
  · rintro _ ⟨b, rfl⟩
    rw [coeffMap_omegaSection, coeffDerivationFun_restrict Z sec hs r q U V h b, omegaSection_restrict Z sec hs h b,
      coeffMap_omegaSection]
  · rw [map_zero, map_zero, map_zero, map_zero]
  · intro m₁ m₂ _ _ h₁ h₂
    rw [map_add, map_add, h₁, h₂, map_add, map_add]
  · intro a m _ hm'
    rw [map_smul, AlgebraicGeometry.Scheme.Modules.map_smul, hm', AlgebraicGeometry.Scheme.Modules.map_smul, map_smul]

end jetLinearPiece

end CoefficientHom

end
