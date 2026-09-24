import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebra_Construction
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentAffineLocal
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualCoevZigzag
import MiyaokaMori.RingTheory.GradedRing.ReesAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.BiproductSections
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAtlasPullback
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraLWP_HomSectionsRing
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraLWP_PullbackSpan
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraLWP_IrrPowSections

/-! # The Rees deformation is locally weighted-polynomial

If `S` is locally the weighted polynomial algebra `Γ(U)[x_s]` (weights `w s ≥ 1`), then its extended Rees deformation
`R = S.reesDeformation` on `𝔸¹_X` is locally the weighted polynomial algebra `Γ(π⁻¹U)[y_s]`, `y_s = λ^{w s - 1} x_s`, with
the same weights (Lemma 2.3 of the paper, the `λ`-rescaling `y_s = λ^{w s-1} x_s`; Stacks 052P;
Stacks 01XB for exactness of sections on affines).

Structure of this file:
* §0 charts: `π⁻¹U` is affine for affine `U` (`π` is an affine morphism); `λ|_V` (`lambdaRes`).
* §1 `Γ(𝔸¹_X, π⁻¹U) ≃+* Γ(X, U)[λ]` for affine `U`; corollary: `λ|_{π⁻¹U}` is a nonzerodivisor.
* §2 sections of `mulCoordPow e M` are multiplication by `λ^e|_V`.
* §3 (via `DeformedJetAlgebraLWP_IrrPowSections`) sections of `I^{(p)}_j` over an affine `U` are `irrPow p j` of the
  section ring (sheaf ↔ ring).
* §4 sections of the Rees piece `R_j` over an affine `V` are `Σ_e λ^e · Γ(V, π^*I^{(j-e)}_j)` (Stacks 01XB).
* §5 pure algebra on `MvPolynomial σ B`: `irrPow` = monomial span; the rescaling `y_s ↦ t^{w s-1} x_s` is injective
  (for `t` a nonzerodivisor) and maps the weight-`j` part onto the Rees span.
* §6 `reesDeformation_isLocallyWeightedPolynomial`: the assembly of §0–§5 with `WeightedPolynomialAtlasPullback` (the
  chart isomorphism `Ψ_i` of `π^*S`, Stacks 01I9) and the helper modules `DeformedJetAlgebraLWP_HomSectionsRing`
  (section-ring homomorphism `ι` of `inclHom S`, injective), `DeformedJetAlgebraLWP_PullbackSpan` (01I9 in span form,
  naturality, base change of spans) and `DeformedJetAlgebraLWP_IrrPowSections`. Chart `i`: `V_i := π⁻¹U_i`,
  `Θ_i := Ψ_i ∘ ι : R(V_i) → Γ_i[x_s]`, `Φ_i := reesRescale λ_i w : Γ_i[y_s] → Γ_i[x_s]`; both injective with image
  `⊕_j reesSpan λ_i w j`, so `e_i := Φ_i⁻¹ ∘ Θ_i` (`AlgEquiv.ofInjective` + `Subalgebra.equivOfEq`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory
open scoped ZeroObject

/-! ## §0 Charts -/

namespace AlgebraicGeometry.Scheme.affineLineOver

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `toBase X = 𝔸(1; X) ↘ X` is an affine morphism (Mathlib: base change of `Spec ℤ[t] → Spec ℤ`).
Stated as a theorem, not an instance; supply it locally with
`haveI := isAffineHom_toBase (X := X)`. -/
theorem isAffineHom_toBase : AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.Scheme.affineLineOver.toBase X) :=
  inferInstanceAs (AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X))

/-- **(a1)** The preimage `π⁻¹U ⊆ A¹_X` of an affine open `U ⊆ X` is affine (`IsAffineOpen.preimage`, `π` affine). These are the
charts of the atlas of `S.reesDeformation`. -/
theorem isAffineOpen_preimage_toBase {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) :
    AlgebraicGeometry.IsAffineOpen (AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U) :=
  haveI := AlgebraicGeometry.Scheme.affineLineOver.isAffineHom_toBase (X := X)
  hU.preimage (AlgebraicGeometry.Scheme.affineLineOver.toBase X)

/-- The coordinate `λ` restricted to an open `V ⊆ A¹_X`. -/
noncomputable abbrev lambdaRes (V : (AlgebraicGeometry.Scheme.affineLineOver X).Opens) :
    Γ(AlgebraicGeometry.Scheme.affineLineOver X, V) :=
  ((AlgebraicGeometry.Scheme.affineLineOver X).presheaf.map (CategoryTheory.homOfLE (le_top : V ≤ ⊤)).op).hom
    (AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1)))

/-! ## §1 `Γ(A¹_X, π⁻¹U) = Γ(X, U)[λ]` -/

/-- `f.appLE ⊤ ⊤ _ = f.appTop` (`Opens.map_top` is `rfl`, so the restriction map is the identity). -/
private theorem appLE_top_top {Y Z : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ Z) (e : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop :=
  AlgebraicGeometry.Scheme.Hom.appLE_eq_app f

/-- Pointwise `ΓSpecIso` naturality: `(Spec.map f).appTop (ΓSpecIso.inv x) = ΓSpecIso.inv (f x)`. -/
private theorem Spec_map_appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (f : R ⟶ S) (x : R) :
    (AlgebraicGeometry.Spec.map f).appTop ((AlgebraicGeometry.Scheme.ΓSpecIso R).inv x) =
      (AlgebraicGeometry.Scheme.ΓSpecIso S).inv (f x) := by
  rw [← CommRingCat.comp_apply, ← AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

/-- `X.isoSpec.inv.appTop = (ΓSpecIso Γ(X, ⊤)).inv` pointwise. -/
private theorem isoSpec_inv_appTop_apply (Y : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (t : Γ(Y, ⊤)) :
    Y.isoSpec.inv.appTop t = (AlgebraicGeometry.Scheme.ΓSpecIso Γ(Y, ⊤)).inv t := by
  have h1 : Y.isoSpec.hom.appTop (Y.isoSpec.inv.appTop t) = t := by
    rw [← CommRingCat.comp_apply, ← AlgebraicGeometry.Scheme.Hom.comp_appTop, Iso.hom_inv_id]
    simp
  have h2 : Y.isoSpec.hom.appTop = (AlgebraicGeometry.Scheme.ΓSpecIso Γ(Y, ⊤)).hom := Y.toSpecΓ_appTop
  rw [h2] at h1
  calc Y.isoSpec.inv.appTop t
      = (AlgebraicGeometry.Scheme.ΓSpecIso Γ(Y, ⊤)).inv
          ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(Y, ⊤)).hom (Y.isoSpec.inv.appTop t)) := by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
    _ = (AlgebraicGeometry.Scheme.ΓSpecIso Γ(Y, ⊤)).inv t := by rw [h1]

/-- Rewriting the morphism under `appLE`. -/
private theorem appLE_of_eq {Y Z : AlgebraicGeometry.Scheme.{u}} {g g' : Y ⟶ Z} (h : g = g') (U : Z.Opens) (V : Y.Opens)
    (e : V ≤ g ⁻¹ᵁ U) : g.appLE U V e = g'.appLE U V (h ▸ e) := by
  subst h; rfl

/-- Two restriction maps of a presheaf on `Opens` that go back and forth compose to the identity. -/
private theorem presheaf_map_op_comp_map_op {Y : AlgebraicGeometry.Scheme.{u}} {A B : Y.Opens} (a : A ⟶ B) (b : B ⟶ A) :
    Y.presheaf.map a.op ≫ Y.presheaf.map b.op = 𝟙 _ := by
  rw [← CategoryTheory.Functor.map_comp, ← op_comp, Subsingleton.elim (b ≫ a) (𝟙 B), op_id,
    CategoryTheory.Functor.map_id]

/-- `U.ι.appLE U ⊤ _` followed by `U.topIso.hom` is the identity of `Γ(X, U)`. -/
private theorem ι_appLE_comp_topIso_hom {Y : AlgebraicGeometry.Scheme.{u}} (U : Y.Opens)
    (e : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U) : U.ι.appLE U ⊤ e ≫ U.topIso.hom = 𝟙 _ := by
  rw [AlgebraicGeometry.Scheme.Opens.ι_appLE]
  simp only [AlgebraicGeometry.Scheme.Opens.topIso_hom]
  exact presheaf_map_op_comp_map_op _ _

/-- **Sections of `𝔸¹_X` over `π⁻¹U`, `U` affine: `Γ(𝔸¹_X, π⁻¹U) ≃+* Γ(X, U)[λ]`, `λ ↦ X`, `π^♯ r ↦ C r`.**
Source: Mathlib `AlgebraicGeometry.AffineSpace` (`isoOfIsAffine`, `SpecIso`, `isPullback_map`); Stacks 01I1
(`𝔸¹_U = Spec Γ(U)[t]`).

Proof: by `AffineSpace.isPullback_map U.ι`, the chart isomorphism `θ : 𝔸(1;U) ≅ 𝔸(1;X) ∣_ π⁻¹U` is
`hpb.isoPullback ≪≫ pullbackRestrictIsoRestrict π U` (so `θ.hom ≫ ι = AffineSpace.map U.ι` is formal), and the ring
isomorphism is `ι.appLE (π⁻¹U) ⊤ ≫ θ.hom.appTop ≫ (isoOfIsAffine).inv.appTop ≫ ΓSpecIso.hom` followed by
`MvPolynomial.mapEquiv U.topIso`, under which `λ|_{π⁻¹U} ↦ X` (`map_appTop_coord`, `isoOfIsAffine_inv_appTop_coord`) and
`π^♯ r ↦ C r` (`map_over`, `isoOfIsAffine_inv_over`). The proof `delta`-unfolds `affineLineOver`/`toBase`/`lambdaRes`
first. Edge case: `U = ⊥` gives the zero ring on both sides. -/
theorem exists_sections_preimage_equiv {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) :
    ∃ e : Γ(AlgebraicGeometry.Scheme.affineLineOver X, AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U) ≃+*
        MvPolynomial (ULift.{u} (Fin 1)) Γ(X, U),
      e (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U)) =
          MvPolynomial.X ⟨0⟩ ∧
        ∀ r : Γ(X, U), e (((AlgebraicGeometry.Scheme.affineLineOver.toBase X).app U).hom r) = MvPolynomial.C r := by
  haveI : AlgebraicGeometry.IsAffine U := hU
  -- work in the `𝔸(1; X)` world throughout (`affineLineOver`/`toBase` are semireducible defs: mixing them with
  -- `𝔸(1; X)` inside implicit arguments of `pullback`/`appTop` blocks `rw`)
  delta AlgebraicGeometry.Scheme.affineLineOver.lambdaRes AlgebraicGeometry.Scheme.affineLineOver.toBase
    AlgebraicGeometry.Scheme.affineLineOver
  -- the chart morphism `𝔸(1; U) → 𝔸(1; X)` and its pullback square
  have hpb := AlgebraicGeometry.AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) U.ι
  let θ := hpb.isoPullback ≪≫ AlgebraicGeometry.pullbackRestrictIsoRestrict (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) U
  have hθ : θ.hom ≫ ((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U).ι = AlgebraicGeometry.AffineSpace.map (ULift.{u} (Fin 1)) U.ι := by
    dsimp only [θ]
    rw [Iso.trans_hom, Category.assoc, AlgebraicGeometry.pullbackRestrictIsoRestrict_hom_ι,
      IsPullback.isoPullback_hom_fst]
  -- the ring isomorphisms
  have e0 : (⊤ : ((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U).toScheme.Opens) ≤ ((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U).ι ⁻¹ᵁ ((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U) := ((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U).ι_preimage_self.ge
  let ψ₀ := ((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U).ι.appLE ((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U) ⊤ e0
  have : IsIso ψ₀ := inferInstance
  let Ψ₁ : Γ((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U, ⊤) ≅ Γ(AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) U, ⊤) := AlgebraicGeometry.Scheme.Γ.mapIso θ.op
  let Ψ₂ : Γ(AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) U, ⊤) ≅ Γ(AlgebraicGeometry.Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) Γ(U, ⊤))), ⊤) :=
    AlgebraicGeometry.Scheme.Γ.mapIso (AlgebraicGeometry.AffineSpace.isoOfIsAffine (ULift.{u} (Fin 1)) U).symm.op
  have hΨ₁ : Ψ₁.hom = θ.hom.appTop := rfl
  have hΨ₂ : Ψ₂.hom = (AlgebraicGeometry.AffineSpace.isoOfIsAffine (ULift.{u} (Fin 1)) U).inv.appTop := rfl
  let ψ₃ := (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) Γ(U, ⊤)))).hom
  let e : Γ(AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X, (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U) ≃+* MvPolynomial (ULift.{u} (Fin 1)) Γ(X, U) :=
    ((asIso ψ₀ ≪≫ Ψ₁ ≪≫ Ψ₂ ≪≫
      AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) Γ(U, ⊤)))).commRingCatIsoToRingEquiv).trans
      (MvPolynomial.mapEquiv (ULift.{u} (Fin 1)) U.topIso.commRingCatIsoToRingEquiv)
  have he : ∀ x, e x = MvPolynomial.mapEquiv (ULift.{u} (Fin 1)) U.topIso.commRingCatIsoToRingEquiv
      (ψ₃ (Ψ₂.hom (Ψ₁.hom (ψ₀ x)))) := fun x => rfl
  have hψ₃ : ∀ y, ψ₃ ((AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) Γ(U, ⊤)))).inv y) = y := fun y => by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  -- `θ.hom.appTop ∘ ι.appTop = (map U.ι).appTop`
  have h1 : ((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U).ι.appTop ≫ θ.hom.appTop = (AlgebraicGeometry.AffineSpace.map (ULift.{u} (Fin 1)) U.ι).appTop := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_appTop, hθ]
  refine ⟨e, ?_, ?_⟩
  · -- λ ↦ X
    have hc : (AlgebraicGeometry.AffineSpace.map (ULift.{u} (Fin 1)) U.ι).appTop (AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1))) =
        AlgebraicGeometry.AffineSpace.coord U (⟨0⟩ : ULift.{u} (Fin 1)) := by
      rw [AlgebraicGeometry.AffineSpace.map_appTop_coord]
    have h0 : (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X).presheaf.map (homOfLE (le_top : (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U ≤ ⊤)).op ≫ ψ₀ = ((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U).ι.appTop := by
      rw [AlgebraicGeometry.Scheme.Hom.map_appLE, appLE_top_top]
    have h0' : ψ₀ ((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X).presheaf.map (homOfLE (le_top : (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U ≤ ⊤)).op
          (AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1)))) =
        ((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U).ι.appTop (AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1))) := by
      rw [← CommRingCat.comp_apply, h0]
    have h1' : θ.hom.appTop (((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U).ι.appTop (AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1)))) =
        (AlgebraicGeometry.AffineSpace.map (ULift.{u} (Fin 1)) U.ι).appTop (AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1))) := by
      rw [← CommRingCat.comp_apply, h1]
    rw [he, hΨ₁, hΨ₂]
    change MvPolynomial.mapEquiv (ULift.{u} (Fin 1)) U.topIso.commRingCatIsoToRingEquiv
      (ψ₃ ((AlgebraicGeometry.AffineSpace.isoOfIsAffine (ULift.{u} (Fin 1)) U).inv.appTop (θ.hom.appTop
      (ψ₀ ((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X).presheaf.map (homOfLE (le_top : (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U ≤ ⊤)).op
          (AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1)))))))) = _
    rw [h0', h1', hc, AlgebraicGeometry.AffineSpace.isoOfIsAffine_inv_appTop_coord, hψ₃]
    rw [MvPolynomial.mapEquiv_apply, MvPolynomial.map_X]
  · -- constants
    intro r
    have e1 : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := U.ι_preimage_self.ge
    have e2 : (⊤ : ((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U).toScheme.Opens) ≤ (((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U).ι ≫ (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X)) ⁻¹ᵁ U := fun x _ => x.2
    have hfπ : AlgebraicGeometry.AffineSpace.map (ULift.{u} (Fin 1)) U.ι ≫ (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) = (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) U ↘ U) ≫ U.ι := AlgebraicGeometry.AffineSpace.map_over U.ι
    -- ψ₀ ∘ π.app U = (ι ≫ π).appLE U ⊤
    have h2 := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE ((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U).ι (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) U ((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U) ⊤ le_rfl e0
    rw [AlgebraicGeometry.Scheme.Hom.appLE_eq_app] at h2
    -- θ.hom.appTop ∘ (ι ≫ π).appLE U ⊤ = ((𝔸U ↘ U) ≫ U.ι).appLE U ⊤ = U.ι.appLE U ⊤ ≫ (𝔸U ↘ U).appTop
    have h3 := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE θ.hom (((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U).ι ≫ (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X)) U ⊤ ⊤ e2 le_top
    have hcomp : θ.hom ≫ ((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U).ι ≫ (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) = (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) U ↘ U) ≫ U.ι := by
      rw [← Category.assoc, hθ]; exact hfπ
    erw [appLE_top_top θ.hom] at h3
    rw [appLE_of_eq hcomp] at h3
    have h4 := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) U ↘ U) U.ι U ⊤ ⊤ e1 le_top
    erw [appLE_top_top (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) U ↘ U)] at h4
    rw [← h4] at h3
    -- (isoOfIsAffine.inv ≫ (𝔸U ↘ U)).appTop = (Spec.map C ≫ U.isoSpec.inv).appTop
    have h5 := congrArg AlgebraicGeometry.Scheme.Hom.appTop
      (AlgebraicGeometry.AffineSpace.isoOfIsAffine_inv_over (n := ULift.{u} (Fin 1)) (S := U))
    rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, AlgebraicGeometry.Scheme.Hom.comp_appTop] at h5
    have h6 : U.topIso.hom ((U.ι.appLE U ⊤ e1) r) = r := by
      rw [← CommRingCat.comp_apply, ι_appLE_comp_topIso_hom U e1, CommRingCat.id_apply]
    have h2' : ψ₀ (((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X).app U).hom r) = ((((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U).ι ≫ (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X)).appLE U ⊤ e2) r := by
      change ψ₀ ((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X).app U r) = _
      rw [← CommRingCat.comp_apply, h2]
    have h3' : θ.hom.appTop (((((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ⁻¹ᵁ U).ι ≫ (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X)).appLE U ⊤ e2) r) = (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) U ↘ U).appTop ((U.ι.appLE U ⊤ e1) r) := by
      rw [← CommRingCat.comp_apply, h3, CommRingCat.comp_apply]
    have h5' : (AlgebraicGeometry.AffineSpace.isoOfIsAffine (ULift.{u} (Fin 1)) U).inv.appTop
        ((AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) U ↘ U).appTop ((U.ι.appLE U ⊤ e1) r)) =
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom MvPolynomial.C)).appTop
          ((U.toScheme.isoSpec).inv.appTop ((U.ι.appLE U ⊤ e1) r)) := by
      rw [← CommRingCat.comp_apply, h5, CommRingCat.comp_apply]
      rfl
    rw [he, hΨ₁, hΨ₂, h2', h3', h5', isoSpec_inv_appTop_apply]
    erw [Spec_map_appTop_ΓSpecIso_inv, hψ₃]
    simp only [CommRingCat.hom_ofHom]
    erw [MvPolynomial.mapEquiv_apply, MvPolynomial.map_C]
    exact congrArg MvPolynomial.C h6

/-- **(a2') `λ|_{π⁻¹U}` is a nonzerodivisor on `Γ(A¹_X, π⁻¹U)` for affine `U`** (from (a2): it corresponds to the variable
`X ∈ Γ(U)[X]`, which is regular, `MvPolynomial.isRegular_X`). This is what makes the rescaling `y_s ↦ λ^{w s-1} x_s`
injective on the chart. -/
theorem lambdaRes_mem_nonZeroDivisors {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) :
    AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U) ∈
      nonZeroDivisors Γ(AlgebraicGeometry.Scheme.affineLineOver X, AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U) := by
  obtain ⟨e, he, -⟩ := AlgebraicGeometry.Scheme.affineLineOver.exists_sections_preimage_equiv hU
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · apply e.injective
    have h := congrArg e hx
    rw [map_mul, he, map_zero] at h
    rw [map_zero]
    exact (MvPolynomial.isRegular_X (n := (⟨0⟩ : ULift.{u} (Fin 1)))).left (h.trans (mul_zero _).symm)
  · apply e.injective
    have h := congrArg e hx
    rw [map_mul, he, map_zero] at h
    rw [map_zero]
    exact (MvPolynomial.isRegular_X (n := (⟨0⟩ : ULift.{u} (Fin 1)))).right (h.trans (zero_mul _).symm)

/-! ## §2 Sections of `mulCoordPow` -/

/-- **(a3) Sections of `mulCoordPow e M` over `V` are multiplication by `λ^e|_V`**: `(λ_ M).inv` is `x ↦ 1 ⊗ x`
(`leftUnitor_inv_app`), `unitMul a ▷ M` acts on the first factor (`whiskerRight_app_tensorSections'`,
`unitMul_val_app_apply`: `1 ↦ a|_V`), and `(λ_ M).hom` is `r ⊗ x ↦ r • x` (`leftUnitor_app_tensorSections`). -/
theorem mulCoordPow_app (e : ℕ) (M : (AlgebraicGeometry.Scheme.affineLineOver X).Modules)
    (V : (AlgebraicGeometry.Scheme.affineLineOver X).Opens) (x : Γ(M, V)) :
    (AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e M).app V x =
      (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes V) ^ e • x := by
  have key : ∀ (f : 𝟙_ (AlgebraicGeometry.Scheme.affineLineOver X).Modules ⟶
      𝟙_ (AlgebraicGeometry.Scheme.affineLineOver X).Modules) (r : Γ(AlgebraicGeometry.Scheme.affineLineOver X, V)),
      f.app V (AlgebraicGeometry.Scheme.Modules.DualZigzag.unitOne V) = r →
      ((λ_ M).inv ≫ (f ▷ M) ≫ (λ_ M).hom).app V x = r • x := by
    intro f r hf
    show (λ_ M).hom.app V ((f ▷ M).app V ((λ_ M).inv.app V x)) = r • x
    rw [AlgebraicGeometry.Scheme.Modules.DualZigzag.leftUnitor_inv_app,
      AlgebraicGeometry.Scheme.Modules.DualZigzag.whiskerRight_app_tensorSections', hf,
      AlgebraicGeometry.Scheme.Modules.leftUnitor_app_tensorSections]
  unfold AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow
  apply key
  have h2 := AlgebraicGeometry.Scheme.Modules.unitMul_val_app_apply
    ((AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1)) :
      Γ(AlgebraicGeometry.Scheme.affineLineOver X, ⊤)) ^ e) (op V)
    (1 : (AlgebraicGeometry.Scheme.affineLineOver X).ringCatSheaf.obj.obj (op V))
  refine h2.trans ?_
  show (1 : Γ(AlgebraicGeometry.Scheme.affineLineOver X, V)) *
      ((AlgebraicGeometry.Scheme.affineLineOver X).presheaf.map (CategoryTheory.homOfLE (le_top : V ≤ ⊤)).op).hom
        ((AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1)) :
          Γ(AlgebraicGeometry.Scheme.affineLineOver X, ⊤)) ^ e) =
      AlgebraicGeometry.Scheme.affineLineOver.lambdaRes V ^ e
  rw [one_mul]
  exact map_pow ((AlgebraicGeometry.Scheme.affineLineOver X).presheaf.map (CategoryTheory.homOfLE (le_top : V ≤ ⊤)).op).hom
    (AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1)) : Γ(AlgebraicGeometry.Scheme.affineLineOver X, ⊤)) e

end AlgebraicGeometry.Scheme.affineLineOver

/-! ## §3 Sections of `I^{(p)}_j` on an affine open (sheaf ↔ ring) -/

/-- The `Γ(X, U)`-linear map on sections induced by a morphism of module sheaves (`Hom.app` is only additive;
`Hom.app_smul` supplies linearity). Now an alias of `Hom.appLinearMap` (`DeformedJetAlgebraLWP_PullbackSpan.lean`), kept
under this name because the statement of (a5) `reesDeformation.incl_app_range_eq` uses it. -/
abbrev AlgebraicGeometry.Scheme.Modules.Hom.appLin {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (U : X.Opens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) :=
  AlgebraicGeometry.Scheme.Modules.Hom.appLinearMap φ U

@[simp] theorem AlgebraicGeometry.Scheme.Modules.Hom.appLin_apply {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (U : X.Opens) (s : Γ(M, U)) :
    AlgebraicGeometry.Scheme.Modules.Hom.appLin φ U s = φ.app U s := rfl

/-- Evaluating a composite of module-sheaf morphisms on a section (definitional; local copy, kept `private` to avoid a
name clash with the identical lemma in other modules). -/
private theorem AlgebraicGeometry.Scheme.Modules.Hom.comp_app_apply_lwp {X : AlgebraicGeometry.Scheme.{u}} {M N K : X.Modules}
    (φ : M ⟶ N) (ψ : N ⟶ K) (U : X.Opens) (x : Γ(M, U)) :
    (φ ≫ ψ).app U x = ψ.app U (φ.app U x) := rfl

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- **Sections of the irrelevant-ideal powers over an affine open are the ring-theoretic `irrPow`**: for `U` affine and
`x ∈ Γ(U, S_j)`, `x` lies in the image of `Γ(U, I^{(p)}_j) → Γ(U, S_j)` iff, as an element of the section ring
`S(U) = ⊕_m Γ(U, S_m)` (`ofPiece`), it lies in `(S(U)_+)^p ∩ S(U)_j = ReesAlgebra.irrPow (S.gradingSubmodule U) p j`.
Source: Stacks 01XB / 01IB (sections over an affine open are an exact equivalence on quasi-coherent sheaves); pure
algebra for the degree-`j` part of a product of homogeneous ideals.

Proof (`DeformedJetAlgebraLWP_IrrPowSections`: `ofPiece_irrelevantPow_app_mem_irrPow` for `⇒`,
`exists_irrelevantPow_app_eq_of_mem_irrPow` for `⇐`), by induction on `p` in both directions. `p = 0`: `I^{(0)}_j = S_j`
and `irrPow 0 j = 𝒜 j`. `p+1`: `I^{(p+1)}_j = Im(g)`, `g : ⊕_{a<j} S_{a+1} ⊗ I^{(p)}_{j-a-1} → S_j`. For `⇒`, on affine `U`
the image of `Γ(U, Im g)` is `Γ(U, g)(Γ(U, ⊕ …))` (exactness of `Γ(U, ·)` on quasi-coherent modules,
`gammaAffine_exact_iff`), sections of the finite biproduct are sums of components, sections of `S_{a+1} ⊗ I^{(p)}_{j-a-1}`
over affine `U` are spanned by `tensorSections` (`tensorSectionsHom_app_bijective_of_isAffineOpen`), on which `g` is
`a ⊗ y ↦ a · ι(y)`, a product of an element of `𝒜₊` and an element of `𝒜₊^p`. For `⇐` (no affineness needed), the
pure-algebra lemma `ReesAlgebra.irrPow_succ_le` (`𝒜₊^{p+1} ∩ 𝒜_j ⊆ N j` whenever `𝒜_d · (𝒜₊^p ∩ 𝒜_e) ⊆ N (d+e)` for
`d ≥ 1`) is applied to `N n := of_n '' Im Γ(U, ι_{p+1,n})`, using `landsIn_whiskerLeft_irrelevantPow_mul_succ`.
Edge cases: `j = 0`, `p ≥ 1`: both sides are `0`; `U = ⊥`: zero ring. -/
theorem irrelevantPow_app_range_iff (U : X.AffineZariskiSite) (p j : ℕ) (x : S.sectionsPiece U.toOpens j) :
    (∃ y, (S.irrelevantPow p j).2.app U.toOpens y = x) ↔
      (S.ofPiece U.toOpens j x : S.toGradedAffineAlgebra.toAffineAlgebra.sections U) ∈
        ReesAlgebra.irrPow (S.toGradedAffineAlgebra.gradingSubmodule U) p j :=
  ⟨fun ⟨y, hy⟩ => hy ▸ S.ofPiece_irrelevantPow_app_mem_irrPow U p j y,
    S.exists_irrelevantPow_app_eq_of_mem_irrPow U p j x⟩

/-! ## §4 Sections of the Rees piece on an affine open -/

/-- **Sections of the Rees piece over an affine `V ⊆ 𝔸¹_X`**: the image of `Γ(V, R_j) → Γ(V, π^*S_j)` is
`Σ_{e=0}^{j} λ^e · Im(Γ(V, π^*I^{(j-e)}_j) → Γ(V, π^*S_j))`. Source: Stacks 01XB (`Γ(V, ·)` exact on quasi-coherent
modules over affine `V`); the definition `R_j = Im(gen S j)`.

Proof: `incl S j = image.ι (gen S j)` and `gen S j = factorThruImage ≫ incl` (`image.fac`); `factorThruImage` is an
epimorphism between quasi-coherent modules, so by `gammaAffine_exact_iff` its sections over the affine `V` are
surjective; hence `range Γ(V, incl) = range Γ(V, gen)`. Sections of the finite biproduct are the product of sections
(`biproduct_sections_total`: every section is `Σ_e ι_e(x_e)`), and `ι_e ≫ gen = pullMap ι_{j-e} ≫ mulCoordPow e`
(`ι_gen`), whose sections are `x ↦ λ^e|_V • Γ(V, pullMap ι_{j-e}) x` (`mulCoordPow_app`). So
`range Γ(V, gen) = Σ_e (range Γ(V, pullMap ι_{j-e})).map (λ^e •)`. Edge cases: `j = 0`: one summand, `R_0 = π^*S_0`;
`V = ⊥`. -/
theorem reesDeformation.incl_app_range_eq {V : (AlgebraicGeometry.Scheme.affineLineOver X).Opens}
    (hV : AlgebraicGeometry.IsAffineOpen V) (j : ℕ) :
    LinearMap.range (AlgebraicGeometry.Scheme.Modules.Hom.appLin
        (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S j) V) =
      ⨆ e : Fin (j + 1),
        (LinearMap.range (AlgebraicGeometry.Scheme.Modules.Hom.appLin
            (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.pullMap S
              (S.irrelevantPow (j - e.1) j).2) V)).map
          (LinearMap.lsmul Γ(AlgebraicGeometry.Scheme.affineLineOver X, V) _
            ((AlgebraicGeometry.Scheme.affineLineOver.lambdaRes V) ^ e.1)) := by
  classical
  set g := AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen S j with hg
  have hfac : ∀ x, g.app V x =
      (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S j).app V
        ((CategoryTheory.Limits.factorThruImage g).app V x) := fun x => by
    have h := congrArg (fun φ : _ ⟶ (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part j =>
      φ.app V x) (CategoryTheory.Limits.image.fac g)
    rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app_apply_lwp] at h
    exact h.symm
  let F : Fin (j + 1) → (AlgebraicGeometry.Scheme.affineLineOver X).Modules := fun e =>
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).obj
      (S.irrelevantPow (j - e.1) j).1
  have hcomp : ∀ (e : Fin (j + 1)) (y : Γ(F e, V)),
      g.app V ((CategoryTheory.Limits.biproduct.ι F e).app V y) =
        (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes V) ^ e.1 •
          (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.pullMap S
            (S.irrelevantPow (j - e.1) j).2).app V y := fun e y => by
    have h := congrArg (fun φ : _ ⟶ (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part j =>
      φ.app V y) (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.ι_gen S j e)
    rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app_apply_lwp, AlgebraicGeometry.Scheme.Modules.Hom.comp_app_apply_lwp,
      AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow_app] at h
    exact h
  have hsurj : Function.Surjective ((CategoryTheory.Limits.factorThruImage g).app V) := by
    have hqc1 : (CategoryTheory.Limits.biproduct F).IsQuasicoherent := by
      refine AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biproduct _ fun e => ?_
      have := AlgebraicGeometry.Scheme.GradedQCAlgebra.irrelevantPow_isQuasicoherent S (j - e.1) j
      infer_instance
    have hqc2 := AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part_isQuasicoherent S j
    have hqc3 : (0 : (AlgebraicGeometry.Scheme.affineLineOver X).Modules).IsQuasicoherent :=
      AlgebraicGeometry.Scheme.Modules.isQuasicoherent_zero _
    let C : CategoryTheory.ShortComplex (AlgebraicGeometry.Scheme.affineLineOver X).Modules :=
      CategoryTheory.ShortComplex.mk (CategoryTheory.Limits.factorThruImage g)
        (0 : AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S j ⟶ 0) CategoryTheory.Limits.comp_zero
    have hC : C.Exact := (CategoryTheory.ShortComplex.exact_iff_epi C rfl).mpr inferInstance
    have hex := (AlgebraicGeometry.Scheme.Modules.gammaAffine_exact_iff C).mp hC ⟨V, hV⟩
    intro y
    have h0 : (C.g.app V).hom y = 0 := by
      show ((0 : AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S j ⟶ 0).app V).hom y = 0
      rw [AlgebraicGeometry.Scheme.Modules.Hom.zero_app, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply]
    obtain ⟨x, hx⟩ := (hex y).mp h0
    exact ⟨x, hx⟩
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := hsurj z
    rw [AlgebraicGeometry.Scheme.Modules.Hom.appLin_apply, ← hfac x,
      AlgebraicGeometry.Scheme.Modules.biproduct_sections_total F V x, map_sum]
    refine Submodule.sum_mem _ fun e _ => ?_
    refine Submodule.mem_iSup_of_mem e (Submodule.mem_map.2
      ⟨(AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.pullMap S (S.irrelevantPow (j - e.1) j).2).app V
          ((CategoryTheory.Limits.biproduct.π F e).app V x),
        LinearMap.mem_range.2 ⟨(CategoryTheory.Limits.biproduct.π F e).app V x, rfl⟩, ?_⟩)
    rw [LinearMap.lsmul_apply, hcomp]
  · refine iSup_le fun e => Submodule.map_le_iff_le_comap.2 ?_
    rintro _ ⟨y, rfl⟩
    refine Submodule.mem_comap.2 (LinearMap.mem_range.2
      ⟨(CategoryTheory.Limits.factorThruImage g).app V ((CategoryTheory.Limits.biproduct.ι F e).app V y), ?_⟩)
    rw [AlgebraicGeometry.Scheme.Modules.Hom.appLin_apply, ← hfac, LinearMap.lsmul_apply,
      AlgebraicGeometry.Scheme.Modules.Hom.appLin_apply, hcomp]

end AlgebraicGeometry.Scheme.GradedQCAlgebra

/-! ## §5 Pure algebra: the weighted polynomial Rees algebra -/

namespace MvPolynomial

variable {σ : Type*} {B : Type*} [CommRing B]

/-- The Rees rescaling `y_s ↦ t^{w s - 1} · x_s` of the weighted polynomial algebra over `B` (`t` plays the role of `λ`). -/
noncomputable def reesRescale (t : B) (w : σ → ℕ) : MvPolynomial σ B →ₐ[B] MvPolynomial σ B :=
  MvPolynomial.aeval fun s => MvPolynomial.C t ^ (w s - 1) * MvPolynomial.X s

/-- Monomials `x^α` of weighted degree `j` and ordinary degree `≥ p` (a `B`-basis of `(𝒜₊^p)_j` when all `w s ≥ 1`). -/
def reesMonomials (w : σ → ℕ) (p j : ℕ) : Set (MvPolynomial σ B) :=
  {q | ∃ α : σ →₀ ℕ, Finsupp.weight w α = j ∧ p ≤ α.degree ∧ q = MvPolynomial.monomial α 1}

/-- The weight-`j` Rees piece `Σ_{e ≤ j} t^e · span (reesMonomials w (j - e) j) ⊆ B[x_s]` (the ring-level `R_j`). -/
def reesSpan (t : B) (w : σ → ℕ) (j : ℕ) : Submodule B (MvPolynomial σ B) :=
  ⨆ e : Fin (j + 1),
    (Submodule.span B (reesMonomials (B := B) w (j - e.1) j)).map (LinearMap.mulLeft B (MvPolynomial.C t ^ e.1))

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ### Arithmetic of weights -/

theorem weight_sub_one_add_degree (w : σ → ℕ) (hw : ∀ s, 0 < w s) (α : σ →₀ ℕ) :
    Finsupp.weight (fun s => w s - 1) α + α.degree = Finsupp.weight w α := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨k, hk⟩ : ∃ k, w i = k + 1 := ⟨w i - 1, by have := hw i; omega⟩
  rw [hk, Nat.add_sub_cancel]
  ring

theorem degree_le_weight_of_pos (w : σ → ℕ) (hw : ∀ s, 0 < w s) (α : σ →₀ ℕ) :
    α.degree ≤ Finsupp.weight w α := by
  have := weight_sub_one_add_degree w hw α; omega

theorem weight_sub_one_eq (w : σ → ℕ) (hw : ∀ s, 0 < w s) (α : σ →₀ ℕ) :
    Finsupp.weight (fun s => w s - 1) α = Finsupp.weight w α - α.degree := by
  have := weight_sub_one_add_degree w hw α; omega

/-! ### `reesRescale` on monomials -/

theorem reesRescale_monomial (t : B) (w : σ → ℕ) (α : σ →₀ ℕ) (c : B) :
    reesRescale t w (monomial α c) = monomial α (c * t ^ Finsupp.weight (fun s => w s - 1) α) := by
  classical
  unfold reesRescale
  rw [aeval_monomial, algebraMap_eq, ← C_mul_monomial]
  congr 1
  rw [monomial_eq]
  simp_rw [mul_pow, ← pow_mul]
  rw [Finsupp.prod_mul]
  congr 1
  rw [map_pow, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum, Finset.prod_pow_eq_pow_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, mul_comm]

theorem coeff_reesRescale (t : B) (w : σ → ℕ) (q : MvPolynomial σ B) (α : σ →₀ ℕ) :
    coeff α (reesRescale t w q) = coeff α q * t ^ Finsupp.weight (fun s => w s - 1) α := by
  classical
  induction q using MvPolynomial.induction_on' with
  | monomial β c =>
    rw [reesRescale_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; rfl
    · simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, add_mul]

/-- **The Rees rescaling is injective when `t` is a nonzerodivisor.** `reesRescale t w (monomial α c) =
c · t^{Σ_s α_s (w s - 1)} · monomial α 1` (`aeval_monomial`, `Finsupp.prod`), so distinct monomials go to `B`-multiples of
distinct monomials with regular coefficients (`IsRegular.pow`, `mem_nonZeroDivisors_iff`); compare coefficients
(`coeff_monomial`, `coeff_C_mul`). -/
theorem reesRescale_injective (t : B) (ht : t ∈ nonZeroDivisors B) (w : σ → ℕ) :
    Function.Injective (reesRescale t w) := by
  refine (injective_iff_map_eq_zero _).2 fun q hq => ?_
  ext α
  have h := congrArg (coeff α) hq
  rw [coeff_reesRescale, coeff_zero] at h
  rw [coeff_zero]
  exact (mem_nonZeroDivisors_iff.1 (pow_mem ht _)).2 _ h

theorem monomial_mem_span_reesMonomials (w : σ → ℕ) {p j : ℕ} {α : σ →₀ ℕ} (hwα : Finsupp.weight w α = j)
    (hdeg : p ≤ α.degree) (c : B) :
    monomial α c ∈ Submodule.span B (reesMonomials (B := B) w p j) := by
  have := Submodule.smul_mem (Submodule.span B (reesMonomials (B := B) w p j)) c
    (Submodule.subset_span ⟨α, hwα, hdeg, rfl⟩)
  rwa [smul_monomial, smul_eq_mul, mul_one] at this

/-- **The rescaling maps the weight-`j` part into the Rees piece**: for a monomial `x^α` of weight `j` (`w s ≥ 1`),
`reesRescale (x^α) = t^{j - |α|} x^α` (`Σ_s α_s (w s - 1) = |α|_w - |α| = j - |α|`, using `|α| ≤ |α|_w`), which lies in the
`e = j - |α|` summand of `reesSpan t w j` (`|α| ≥ j - e`). Extend by linearity (`IsWeightedHomogeneous.induction_on`). -/
theorem reesRescale_mem_reesSpan (t : B) (w : σ → ℕ) (hw : ∀ s, 0 < w s) {j : ℕ} {q : MvPolynomial σ B}
    (hq : q.IsWeightedHomogeneous w j) : reesRescale t w q ∈ reesSpan t w j := by
  classical
  rw [q.as_sum, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  have hwα : Finsupp.weight w α = j := hq (mem_support_iff.1 hα)
  have hdeg : α.degree ≤ j := hwα ▸ degree_le_weight_of_pos w hw α
  rw [reesRescale_monomial, weight_sub_one_eq w hw, hwα]
  refine Submodule.mem_iSup_of_mem ⟨j - α.degree, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ ?_
  refine Submodule.mem_map.2 ⟨monomial α (coeff α q),
    monomial_mem_span_reesMonomials w hwα (le_of_eq (Nat.sub_sub_self hdeg)) _, ?_⟩
  rw [LinearMap.mulLeft_apply, ← map_pow, C_mul_monomial, mul_comm]

/-- **The rescaling maps the weight-`j` part onto the Rees piece**: a generator `t^e · x^α` of `reesSpan t w j`
(`|α|_w = j`, `|α| ≥ j - e`) equals `t^{e - (j - |α|)} · reesRescale (x^α)` = `reesRescale (t^{e-(j-|α|)} x^α)`
(`reesRescale` is `B`-linear and `C t` is a constant), with `t^{e-(j-|α|)} x^α` weighted-homogeneous of weight `j`;
close under sums (`Submodule.iSup_induction`, `Submodule.span_induction`). -/
theorem exists_isWeightedHomogeneous_reesRescale_eq (t : B) (w : σ → ℕ) (hw : ∀ s, 0 < w s) {j : ℕ}
    {q : MvPolynomial σ B} (hq : q ∈ reesSpan t w j) :
    ∃ p : MvPolynomial σ B, p.IsWeightedHomogeneous w j ∧ reesRescale t w p = q := by
  classical
  have hle : reesSpan t w j ≤
      (weightedHomogeneousSubmodule B w j).map (reesRescale t w).toLinearMap := by
    refine iSup_le fun e => ?_
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    rintro _ ⟨α, hwα, hdeg, rfl⟩
    have hdeg' : α.degree ≤ j := hwα ▸ degree_le_weight_of_pos w hw α
    refine Submodule.mem_comap.2 (Submodule.mem_map.2
      ⟨monomial α (t ^ (e.1 - (j - α.degree))), isWeightedHomogeneous_monomial _ _ _ hwα, ?_⟩)
    rw [AlgHom.toLinearMap_apply, reesRescale_monomial, LinearMap.mulLeft_apply, ← map_pow, C_mul_monomial,
      mul_one, weight_sub_one_eq w hw, hwα, ← pow_add]
    congr 2
    have := e.2
    omega
  obtain ⟨p, hp, hpq⟩ := Submodule.mem_map.1 (hle hq)
  exact ⟨p, hp, hpq⟩

/-! ### The irrelevant ideal of the weighted grading and its powers -/

theorem irrelevant_weightedHomogeneousSubmodule (w : σ → ℕ) (hw : ∀ s, 0 < w s) :
    ReesAlgebra.irrelevant (weightedHomogeneousSubmodule B w) =
      Ideal.span (Set.range (X : σ → MvPolynomial σ B)) := by
  classical
  apply le_antisymm
  · refine (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr fun i hi a ha => ?_
    have ha' : a ∈ weightedHomogeneousSubmodule B w i := ha
    show a ∈ Ideal.span (Set.range (X : σ → MvPolynomial σ B))
    rw [← Set.image_univ, mem_ideal_span_X_image]
    intro m hm
    have hwm : Finsupp.weight w m = i := ha' (mem_support_iff.1 hm)
    by_contra h
    push Not at h
    have hm0 : m = 0 := Finsupp.ext fun s => h s (Set.mem_univ _)
    subst hm0
    rw [map_zero] at hwm
    omega
  · rw [Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    exact HomogeneousIdeal.mem_irrelevant_of_mem _ (hw s) (isWeightedHomogeneous_X B w s)

theorem mem_irrelevant_weightedHomogeneousSubmodule_iff (w : σ → ℕ) (hw : ∀ s, 0 < w s) {x : MvPolynomial σ B} :
    x ∈ ReesAlgebra.irrelevant (weightedHomogeneousSubmodule B w) ↔ ∀ m ∈ x.support, m ≠ 0 := by
  rw [irrelevant_weightedHomogeneousSubmodule w hw, ← Set.image_univ, mem_ideal_span_X_image]
  refine forall₂_congr fun m _ => ?_
  constructor
  · rintro ⟨i, -, hi⟩ h0
    exact hi (by simp [h0])
  · intro h
    obtain ⟨i, hi⟩ := DFunLike.ne_iff.1 h
    exact ⟨i, Set.mem_univ _, hi⟩

theorem degree_le_of_mem_irrelevant_pow (w : σ → ℕ) (hw : ∀ s, 0 < w s) {p : ℕ} {x : MvPolynomial σ B}
    (hx : x ∈ (ReesAlgebra.irrelevant (weightedHomogeneousSubmodule B w)) ^ p) :
    ∀ m ∈ x.support, p ≤ m.degree := by
  classical
  refine Submodule.pow_induction_on_left' (ReesAlgebra.irrelevant (weightedHomogeneousSubmodule B w))
    (C := fun n x _ => ∀ m ∈ x.support, n ≤ m.degree) ?_ ?_ ?_ hx
  · intro r m _; exact Nat.zero_le _
  · intro x y i _ _ hx hy m hm
    rcases Finset.mem_union.1 (support_add hm) with h | h
    exacts [hx m h, hy m h]
  · intro a ha i x _ hx m hm
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.1 (support_mul a x hm)
    have h1 : m₁ ≠ 0 := (mem_irrelevant_weightedHomogeneousSubmodule_iff w hw).1 ha m₁ hm₁
    have h2 := hx m₂ hm₂
    have h3 : 0 < m₁.degree := Nat.pos_of_ne_zero fun h => h1 ((Finsupp.degree_eq_zero_iff _).1 h)
    rw [map_add]
    omega

theorem monomial_mem_irrelevant_pow (w : σ → ℕ) (hw : ∀ s, 0 < w s) (c : B) :
    ∀ (p : ℕ) (α : σ →₀ ℕ), p ≤ α.degree →
      monomial α c ∈ (ReesAlgebra.irrelevant (weightedHomogeneousSubmodule B w)) ^ p
  | 0, α, _ => by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  | p + 1, α, h => by
    classical
    have hne : α ≠ 0 := fun h0 => by subst h0; simp at h
    obtain ⟨s, hs⟩ := DFunLike.ne_iff.1 hne
    have hle : Finsupp.single s 1 ≤ α :=
      Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (by simpa using hs))
    have hα : α = Finsupp.single s 1 + (α - Finsupp.single s 1) := (add_tsub_cancel_of_le hle).symm
    have hdeg : p ≤ (α - Finsupp.single s 1).degree := by
      have := congrArg Finsupp.degree hα
      rw [map_add, Finsupp.degree_single] at this
      omega
    rw [hα, monomial_single_add, pow_one, pow_succ']
    exact Ideal.mul_mem_mul
      (HomogeneousIdeal.mem_irrelevant_of_mem _ (hw s) (isWeightedHomogeneous_X B w s))
      (monomial_mem_irrelevant_pow w hw c p _ hdeg)

/-- **In `B[x_s]` with weights `w s ≥ 1`, the weight-`j` part of the `p`-th power of the irrelevant ideal is spanned by
the monomials of weight `j` and degree `≥ p`.** Pure algebra.

Proof: `𝒜₊` (`HomogeneousIdeal.irrelevant` of the weighted grading) is the span of the monomials of positive weight,
i.e. (all `w s ≥ 1`) of the non-constant monomials `x^α`, `α ≠ 0`, i.e. `𝒜₊ = (x_s)_s`. Hence `𝒜₊^p` is spanned by the
monomials of degree `≥ p` (`Ideal.span_pow`/`Submodule.span_mul_span`: a product of `p` non-constant monomials has
degree `≥ p`, and every monomial of degree `≥ p` is such a product; `Finsupp.degree`), and intersecting with
`𝒜_j = weightedHomogeneousSubmodule j` (spanned by the monomials of weight `j`) keeps exactly `reesMonomials w p j`.
Edge cases: `p = 0` (`irrPow_zero`, all monomials of weight `j`); `σ` empty (`j = 0`, `p = 0`: `B`; else `0`). -/
theorem irrPow_weightedHomogeneousSubmodule_eq_span (w : σ → ℕ) (hw : ∀ s, 0 < w s) (p j : ℕ) :
    ReesAlgebra.irrPow (MvPolynomial.weightedHomogeneousSubmodule B w) p j =
      Submodule.span B (reesMonomials (B := B) w p j) := by
  classical
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2⟩ := (ReesAlgebra.mem_irrPow _).1 hx
    rw [x.as_sum]
    refine Submodule.sum_mem _ fun α hα => ?_
    exact monomial_mem_span_reesMonomials w (hx2 (mem_support_iff.1 hα))
      (degree_le_of_mem_irrelevant_pow w hw hx1 α hα) _
  · rw [Submodule.span_le]
    rintro _ ⟨α, hwα, hdeg, rfl⟩
    exact (ReesAlgebra.mem_irrPow _).2
      ⟨monomial_mem_irrelevant_pow w hw 1 p α hdeg, isWeightedHomogeneous_monomial _ _ _ hwα⟩

/-! ### Further facts on `reesRescale` needed by the assembly (§6) -/

/-- `reesRescale` fixes constants (`aeval_C`). -/
theorem reesRescale_C (t : B) (w : σ → ℕ) (r : B) : reesRescale t w (C r) = C r := by
  unfold reesRescale
  rw [aeval_C, algebraMap_eq]

/-- `reesRescale` preserves weighted homogeneity (`coeff_reesRescale`: it only rescales coefficients). -/
theorem reesRescale_isWeightedHomogeneous (t : B) (w : σ → ℕ) {m : ℕ} {p : MvPolynomial σ B}
    (hp : p.IsWeightedHomogeneous w m) : (reesRescale t w p).IsWeightedHomogeneous w m := by
  intro d hd
  rw [coeff_reesRescale] at hd
  exact hp (left_ne_zero_of_mul hd)

/-- **(a6.v) The image of `reesRescale` is `⊕_j reesSpan t w j`** (from (a6.iii) and (a6.iv), summing over the weights). -/
theorem range_reesRescale_toLinearMap (t : B) (w : σ → ℕ) (hw : ∀ s, 0 < w s) :
    LinearMap.range (reesRescale t w).toLinearMap = ⨆ j, reesSpan t w j := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    rw [AlgHom.toLinearMap_apply]
    induction p using MvPolynomial.induction_on' with
    | monomial α c =>
      exact Submodule.mem_iSup_of_mem (Finsupp.weight w α)
        (reesRescale_mem_reesSpan t w hw (isWeightedHomogeneous_monomial _ _ _ rfl))
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
  · refine iSup_le fun j q hq => ?_
    obtain ⟨p, -, hpq⟩ := exists_isWeightedHomogeneous_reesRescale_eq t w hw hq
    exact ⟨p, hpq⟩

/-- `reesMonomials` is stable under base change of coefficients. -/
theorem map_image_reesMonomials {B' : Type*} [CommRing B'] (f : B →+* B') (w : σ → ℕ) (p j : ℕ) :
    MvPolynomial.map f '' reesMonomials (B := B) w p j = reesMonomials (B := B') w p j := by
  ext q
  constructor
  · rintro ⟨_, ⟨α, hα, hd, rfl⟩, rfl⟩
    exact ⟨α, hα, hd, by rw [map_monomial, map_one]⟩
  · rintro ⟨α, hα, hd, rfl⟩
    exact ⟨monomial α 1, ⟨α, hα, hd, rfl⟩, by rw [map_monomial, map_one]⟩

end MvPolynomial

/-! ## §6 Assembly

Notation (fixed for this section): `π := toBase X : 𝔸¹_X → X`, `T := S.pullback π`, `R := S.reesDeformation`,
`𝒜` a weighted polynomial atlas of `S` with charts `U_i`, `V_i := π⁻¹U_i` (affine), `Γ_i := Γ(𝔸¹_X, V_i)`,
`λ_i := lambdaRes V_i`, `Ψ_i := pullbackAtlasEquiv : T(V_i) ≃+* Γ_i[x_s]` (Stacks 01I9),
`ι := (inclHom S).sectionsRingHom V_i : R(V_i) →+* T(V_i)` (injective), `Θ_i := Ψ_i ∘ ι` and `Φ_i := reesRescale λ_i w`. -/

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

open scoped TensorProduct

attribute [local instance] MvPolynomial.weightedGradedAlgebra

section Chart

variable {X V : AlgebraicGeometry.Scheme.{u}} (g : V ⟶ X) (S : X.GradedQCAlgebra)
variable {σ : Type u} {w : σ → ℕ} (𝒜 : S.toGradedAffineAlgebra.WeightedPolynomialAtlas w) (i : 𝒜.I)
variable (W' : V.AffineZariskiSite) (hW : W'.toOpens ≤ g ⁻¹ᵁ (𝒜.chart i).toOpens)
variable (hΨ : letI := pullbackBaseAlgebra g (𝒜.chart i) W' hW
  letI := S.pullbackSectionsAlgebra g (𝒜.chart i) W' hW
  Function.Bijective (S.pullbackTensorAlgHom g (𝒜.chart i) W' hW))

/-- **The chart isomorphism of `g^*S` on pulled-back sections**: `Ψ (of_m ((g^*s)|_W)) = map g^♯ (φ_i (of_m s))`
(`Ψ⁻¹` inverts `pullbackTensorAlgHom`, which sends `1 ⊗ a` to `Φ a`; then `algebraTensorAlgEquiv_tmul`). -/
theorem pullbackAtlasEquiv_ofPiece_pullbackPiece (m : ℕ) (s : S.sectionsPiece (𝒜.chart i).toOpens m) :
    S.pullbackAtlasEquiv g 𝒜 i W' hW hΨ
        ((S.pullback g).ofPiece W'.toOpens m (S.pullbackPiece g (𝒜.chart i).toOpens W'.toOpens hW m s)) =
      MvPolynomial.map (g.appLE (𝒜.chart i).toOpens W'.toOpens hW).hom (𝒜.equiv i (S.ofPiece (𝒜.chart i).toOpens m s)) := by
  let _ := pullbackBaseAlgebra g (𝒜.chart i) W' hW
  let _ := S.pullbackSectionsAlgebra g (𝒜.chart i) W' hW
  have h1 : (S.pullback g).ofPiece W'.toOpens m (S.pullbackPiece g (𝒜.chart i).toOpens W'.toOpens hW m s) =
      S.pullbackTensorAlgHom g (𝒜.chart i) W' hW ((1 : Γ(V, W'.toOpens)) ⊗ₜ S.ofPiece (𝒜.chart i).toOpens m s) :=
    (S.pullbackSectionsRingHom_ofPiece g _ _ hW m s).symm.trans
      ((one_smul Γ(V, W'.toOpens) (S.pullbackSectionsAlgHom g (𝒜.chart i) W' hW
        (S.ofPiece (𝒜.chart i).toOpens m s))).symm.trans
          (S.pullbackTensorAlgHom_tmul g (𝒜.chart i) W' hW 1 (S.ofPiece (𝒜.chart i).toOpens m s)).symm)
  have key : ∀ t, S.pullbackAtlasEquiv g 𝒜 i W' hW hΨ (S.pullbackTensorAlgHom g (𝒜.chart i) W' hW t) =
      MvPolynomial.algebraTensorAlgEquiv Γ(X, (𝒜.chart i).toOpens) Γ(V, W'.toOpens)
        (Algebra.TensorProduct.congr AlgEquiv.refl (𝒜.algEquiv i) t) := fun t => by
    show MvPolynomial.algebraTensorAlgEquiv Γ(X, (𝒜.chart i).toOpens) Γ(V, W'.toOpens)
      (Algebra.TensorProduct.congr AlgEquiv.refl (𝒜.algEquiv i)
        ((AlgEquiv.ofBijective _ hΨ).symm ((AlgEquiv.ofBijective _ hΨ) t))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [h1, key, Algebra.TensorProduct.congr_apply]
  erw [Algebra.TensorProduct.map_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul]
  rw [map_one, one_smul]
  rfl

/-- `Γ(W, (g^*S)_m) → Γ(W)[x_s]`, `z ↦ Ψ (of_m z)`, as a `Γ(W)`-linear map (`Ψ` sends the structure map to `C`, and
`unit r · of_m z = of_m (r • z)`). -/
def pullbackAtlasPieceLin (m : ℕ) :
    Γ((S.pullback g).part m, W'.toOpens) →ₗ[Γ(V, W'.toOpens)] MvPolynomial σ Γ(V, W'.toOpens) where
  toFun z := S.pullbackAtlasEquiv g 𝒜 i W' hW hΨ ((S.pullback g).ofPiece W'.toOpens m z)
  map_add' z z' := by
    have h0 : (S.pullback g).ofPiece W'.toOpens m (z + z') =
        (S.pullback g).ofPiece W'.toOpens m z + (S.pullback g).ofPiece W'.toOpens m z' :=
      map_add (DirectSum.of ((S.pullback g).sectionsPiece W'.toOpens) m) z z'
    exact (congrArg (S.pullbackAtlasEquiv g 𝒜 i W' hW hΨ) h0).trans
      (map_add (S.pullbackAtlasEquiv g 𝒜 i W' hW hΨ) _ _)
  map_smul' r z := by
    have h1 := (S.pullback g).sectionsUnitHom_mul_ofPiece W'.toOpens r z
    have h2 : S.pullbackAtlasEquiv g 𝒜 i W' hW hΨ ((S.pullback g).sectionsUnitHom W'.toOpens r) = MvPolynomial.C r :=
      S.pullbackAtlasEquiv_unitHom g 𝒜 i W' hW hΨ r
    simp only [RingHom.id_apply]
    refine (congrArg (S.pullbackAtlasEquiv g 𝒜 i W' hW hΨ) h1.symm).trans ?_
    refine (map_mul (S.pullbackAtlasEquiv g 𝒜 i W' hW hΨ) _ _).trans ?_
    rw [h2, ← MvPolynomial.smul_eq_C_mul]

theorem pullbackAtlasPieceLin_apply (m : ℕ) (z : Γ((S.pullback g).part m, W'.toOpens)) :
    S.pullbackAtlasPieceLin g 𝒜 i W' hW hΨ m z =
      S.pullbackAtlasEquiv g 𝒜 i W' hW hΨ ((S.pullback g).ofPiece W'.toOpens m z) := rfl

/-- **Transport of (a6.i) along the chart isomorphism**: `x ∈ (S(U)_+)^p ∩ S(U)_j ↔ φ_i x ∈ (Γ(U)[x_s]_+)^p ∩ (Γ(U)[x_s])_j`
(`ReesAlgebra.map_mem_irrPow` for `φ_i` and `φ_i⁻¹`, both graded by `equiv_grading`). -/
theorem mem_irrPow_iff_equiv_mem (p j : ℕ) (x : S.toGradedAffineAlgebra.toAffineAlgebra.sections (𝒜.chart i)) :
    x ∈ ReesAlgebra.irrPow (S.toGradedAffineAlgebra.gradingSubmodule (𝒜.chart i)) p j ↔
      𝒜.equiv i x ∈ ReesAlgebra.irrPow (MvPolynomial.weightedHomogeneousSubmodule Γ(X, (𝒜.chart i).toOpens) w) p j := by
  constructor
  · intro hx
    exact ReesAlgebra.map_mem_irrPow (S.toGradedAffineAlgebra.gradingSubmodule (𝒜.chart i))
      (MvPolynomial.weightedHomogeneousSubmodule Γ(X, (𝒜.chart i).toOpens) w) (𝒜.equiv i).toRingHom
      (fun m a ha => (𝒜.equiv_grading i m a).1 ha) hx
  · intro hx
    have := ReesAlgebra.map_mem_irrPow (MvPolynomial.weightedHomogeneousSubmodule Γ(X, (𝒜.chart i).toOpens) w)
      (S.toGradedAffineAlgebra.gradingSubmodule (𝒜.chart i)) (𝒜.equiv i).symm.toRingHom
      (fun m a ha => 𝒜.symm_mem i ha) hx
    rwa [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at this

/-- **(a4) + (a6.i) in image form**: the image of `Γ(U_i, I^{(p)}_j) → Γ(U_i, S_j)` corresponds under `φ_i ∘ of_j` exactly to
`(Γ(U_i)[x_s]_+)^p ∩ (Γ(U_i)[x_s])_j = span (reesMonomials w p j)`. -/
theorem image_equiv_ofPiece_range_irrelevantPow (hw : ∀ s, 0 < w s) (p j : ℕ) :
    (fun x => 𝒜.equiv i (S.ofPiece (𝒜.chart i).toOpens j x)) '' Set.range ((S.irrelevantPow p j).2.app (𝒜.chart i).toOpens) =
      (Submodule.span Γ(X, (𝒜.chart i).toOpens) (MvPolynomial.reesMonomials (B := Γ(X, (𝒜.chart i).toOpens)) w p j) :
        Set (MvPolynomial σ Γ(X, (𝒜.chart i).toOpens))) := by
  rw [← MvPolynomial.irrPow_weightedHomogeneousSubmodule_eq_span w hw p j]
  ext y
  constructor
  · rintro ⟨x, ⟨t, rfl⟩, rfl⟩
    exact (S.mem_irrPow_iff_equiv_mem 𝒜 i p j _).1 (S.ofPiece_irrelevantPow_app_mem_irrPow (𝒜.chart i) p j t)
  · intro hy
    have hx : (𝒜.equiv i).symm y ∈ ReesAlgebra.irrPow (S.toGradedAffineAlgebra.gradingSubmodule (𝒜.chart i)) p j :=
      (S.mem_irrPow_iff_equiv_mem 𝒜 i p j _).2 (by rwa [RingEquiv.apply_symm_apply])
    obtain ⟨x', hx'⟩ := hx.2
    have hx'' : S.ofPiece (𝒜.chart i).toOpens j x' = (𝒜.equiv i).symm y := hx'
    have hmem : (S.ofPiece (𝒜.chart i).toOpens j x' : S.toGradedAffineAlgebra.toAffineAlgebra.sections (𝒜.chart i)) ∈
        ReesAlgebra.irrPow (S.toGradedAffineAlgebra.gradingSubmodule (𝒜.chart i)) p j := by
      rw [hx'']; exact hx
    obtain ⟨t, ht⟩ := S.exists_irrelevantPow_app_eq_of_mem_irrPow (𝒜.chart i) p j x' hmem
    refine ⟨x', ⟨t, ht⟩, ?_⟩
    show 𝒜.equiv i (S.ofPiece (𝒜.chart i).toOpens j x') = y
    rw [hx'', RingEquiv.apply_symm_apply]

/-- **(C) The image of `Γ(W, g^*I^{(p)}_j) → Γ(W, (g^*S)_j)` under `L_j = Ψ ∘ of_j` is `span_{Γ(W)} (reesMonomials w p j)`**
(01I9 span form + naturality, then (a4) + (a6.i) transported along `φ_i`, then base change of the span along `g^♯`). -/
theorem map_pullbackAtlasPieceLin_range_pullback_map (hw : ∀ s, 0 < w s) (p j : ℕ) :
    (LinearMap.range (AlgebraicGeometry.Scheme.Modules.Hom.appLinearMap (N := (S.pullback g).part j)
        ((AlgebraicGeometry.Scheme.Modules.pullback g).map (S.irrelevantPow p j).2) W'.toOpens)).map
        (S.pullbackAtlasPieceLin g 𝒜 i W' hW hΨ j) =
      Submodule.span Γ(V, W'.toOpens) (MvPolynomial.reesMonomials (B := Γ(V, W'.toOpens)) w p j) := by
  have hqc := S.irrelevantPow_isQuasicoherent p j
  have hR : LinearMap.range (AlgebraicGeometry.Scheme.Modules.Hom.appLinearMap (N := (S.pullback g).part j)
      ((AlgebraicGeometry.Scheme.Modules.pullback g).map (S.irrelevantPow p j).2) W'.toOpens) =
      Submodule.span Γ(V, W'.toOpens) (Set.image (β := Γ((S.pullback g).part j, W'.toOpens))
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn g (S.part j) (𝒜.chart i).toOpens W'.toOpens hW)
        (Set.range ((S.irrelevantPow p j).2.app (𝒜.chart i).toOpens))) :=
    AlgebraicGeometry.Scheme.Modules.range_pullback_map_appLinearMap_eq_span g (S.irrelevantPow p j).2
      (U := (𝒜.chart i).toOpens) (𝒜.chart i).2 (V := W'.toOpens) W'.2 hW
  rw [hR, Submodule.map_span]
  have hset : S.pullbackAtlasPieceLin g 𝒜 i W' hW hΨ j '' Set.image (β := Γ((S.pullback g).part j, W'.toOpens))
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn g (S.part j) (𝒜.chart i).toOpens W'.toOpens hW)
        (Set.range ((S.irrelevantPow p j).2.app (𝒜.chart i).toOpens)) =
      MvPolynomial.map (g.appLE (𝒜.chart i).toOpens W'.toOpens hW).hom ''
        ((fun x => 𝒜.equiv i (S.ofPiece (𝒜.chart i).toOpens j x)) ''
          Set.range ((S.irrelevantPow p j).2.app (𝒜.chart i).toOpens)) := by
    ext q
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, (S.pullbackAtlasEquiv_ofPiece_pullbackPiece g 𝒜 i W' hW hΨ j x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, S.pullbackAtlasEquiv_ofPiece_pullbackPiece g 𝒜 i W' hW hΨ j x⟩
  rw [hset, S.image_equiv_ofPiece_range_irrelevantPow 𝒜 i hw p j, MvPolynomial.span_map_image_span,
    MvPolynomial.map_image_reesMonomials]

end Chart

/-! ### The charts `V_i = π⁻¹U_i` of the Rees deformation -/

section Rees

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)
variable {σ : Type u} {w : σ → ℕ} (𝒜 : S.toGradedAffineAlgebra.WeightedPolynomialAtlas w) (i : 𝒜.I)

/-- The chart `V_i := π⁻¹(U_i) ⊆ A¹_X` over the chart `U_i` of `𝒜` (affine by (a1)). -/
def reesChart : (AlgebraicGeometry.Scheme.affineLineOver X).AffineZariskiSite :=
  ⟨AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ (𝒜.chart i).toOpens,
    AlgebraicGeometry.Scheme.affineLineOver.isAffineOpen_preimage_toBase (𝒜.chart i).2⟩

/-- `Ψ_i : (π^*S)(V_i) ≃+* Γ_i[x_s]` (the chart isomorphism of the pullback, Stacks 01I9). -/
def reesChartPullbackEquiv :
    (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).toGradedAffineAlgebra.toAffineAlgebra.sections
        (S.reesChart 𝒜 i) ≃+*
      MvPolynomial σ Γ(AlgebraicGeometry.Scheme.affineLineOver X, (S.reesChart 𝒜 i).toOpens) :=
  S.pullbackAtlasEquiv (AlgebraicGeometry.Scheme.affineLineOver.toBase X) 𝒜 i (S.reesChart 𝒜 i) le_rfl
    (S.pullbackTensorAlgHom_bijective (AlgebraicGeometry.Scheme.affineLineOver.toBase X) (𝒜.chart i)
      (S.reesChart 𝒜 i) le_rfl)

set_option backward.isDefEq.respectTransparency false in
/-- A monomorphism of sheaves of modules is injective on sections (evaluation preserves monomorphisms; local copy of
`injective_app_of_mono` from `Stacks0806_ReesLiftMaps.lean`, including that file's `set_option` — `X.Modules` is a `def`
wrapping `SheafOfModules`, so the `Mono` instance is only found with transparency relaxed). -/
private theorem injective_app_of_mono_lwp {Y : AlgebraicGeometry.Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N) [Mono φ]
    (W : Y.Opens) : Function.Injective (φ.app W) := by
  have : Mono ((SheafOfModules.evaluation Y.ringCatSheaf (op W)).map φ) :=
    (SheafOfModules.evaluation Y.ringCatSheaf (op W)).map_mono φ
  exact (ModuleCat.mono_iff_injective _).mp this

/-- `ι : R(V_i) →+* (π^*S)(V_i)`, induced by the graded morphism `inclHom S : R ⟶ π^*S`. -/
abbrev reesInclRingHom :
    S.reesDeformation.sectionsRing (S.reesChart 𝒜 i).toOpens →+*
      (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).sectionsRing (S.reesChart 𝒜 i).toOpens :=
  (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.inclHom S).sectionsRingHom (S.reesChart 𝒜 i).toOpens

/-- `ι` is injective (each `incl S j = image.ι _` is a monomorphism). -/
theorem reesInclRingHom_injective : Function.Injective (S.reesInclRingHom 𝒜 i) :=
  Hom.sectionsRingHom_injective _ _ fun m => injective_app_of_mono_lwp
    (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S m) _

/-- `Θ_i := Ψ_i ∘ ι : R(V_i) →ₐ[Γ_i] Γ_i[x_s]` (a `Γ_i`-algebra map: `ι` and `Ψ_i` respect the structure maps). -/
def reesChartAlgHom :
    S.reesDeformation.toGradedAffineAlgebra.toAffineAlgebra.sections (S.reesChart 𝒜 i)
      →ₐ[Γ(AlgebraicGeometry.Scheme.affineLineOver X, (S.reesChart 𝒜 i).toOpens)]
        MvPolynomial σ Γ(AlgebraicGeometry.Scheme.affineLineOver X, (S.reesChart 𝒜 i).toOpens) where
  toRingHom := (S.reesChartPullbackEquiv 𝒜 i).toRingHom.comp (S.reesInclRingHom 𝒜 i)
  commutes' r := by
    show S.reesChartPullbackEquiv 𝒜 i (S.reesInclRingHom 𝒜 i
      (S.reesDeformation.sectionsUnitHom (S.reesChart 𝒜 i).toOpens r)) = MvPolynomial.C r
    rw [Hom.sectionsRingHom_sectionsUnitHom]
    exact S.pullbackAtlasEquiv_unitHom _ 𝒜 i (S.reesChart 𝒜 i) le_rfl _ r

theorem reesChartAlgHom_apply (a : S.reesDeformation.toGradedAffineAlgebra.toAffineAlgebra.sections (S.reesChart 𝒜 i)) :
    S.reesChartAlgHom 𝒜 i a = S.reesChartPullbackEquiv 𝒜 i (S.reesInclRingHom 𝒜 i a) := rfl

theorem reesChartAlgHom_injective : Function.Injective (S.reesChartAlgHom 𝒜 i) :=
  (S.reesChartPullbackEquiv 𝒜 i).injective.comp (S.reesInclRingHom_injective 𝒜 i)

/-- `Θ_i (of_j y) = L_j (incl_j y)`. -/
theorem reesChartAlgHom_ofPiece (j : ℕ) (y : Γ(S.reesDeformation.part j, (S.reesChart 𝒜 i).toOpens)) :
    S.reesChartAlgHom 𝒜 i (S.reesDeformation.ofPiece (S.reesChart 𝒜 i).toOpens j y) =
      S.pullbackAtlasPieceLin (AlgebraicGeometry.Scheme.affineLineOver.toBase X) 𝒜 i (S.reesChart 𝒜 i) le_rfl
        (S.pullbackTensorAlgHom_bijective (AlgebraicGeometry.Scheme.affineLineOver.toBase X) (𝒜.chart i)
          (S.reesChart 𝒜 i) le_rfl) j
        ((AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S j).app (S.reesChart 𝒜 i).toOpens y) := by
  exact congrArg (S.reesChartPullbackEquiv 𝒜 i)
    ((AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.inclHom S).sectionsRingHom_ofPiece _ j y)

/-- **(B) The degree-`j` part of the image of `R(V_i)` in `Γ_i[x_s]` is `reesSpan λ_i w j`**: by (a5) the image of `R_j(V_i)`
in `Γ(V_i, π^*S_j)` is `Σ_e λ_i^e · Im Γ(V_i, π^*ι_{j-e})`, and (C) identifies each `L_j (Im Γ(V_i, π^*ι_p))` with
`span (reesMonomials w p j)`; `L_j` turns `λ_i^e •` into `(C λ_i)^e ·`. -/
theorem map_pullbackAtlasPieceLin_range_incl (hw : ∀ s, 0 < w s) (j : ℕ) :
    (LinearMap.range (AlgebraicGeometry.Scheme.Modules.Hom.appLin
        (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S j) (S.reesChart 𝒜 i).toOpens)).map
        (S.pullbackAtlasPieceLin (AlgebraicGeometry.Scheme.affineLineOver.toBase X) 𝒜 i (S.reesChart 𝒜 i) le_rfl
          (S.pullbackTensorAlgHom_bijective (AlgebraicGeometry.Scheme.affineLineOver.toBase X) (𝒜.chart i)
            (S.reesChart 𝒜 i) le_rfl) j) =
      MvPolynomial.reesSpan (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) w j := by
  rw [AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl_app_range_eq S (V := (S.reesChart 𝒜 i).toOpens)
    (S.reesChart 𝒜 i).2 j, Submodule.map_iSup]
  unfold MvPolynomial.reesSpan
  refine iSup_congr fun e => ?_
  rw [← Submodule.map_comp, ← S.map_pullbackAtlasPieceLin_range_pullback_map _ 𝒜 i (S.reesChart 𝒜 i) le_rfl
    (S.pullbackTensorAlgHom_bijective (AlgebraicGeometry.Scheme.affineLineOver.toBase X) (𝒜.chart i)
      (S.reesChart 𝒜 i) le_rfl) hw (j - e.1) j, ← Submodule.map_comp]
  congr 1
  ext z
  simp only [LinearMap.comp_apply, LinearMap.lsmul_apply, LinearMap.mulLeft_apply, map_smul,
    MvPolynomial.smul_eq_C_mul, map_pow]

end Rees

end AlgebraicGeometry.Scheme.GradedQCAlgebra

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- **The Rees deformation of a locally weighted-polynomial algebra is locally weighted-polynomial with the same
weights.** Source: Lemma 2.3 of the paper (the `λ`-rescaling `y_s = λ^{w s - 1} x_s`); Stacks 052P.

Proof (assembly of §0–§5). Let `𝒜 : S.toGradedAffineAlgebra.WeightedPolynomialAtlas w` (`hS`,
`isLocallyWeightedPolynomial_iff`) with charts `U_i` and ring isomorphisms `φ_i : S(U_i) ≃+* Γ(U_i)[x_s]`. Put
`π := toBase X`, `V_i := π⁻¹U_i`, affine by `isAffineOpen_preimage_toBase`, covering `𝔸¹_X`. Write `T := S.pullback π`,
`R := S.reesDeformation`, `Γ_i := Γ(𝔸¹_X, V_i)`, `λ_i := lambdaRes V_i`.
1. **Chart of `T`** (`WeightedPolynomialAtlasPullback`): `Ψ_i := S.pullbackAtlasEquiv π 𝒜 i ⟨V_i, _⟩ le_rfl hΨ :
   T(V_i) ≃+* Γ_i[x_s]`, with `hΨ := S.pullbackTensorAlgHom_bijective …` (Stacks 01I9), satisfying
   `pullbackAtlasEquiv_grading` and `pullbackAtlasEquiv_unitHom`; a section `y ∈ Γ(V_i, π^*I^{(p)}_j)` maps under
   `Γ(V_i, pullMap ι_p)` and `Ψ_i` into the `Γ_i`-span of the monomials of weight `j` and degree `≥ p`
   (`irrelevantPow_app_range_iff` + `irrPow_weightedHomogeneousSubmodule_eq_span` transported along `φ_i`, 01I9 in span
   form `range_pullback_map_appLinearMap_eq_span`, base change of spans `span_map_image_span`).
2. **`R(V_i)` inside `T(V_i)`**: the graded morphism `inclHom S : R ⟶ T` gives an injective ring homomorphism
   `ι : R(V_i) → T(V_i)` on section rings (`DeformedJetAlgebraLWP_HomSectionsRing`), and by `incl_app_range_eq` its image
   in degree `j` is `Σ_e λ_i^e · Γ(V_i, π^*I^{(j-e)}_j)`, which under `Ψ_i` and step 1 is `reesSpan λ_i w j`
   (`map_pullbackAtlasPieceLin_range_incl`).
3. **Chart of `R`**: `Φ_i := reesRescale λ_i w : Γ_i[y_s] → Γ_i[x_s]` is injective by `lambdaRes_mem_nonZeroDivisors` and
   `reesRescale_injective`, and by `reesRescale_mem_reesSpan` / `exists_isWeightedHomogeneous_reesRescale_eq` its image
   is `⨆_j reesSpan λ_i w j` (`range_reesRescale_toLinearMap`); so `LinearMap.range Θ_i = LinearMap.range Φ_i` for
   `Θ_i := Ψ_i ∘ ι`, and `e_i := Φ_i⁻¹ ∘ Θ_i : R(V_i) ≃+* Γ_i[y_s]` (`AlgEquiv.ofInjective`, `Subalgebra.equivOfEq`).
4. **Fields**: `equiv_grading` uses `GradedRingHom.mem_iff_of_injective` twice (for `ι` and for `Φ_i`, which preserves
   weights since `λ_i` is a scalar); `equiv_unit` uses the injectivity of `Φ_i` and `reesRescale_C`.
Edge cases: `σ` empty gives `S = O_X`, `R = O_{𝔸¹_X}`; a degree `j` with no monomials gives `R_j = 0`. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation_isLocallyWeightedPolynomial {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) {σ : Type u} [Finite σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (hS : S.IsLocallyWeightedPolynomial w hw) : S.reesDeformation.IsLocallyWeightedPolynomial w hw := by
  rw [AlgebraicGeometry.Scheme.GradedQCAlgebra.isLocallyWeightedPolynomial_iff] at hS ⊢
  obtain ⟨𝒜⟩ := hS
  classical
  -- `Φ_i := reesRescale λ_i w`, injective by (a2') and (a6.ii)
  have hΦinj : ∀ i : 𝒜.I, Function.Injective
      (MvPolynomial.reesRescale (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) w) :=
    fun i => MvPolynomial.reesRescale_injective _
      (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes_mem_nonZeroDivisors (𝒜.chart i).2) w
  -- `Θ_i := Ψ_i ∘ ι`, injective; its image is `⊕_j reesSpan λ_i w j` (by (B))
  have hΘrange : ∀ i : 𝒜.I, LinearMap.range (S.reesChartAlgHom 𝒜 i).toLinearMap =
      ⨆ j, MvPolynomial.reesSpan (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) w j := by
    intro i
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [AlgHom.toLinearMap_apply]
      suffices h : ∀ y : DirectSum ℕ (S.reesDeformation.sectionsPiece (S.reesChart 𝒜 i).toOpens),
          S.reesChartAlgHom 𝒜 i y ∈ ⨆ j, MvPolynomial.reesSpan
            (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) w j from h x
      intro y
      induction y using DirectSum.induction_on with
      | zero =>
        have h0 : S.reesChartAlgHom 𝒜 i (0 : DirectSum ℕ (S.reesDeformation.sectionsPiece (S.reesChart 𝒜 i).toOpens)) = 0 :=
          map_zero _
        rw [h0]; exact zero_mem _
      | of m a =>
        refine Submodule.mem_iSup_of_mem m ?_
        rw [← S.map_pullbackAtlasPieceLin_range_incl 𝒜 i hw m]
        exact Submodule.mem_map.2 ⟨(AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S m).app _ a,
          LinearMap.mem_range.2 ⟨a, rfl⟩, (S.reesChartAlgHom_ofPiece 𝒜 i m a).symm⟩
      | add x y hx hy =>
        have hadd : S.reesChartAlgHom 𝒜 i (x + y) = S.reesChartAlgHom 𝒜 i x + S.reesChartAlgHom 𝒜 i y :=
          map_add _ x y
        rw [hadd]; exact add_mem hx hy
    · refine iSup_le fun j => ?_
      rw [← S.map_pullbackAtlasPieceLin_range_incl 𝒜 i hw j]
      rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨S.reesDeformation.ofPiece _ j y, S.reesChartAlgHom_ofPiece 𝒜 i j y⟩
  -- the image of `Φ_i` is the same (a6.v)
  have hrange : ∀ i : 𝒜.I, (S.reesChartAlgHom 𝒜 i).range =
      (MvPolynomial.reesRescale (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) w).range :=
    fun i => by
      ext q
      rw [AlgHom.mem_range, AlgHom.mem_range]
      have h1 : q ∈ LinearMap.range (S.reesChartAlgHom 𝒜 i).toLinearMap ↔ q ∈ LinearMap.range
          (MvPolynomial.reesRescale (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) w).toLinearMap := by
        rw [hΘrange, MvPolynomial.range_reesRescale_toLinearMap _ w hw]
      simpa only [LinearMap.mem_range, AlgHom.toLinearMap_apply] using h1
  -- the chart isomorphisms `e_i := Φ_i⁻¹ ∘ Θ_i : R(V_i) ≃ₐ Γ_i[y_s]`
  let e : ∀ i : 𝒜.I, S.reesDeformation.toGradedAffineAlgebra.toAffineAlgebra.sections (S.reesChart 𝒜 i)
      ≃ₐ[Γ(AlgebraicGeometry.Scheme.affineLineOver X, (S.reesChart 𝒜 i).toOpens)]
        MvPolynomial σ Γ(AlgebraicGeometry.Scheme.affineLineOver X, (S.reesChart 𝒜 i).toOpens) := fun i =>
    (AlgEquiv.ofInjective _ (S.reesChartAlgHom_injective 𝒜 i)).trans
      ((Subalgebra.equivOfEq _ _ (hrange i)).trans (AlgEquiv.ofInjective _ (hΦinj i)).symm)
  have hΦe : ∀ (i : 𝒜.I) a,
      MvPolynomial.reesRescale (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) w (e i a) =
        S.reesChartAlgHom 𝒜 i a := fun i a =>
    congrArg Subtype.val (AlgEquiv.apply_symm_apply (AlgEquiv.ofInjective _ (hΦinj i))
      (Subalgebra.equivOfEq _ _ (hrange i) (AlgEquiv.ofInjective _ (S.reesChartAlgHom_injective 𝒜 i) a)))
  refine ⟨{ I := 𝒜.I
            chart := fun i => S.reesChart 𝒜 i
            covers := fun v => ?_
            equiv := fun i => (e i).toRingEquiv
            equiv_grading := fun i m a => ?_
            equiv_unit := fun i r => ?_ }⟩
  · -- `V_i = π⁻¹U_i` cover `A¹_X`
    obtain ⟨i, hi⟩ := 𝒜.covers ((AlgebraicGeometry.Scheme.affineLineOver.toBase X).base v)
    exact ⟨i, hi⟩
  · -- grading: `a ∈ R_m(V_i) ↔ ι a ∈ T_m(V_i) ↔ Ψ_i (ι a) weight-`m` ↔ Φ_i (e_i a) weight-`m` ↔ e_i a weight-`m``
    have h1 := GradedRingHom.mem_iff_of_injective
      ((AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.inclHom S).sectionsGradedRingHom (S.reesChart 𝒜 i).toOpens)
      (S.reesInclRingHom_injective 𝒜 i) m a
    have h2 := S.pullbackAtlasEquiv_grading (AlgebraicGeometry.Scheme.affineLineOver.toBase X) 𝒜 i (S.reesChart 𝒜 i) le_rfl
      (S.pullbackTensorAlgHom_bijective (AlgebraicGeometry.Scheme.affineLineOver.toBase X) (𝒜.chart i)
        (S.reesChart 𝒜 i) le_rfl) m (S.reesInclRingHom 𝒜 i a)
    let ΦG : MvPolynomial.weightedHomogeneousSubmodule Γ(AlgebraicGeometry.Scheme.affineLineOver X, (S.reesChart 𝒜 i).toOpens) w
        →+*ᵍ MvPolynomial.weightedHomogeneousSubmodule Γ(AlgebraicGeometry.Scheme.affineLineOver X, (S.reesChart 𝒜 i).toOpens) w :=
      { toRingHom := (MvPolynomial.reesRescale
          (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) w).toRingHom
        map_mem := fun {m} {p} hp => MvPolynomial.reesRescale_isWeightedHomogeneous _ w hp }
    have h3 := GradedRingHom.mem_iff_of_injective ΦG (hΦinj i) m (e i a)
    have h4 : MvPolynomial.reesRescale (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) w
        (e i a) = S.pullbackAtlasEquiv (AlgebraicGeometry.Scheme.affineLineOver.toBase X) 𝒜 i (S.reesChart 𝒜 i) le_rfl
          (S.pullbackTensorAlgHom_bijective (AlgebraicGeometry.Scheme.affineLineOver.toBase X) (𝒜.chart i)
            (S.reesChart 𝒜 i) le_rfl) (S.reesInclRingHom 𝒜 i a) := hΦe i a
    refine h1.trans (h2.trans ?_)
    rw [← h4]
    exact h3.symm
  · -- unit: `Φ_i (e_i (unit r)) = Θ_i (unit r) = C r = Φ_i (C r)`
    apply hΦinj i
    show MvPolynomial.reesRescale (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) w
      (e i (S.reesDeformation.toGradedAffineAlgebra.toAffineAlgebra.unitHom (S.reesChart 𝒜 i) r)) = _
    rw [hΦe, MvPolynomial.reesRescale_C]
    exact (S.reesChartAlgHom 𝒜 i).commutes r

end
