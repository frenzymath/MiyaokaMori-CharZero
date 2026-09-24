import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetRepresentableBy

/-! # Based jets of affine space

The based jets of affine space: the relative jet scheme of order `r` of `𝔸^m_U/U` with the zero
section as constant term is `J_r^0(𝔸^m_U/U) ≅ 𝔸_U^{mr}` as a scheme over `U`, the coordinates being
the coefficients `a_1, …, a_r` of each component (the chart (2.5) of §2.2 of the paper).
-/

-- `TruncatedJetRing` is `AdjoinRoot (X^(r+1))`; representatives are taken with
-- `jetProjection_surjective` (so that `rw` sees `jetProjection … p`, not `Ideal.Quotient.mk (span …) p`), and
-- `Ideal.Quotient.lift_mk` is rewritten with `erw` (it matches only up to unfolding `AdjoinRoot`).

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! A concrete half of the affine-space chart: coefficients on a test scheme
    produce a based jet by evaluating the universal truncated polynomial. -/

private noncomputable def affineSpaceJetCoeffPoly {k : Type u} [Field k]
    {W : AlgebraicGeometry.Scheme.{u}}
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (m r : ℕ) (a : ULift.{u} (Fin m × Fin r) → Γ(W, ⊤))
    (i : ULift.{u} (Fin m)) : Polynomial (Γ(W, ⊤)) :=
  ∑ q : Fin r, Polynomial.monomial (q.1 + 1) (a ⟨i.down, q⟩)

private theorem affineSpaceJetCoeffPoly_eval_zero {k : Type u} [Field k]
    {W : AlgebraicGeometry.Scheme.{u}}
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (m r : ℕ) (a : ULift.{u} (Fin m × Fin r) → Γ(W, ⊤))
    (i : ULift.{u} (Fin m)) :
    (affineSpaceJetCoeffPoly (k := k) m r a i).eval 0 = 0 := by
  classical
  change Polynomial.eval₂ (RingHom.id _) 0
      (Finset.univ.sum (fun q : Fin r =>
        Polynomial.monomial (q.1 + 1) (a ⟨i.down, q⟩))) = 0
  rw [Polynomial.eval₂_finsetSum]
  simp

private theorem affineSpaceJetCoeffPoly_coeff {k : Type u} [Field k]
    {W : AlgebraicGeometry.Scheme.{u}}
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (m r : ℕ) (a : ULift.{u} (Fin m × Fin r) → Γ(W, ⊤))
    (i : ULift.{u} (Fin m)) (q : Fin r) :
    (affineSpaceJetCoeffPoly (k := k) m r a i).coeff (q.1 + 1) =
      a ⟨i.down, q⟩ := by
  classical
  unfold affineSpaceJetCoeffPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single q]
  · simp
  · intro b _ hbq
    rw [if_neg]
    intro h
    apply hbq
    apply Fin.ext
    omega
  · simp

private noncomputable def affineSpaceJetOfCoordinates {k : Type u} [Field k]
    {U : AlgebraicGeometry.Scheme.{u}}
    [U.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (m r : ℕ) {W : CategoryTheory.Over U}
    (a : ULift.{u} (Fin m × Fin r) → Γ(W.left, ⊤)) :
    (relativeJetFunctor (k := k)
      (CategoryTheory.Over.mk
        (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
      (AlgebraicGeometry.AffineSpace.homOfVector (CategoryTheory.CategoryStruct.id U) 0)
      (by simp) r).obj (Opposite.op W) := by
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (U ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : W.left.Over U := ⟨W.hom⟩
  let J := jetThickening (k := k) r W.left
  let vec : ULift.{u} (Fin m) → Γ(J, ⊤) := fun i =>
    jetThickening.sectionsHom (k := k) r W.left ⊤
      (MiyaokaMori.Jet.jetProjection _ r
        (affineSpaceJetCoeffPoly (k := k) m r a i))
  let f : J ⟶ AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U :=
    AlgebraicGeometry.AffineSpace.homOfVector
      (jetThickeningProj (k := k) r W.left ≫ W.hom) vec
  refine ⟨f, ?_⟩
  constructor
  · exact AlgebraicGeometry.AffineSpace.homOfVector_over _ _
  · apply AlgebraicGeometry.AffineSpace.hom_ext
    · dsimp [f]
      rw [CategoryTheory.Category.assoc]
      rw [AlgebraicGeometry.AffineSpace.homOfVector_over]
      rw [← CategoryTheory.Category.assoc,
        jetConstantTerm_comp_proj (k := k) r, CategoryTheory.Category.id_comp]
      rw [CategoryTheory.Category.assoc,
        AlgebraicGeometry.AffineSpace.homOfVector_over,
        CategoryTheory.Category.comp_id]
    · intro i
      rw [AlgebraicGeometry.Scheme.Hom.comp_appTop]
      change (jetConstantTerm (k := k) r W.left).appTop.hom
          (f.appTop (AlgebraicGeometry.AffineSpace.coord U i)) =
        ((W.hom ≫ AlgebraicGeometry.AffineSpace.homOfVector
          (CategoryTheory.CategoryStruct.id U) 0).appTop.hom
          (AlgebraicGeometry.AffineSpace.coord U i))
      rw [AlgebraicGeometry.Scheme.Hom.comp_appTop,
        AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord]
      simp only [CommRingCat.comp_apply,
        AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord]
      simp only [Pi.zero_apply, map_zero]
      change ((jetConstantTerm (k := k) r W.left).app ⊤).hom (vec i) = 0
      rw [AlgebraicGeometry.Scheme.Hom.app_eq_appLE]
      change ((jetConstantTerm (k := k) r W.left).appLE _ ⊤ _).hom
        ((jetThickening.sectionsHom (k := k) r W.left ⊤)
          (MiyaokaMori.Jet.jetProjection _ r
            (affineSpaceJetCoeffPoly m r a i))) = 0
      rw [jetConstantTerm_sectionsHom (k := k) r W.left ⊤]
      exact affineSpaceJetCoeffPoly_eval_zero m r a i

theorem relativeJetFunctor_affineSpace_of_coordinates {k : Type u} [Field k]
    {U : AlgebraicGeometry.Scheme.{u}}
    [U.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (m r : ℕ)
    {W : CategoryTheory.Over U}
    (a : ULift.{u} (Fin m × Fin r) → Γ(W.left, ⊤)) :
    Nonempty ((relativeJetFunctor (k := k)
      (CategoryTheory.Over.mk
        (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
      (AlgebraicGeometry.AffineSpace.homOfVector (CategoryTheory.CategoryStruct.id U) 0)
      (by simp) r).obj (Opposite.op W)) :=
  ⟨affineSpaceJetOfCoordinates m r a⟩

/-- Extract the positive coefficients of each coordinate of a based affine-space jet. -/
noncomputable def relativeJetFunctor_affineSpace_coordinates {k : Type u} [Field k]
    {U : AlgebraicGeometry.Scheme.{u}}
    [U.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (m r : ℕ) {W : CategoryTheory.Over U}
    (φ : (relativeJetFunctor (k := k)
      (CategoryTheory.Over.mk
        (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
      (AlgebraicGeometry.AffineSpace.homOfVector (CategoryTheory.CategoryStruct.id U) 0)
      (by simp) r).obj (Opposite.op W)) :
    ULift.{u} (Fin m × Fin r) → Γ(W.left, ⊤) := by
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (U ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  intro iq
  let p : MiyaokaMori.Jet.TruncatedJetRing Γ(W.left, ⊤) r :=
    (RingEquiv.ofBijective _
      (jetThickening.sectionsHom_bijective (k := k) r W.left ⊤)).symm
    (φ.1.appTop
      (AlgebraicGeometry.AffineSpace.coord U ⟨iq.down.1⟩))
  exact MiyaokaMori.Jet.TruncatedJetRing.coeff r (iq.down.2.1 + 1)
    (Nat.succ_le_of_lt iq.down.2.2) p

/-! ## Computing the based jet built from coordinates -/

private theorem affineSpaceJetCoeffPoly_map {k : Type u} [Field k]
    {W W' : AlgebraicGeometry.Scheme.{u}}
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [W'.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (m r : ℕ) (a : ULift.{u} (Fin m × Fin r) → Γ(W, ⊤)) (ρ : Γ(W, ⊤) →+* Γ(W', ⊤))
    (i : ULift.{u} (Fin m)) :
    (affineSpaceJetCoeffPoly (k := k) m r a i).map ρ =
      affineSpaceJetCoeffPoly (k := k) m r (fun iq => ρ (a iq)) i := by
  unfold affineSpaceJetCoeffPoly
  rw [Polynomial.map_sum]
  simp only [Polynomial.map_monomial]

private theorem affineSpaceJetCoeffPoly_coeff_zero {k : Type u} [Field k]
    {W : AlgebraicGeometry.Scheme.{u}}
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (m r : ℕ) (a : ULift.{u} (Fin m × Fin r) → Γ(W, ⊤)) (i : ULift.{u} (Fin m)) :
    (affineSpaceJetCoeffPoly (k := k) m r a i).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact affineSpaceJetCoeffPoly_eval_zero m r a i

/-- The `i`-th coordinate of the based jet built from coefficients `a` is the truncated
polynomial `Σ_{q<r} a_{i,q} t^{q+1}` (as a section of the thickening). -/
private theorem affineSpaceJetOfCoordinates_appTop_coord {k : Type u} [Field k]
    {U : AlgebraicGeometry.Scheme.{u}}
    [U.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (m r : ℕ) {W : CategoryTheory.Over U}
    (a : ULift.{u} (Fin m × Fin r) → Γ(W.left, ⊤)) (i : ULift.{u} (Fin m)) :
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (U ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    (affineSpaceJetOfCoordinates (k := k) m r a).1.appTop.hom
        (AlgebraicGeometry.AffineSpace.coord U i) =
      jetThickening.sectionsHom (k := k) r W.left ⊤
        (MiyaokaMori.Jet.jetProjection _ r (affineSpaceJetCoeffPoly (k := k) m r a i)) :=
  AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord _ _ _

/-- The order-`0` coefficient is the augmentation `t ↦ 0`. -/
private theorem truncatedJetRing_coeff_zero_eq_epsilon {S : Type u} [CommRing S] (r : ℕ)
    (p : MiyaokaMori.Jet.TruncatedJetRing S r) :
    MiyaokaMori.Jet.TruncatedJetRing.coeff r 0 (Nat.zero_le r) p =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r p := by
  obtain ⟨P, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ p
  exact (MiyaokaMori.Jet.TruncatedJetRing.coeff_jetProjection r 0 (Nat.zero_le r) P).trans
    (Polynomial.coeff_zero_eq_eval_zero P)

/-- Extracting coordinates from the jet built out of coefficients gives the coefficients back. -/
theorem relativeJetFunctor_affineSpace_coordinates_of_coordinates {k : Type u} [Field k]
    {U : AlgebraicGeometry.Scheme.{u}}
    [U.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (m r : ℕ) {W : CategoryTheory.Over U}
    (a : ULift.{u} (Fin m × Fin r) → Γ(W.left, ⊤)) :
    relativeJetFunctor_affineSpace_coordinates (k := k) m r
      (affineSpaceJetOfCoordinates (k := k) m r a) = a := by
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (U ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  funext iq
  show MiyaokaMori.Jet.TruncatedJetRing.coeff r (iq.down.2.1 + 1) (Nat.succ_le_of_lt iq.down.2.2)
    ((RingEquiv.ofBijective _
      (jetThickening.sectionsHom_bijective (k := k) r W.left ⊤)).symm
      ((affineSpaceJetOfCoordinates (k := k) m r a).1.appTop.hom
        (AlgebraicGeometry.AffineSpace.coord U ⟨iq.down.1⟩))) = a iq
  rw [affineSpaceJetOfCoordinates_appTop_coord]
  have h : (RingEquiv.ofBijective _
      (jetThickening.sectionsHom_bijective (k := k) r W.left ⊤)).symm
      (jetThickening.sectionsHom (k := k) r W.left ⊤
        (MiyaokaMori.Jet.jetProjection _ r (affineSpaceJetCoeffPoly (k := k) m r a ⟨iq.down.1⟩))) =
      MiyaokaMori.Jet.jetProjection _ r (affineSpaceJetCoeffPoly (k := k) m r a ⟨iq.down.1⟩) :=
    (RingEquiv.ofBijective _
      (jetThickening.sectionsHom_bijective (k := k) r W.left ⊤)).symm_apply_apply
      (MiyaokaMori.Jet.jetProjection _ r (affineSpaceJetCoeffPoly (k := k) m r a ⟨iq.down.1⟩))
  rw [h, MiyaokaMori.Jet.TruncatedJetRing.coeff_jetProjection]
  exact affineSpaceJetCoeffPoly_coeff m r a ⟨iq.down.1⟩ iq.down.2

/-- The constant term of every coordinate of a based affine-space jet vanishes. -/
private theorem relativeJetFunctor_affineSpace_epsilon {k : Type u} [Field k]
    {U : AlgebraicGeometry.Scheme.{u}}
    [U.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (m r : ℕ) {W : CategoryTheory.Over U}
    (φ : (relativeJetFunctor (k := k)
      (CategoryTheory.Over.mk
        (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
      (AlgebraicGeometry.AffineSpace.homOfVector (CategoryTheory.CategoryStruct.id U) 0)
      (by simp) r).obj (Opposite.op W)) (i : ULift.{u} (Fin m)) :
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (U ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r
      ((RingEquiv.ofBijective _
        (jetThickening.sectionsHom_bijective (k := k) r W.left ⊤)).symm
        (φ.1.appTop.hom (AlgebraicGeometry.AffineSpace.coord U i))) = 0 := by
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (U ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have h0 : (W.hom ≫ AlgebraicGeometry.AffineSpace.homOfVector
      (CategoryTheory.CategoryStruct.id U) 0).appTop.hom
        (AlgebraicGeometry.AffineSpace.coord U i) = 0 := by
    rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord]
    simp only [Pi.zero_apply, map_zero]
  have h := congrArg (fun ψ => ψ.appTop.hom (AlgebraicGeometry.AffineSpace.coord U i)) φ.2.2
  simp only at h
  rw [h0, AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  change ((jetConstantTerm (k := k) r W.left).app ⊤).hom
    (φ.1.appTop.hom (AlgebraicGeometry.AffineSpace.coord U i)) = 0 at h
  rw [AlgebraicGeometry.Scheme.Hom.app_eq_appLE] at h
  obtain ⟨p, hp⟩ := (jetThickening.sectionsHom_bijective (k := k) r W.left ⊤).2
    (φ.1.appTop.hom (AlgebraicGeometry.AffineSpace.coord U i))
  have hp' : (RingEquiv.ofBijective _
      (jetThickening.sectionsHom_bijective (k := k) r W.left ⊤)).symm
        (φ.1.appTop.hom (AlgebraicGeometry.AffineSpace.coord U i)) = p := by
    rw [← hp]
    exact (RingEquiv.ofBijective _
      (jetThickening.sectionsHom_bijective (k := k) r W.left ⊤)).symm_apply_apply p
  rw [hp', ← jetConstantTerm_sectionsHom (k := k) r W.left ⊤ p, hp]
  exact h

/-- Building a based jet from the coordinates of a based jet gives the jet back. -/
theorem affineSpaceJetOfCoordinates_coordinates {k : Type u} [Field k]
    {U : AlgebraicGeometry.Scheme.{u}}
    [U.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (m r : ℕ) {W : CategoryTheory.Over U}
    (φ : (relativeJetFunctor (k := k)
      (CategoryTheory.Over.mk
        (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
      (AlgebraicGeometry.AffineSpace.homOfVector (CategoryTheory.CategoryStruct.id U) 0)
      (by simp) r).obj (Opposite.op W)) :
    affineSpaceJetOfCoordinates (k := k) m r
      (relativeJetFunctor_affineSpace_coordinates (k := k) m r φ) = φ := by
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (U ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  apply Subtype.ext
  apply AlgebraicGeometry.AffineSpace.hom_ext
  · exact (affineSpaceJetOfCoordinates (k := k) m r
      (relativeJetFunctor_affineSpace_coordinates (k := k) m r φ)).2.1.trans φ.2.1.symm
  · intro i
    rw [affineSpaceJetOfCoordinates_appTop_coord]
    set e := RingEquiv.ofBijective _ (jetThickening.sectionsHom_bijective (k := k) r W.left ⊤)
      with he
    have hx : φ.1.appTop.hom (AlgebraicGeometry.AffineSpace.coord U i) =
        jetThickening.sectionsHom (k := k) r W.left ⊤
          (e.symm (φ.1.appTop.hom (AlgebraicGeometry.AffineSpace.coord U i))) :=
      (e.apply_symm_apply _).symm
    rw [hx]
    congr 1
    apply MiyaokaMori.Jet.TruncatedJetRing.ext_coeff
    intro n hn
    rw [MiyaokaMori.Jet.TruncatedJetRing.coeff_jetProjection]
    cases n with
    | zero =>
      rw [affineSpaceJetCoeffPoly_coeff_zero, truncatedJetRing_coeff_zero_eq_epsilon]
      exact (relativeJetFunctor_affineSpace_epsilon (k := k) m r φ i).symm
    | succ q =>
      rw [affineSpaceJetCoeffPoly_coeff m r _ i ⟨q, Nat.lt_of_succ_le hn⟩]
      rfl

/-! ## Naturality of `sectionsHom` in the base -/

/-- `jetThickeningMap` is natural for `sectionsHom`: for `g : W' ⟶ W` over `k`, `V ⊆ W` open and
`p ∈ Γ(W,V)[t]/(t^{r+1})`, `(g × 𝟙)^♯ (sectionsHom_V p) = sectionsHom_{g⁻¹V} (g^♯ applied to the
coefficients of p)`.

Proof: both sides are ring homomorphisms out of the quotient `Γ(W,V)[t]/(t^{r+1})`, so it suffices
to check on constants and on `t` (`Ideal.Quotient.ringHom_ext`, `Polynomial.ringHom_ext`).
On a constant `a`: `sectionsHom` sends it to `pr^♯ a`, and `(g × 𝟙) ≫ pr = pr ≫ g`
(`jetThickeningMap_proj`). On `t`: `t = snd^♯ [X]` and `(g × 𝟙) ≫ snd = snd`
(`jetThickeningMap_snd`).

Source: §2.2 of the paper (functions on `W ×_k D_r` are truncated polynomials). -/
theorem jetThickening.sectionsHom_jetThickeningMap {k : Type u} [Field k] (r : ℕ)
    {W W' : AlgebraicGeometry.Scheme.{u}}
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [W'.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (g : W' ⟶ W) [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] (V : W.Opens)
    (p : MiyaokaMori.Jet.TruncatedJetRing Γ(W, V) r)
    (hle : jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V) ≤
      jetThickeningMap (k := k) r g ⁻¹ᵁ (jetThickeningProj (k := k) r W ⁻¹ᵁ V)) :
    ((jetThickeningMap (k := k) r g).appLE _ _ hle).hom
        (jetThickening.sectionsHom (k := k) r W V p) =
      jetThickening.sectionsHom (k := k) r W' (g ⁻¹ᵁ V)
        (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (g.app V).hom p) := by
  obtain ⟨p, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ p
  rw [MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map_projection]
  unfold jetThickening.sectionsHom
  rw [MiyaokaMori.Jet.lift_jetProjection, MiyaokaMori.Jet.lift_jetProjection]
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map]
  rw [Polynomial.hom_eval₂]
  congr 1
  · ext a
    have h1 := AlgebraicGeometry.Scheme.Hom.comp_appLE (jetThickeningMap (k := k) r g)
      (jetThickeningProj (k := k) r W) V
      (jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V)) hle
    have h2 := AlgebraicGeometry.Scheme.Hom.comp_appLE (jetThickeningProj (k := k) r W') g V
      (jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V)) le_rfl
    have h3 := AlgebraicGeometry.Scheme.Hom.appLE_congr_hom (jetThickeningMap_proj (k := k) r g) V
      (jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V)) hle le_rfl
    rw [h1, h2] at h3
    have h4 := congrArg (fun φ : Γ(W, V) ⟶ Γ(jetThickening (k := k) r W',
      jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V)) => φ.hom a) h3
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h4
    rw [AlgebraicGeometry.Scheme.Hom.appLE_eq_app] at h4
    exact h4
  · have h1 := AlgebraicGeometry.Scheme.Hom.map_appLE (jetThickeningMap (k := k) r g) hle
      (CategoryTheory.homOfLE (le_top : jetThickeningProj (k := k) r W ⁻¹ᵁ V ≤ ⊤)).op
    have h2 := congrArg (fun φ : Γ(jetThickening (k := k) r W, ⊤) ⟶
      Γ(jetThickening (k := k) r W', jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V)) =>
        φ.hom (jetThickening.parameter (k := k) r W)) h1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
    rw [h2]
    unfold jetThickening.parameter
    have h3 := AlgebraicGeometry.Scheme.Hom.comp_appLE (jetThickeningMap (k := k) r g)
      (CategoryTheory.Limits.pullback.snd (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ⊤
      (jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V)) le_top
    have h4 := AlgebraicGeometry.Scheme.Hom.appLE_congr_hom (jetThickeningMap_snd (k := k) r g) ⊤
      (jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V)) le_top le_top
    rw [h3] at h4
    have h5 := congrArg (fun φ : Γ(jetBase k r, ⊤) ⟶
      Γ(jetThickening (k := k) r W', jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V)) =>
        φ.hom ((AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r))).inv.hom
            (MiyaokaMori.Jet.jetProjection k r Polynomial.X))) h4
    simp only [CommRingCat.hom_comp] at h5
    exact h5.trans rfl

/-- Global-sections form of `jetThickening.sectionsHom_jetThickeningMap`. -/
theorem jetThickening.sectionsHom_jetThickeningMap_top {k : Type u} [Field k] (r : ℕ)
    {W W' : AlgebraicGeometry.Scheme.{u}}
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [W'.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (g : W' ⟶ W) [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (p : MiyaokaMori.Jet.TruncatedJetRing Γ(W, ⊤) r) :
    (jetThickeningMap (k := k) r g).appTop.hom (jetThickening.sectionsHom (k := k) r W ⊤ p) =
      jetThickening.sectionsHom (k := k) r W' ⊤
        (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r g.appTop.hom p) := by
  rw [show (jetThickeningMap (k := k) r g).appTop =
      (jetThickeningMap (k := k) r g).appLE ⊤ _ le_rfl from
    AlgebraicGeometry.Scheme.Hom.app_eq_appLE _]
  exact jetThickening.sectionsHom_jetThickeningMap (k := k) r g ⊤ p (fun _ _ => trivial)

/-- Building based jets from coordinates is natural in the test scheme. -/
theorem affineSpaceJetOfCoordinates_map {k : Type u} [Field k]
    {U : AlgebraicGeometry.Scheme.{u}}
    [U.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (m r : ℕ) {W W' : CategoryTheory.Over U} (f : W' ⟶ W)
    (a : ULift.{u} (Fin m × Fin r) → Γ(W.left, ⊤)) :
    affineSpaceJetOfCoordinates (k := k) m r (fun iq => f.left.appTop.hom (a iq)) =
      (relativeJetFunctor (k := k)
        (CategoryTheory.Over.mk
          (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
        (AlgebraicGeometry.AffineSpace.homOfVector (CategoryTheory.CategoryStruct.id U) 0)
        (by simp) r).map f.op (affineSpaceJetOfCoordinates (k := k) m r a) := by
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (U ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : W'.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W'.hom ≫ (U ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : f.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.Over.w_assoc f _⟩
  apply Subtype.ext
  apply AlgebraicGeometry.AffineSpace.hom_ext
  · exact (affineSpaceJetOfCoordinates (k := k) m r
      (fun iq => f.left.appTop.hom (a iq))).2.1.trans
      ((relativeJetFunctor (k := k) _ _ _ r).map f.op
        (affineSpaceJetOfCoordinates (k := k) m r a)).2.1.symm
  · intro i
    rw [affineSpaceJetOfCoordinates_appTop_coord]
    change _ = (jetThickeningMap (k := k) r f.left ≫
      (affineSpaceJetOfCoordinates (k := k) m r a).1).appTop.hom
        (AlgebraicGeometry.AffineSpace.coord U i)
    rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      affineSpaceJetOfCoordinates_appTop_coord,
      jetThickening.sectionsHom_jetThickeningMap_top,
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map_projection,
      affineSpaceJetCoeffPoly_map]

/-! ## The affine-space jet functor is represented by `𝔸^{mr}_U` -/

/-- `𝔸(Fin m × Fin r; U)` represents the based jet functor of `𝔸(Fin m; U)/U` at the zero
section: a `U`-morphism `W → 𝔸^{mr}_U` is `m·r` functions `a_{i,q}` on `W`
(`AffineSpace.homOverEquiv`), which give the based jet `x_i ↦ Σ_{q<r} a_{i,q} t^{q+1}`
(`affineSpaceJetOfCoordinates`); conversely a based jet has coordinates
(`relativeJetFunctor_affineSpace_coordinates`). Ein–Mustaţă, *Jet schemes and singularities*,
Remark 2.6, relative and based version; §2.2 of the paper. -/
noncomputable def relativeJetFunctor.affineSpaceRepresentableBy {k : Type u} [Field k]
    {U : AlgebraicGeometry.Scheme.{u}}
    [U.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (m r : ℕ) :
    (relativeJetFunctor (k := k)
      (CategoryTheory.Over.mk
        (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
      (AlgebraicGeometry.AffineSpace.homOfVector (CategoryTheory.CategoryStruct.id U) 0)
      (by simp) r).RepresentableBy
      (CategoryTheory.Over.mk (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m × Fin r)) U ↘ U)) where
  homEquiv {W} :=
    { toFun := fun g => affineSpaceJetOfCoordinates (k := k) m r
        (fun iq => g.left.appTop.hom (AlgebraicGeometry.AffineSpace.coord U iq))
      invFun := fun φ => CategoryTheory.Over.homMk
        (AlgebraicGeometry.AffineSpace.homOfVector W.hom
          (relativeJetFunctor_affineSpace_coordinates (k := k) m r φ))
        (AlgebraicGeometry.AffineSpace.homOfVector_over _ _)
      left_inv := fun g => by
        apply CategoryTheory.Over.OverMorphism.ext
        show AlgebraicGeometry.AffineSpace.homOfVector W.hom
          (relativeJetFunctor_affineSpace_coordinates (k := k) m r
            (affineSpaceJetOfCoordinates (k := k) m r
              (fun iq => g.left.appTop.hom (AlgebraicGeometry.AffineSpace.coord U iq)))) = g.left
        apply AlgebraicGeometry.AffineSpace.hom_ext
        · rw [AlgebraicGeometry.AffineSpace.homOfVector_over]
          exact (CategoryTheory.Over.w g).symm
        · intro iq
          rw [AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord,
            relativeJetFunctor_affineSpace_coordinates_of_coordinates]
      right_inv := fun φ => by
        show affineSpaceJetOfCoordinates (k := k) m r
          (fun iq => (AlgebraicGeometry.AffineSpace.homOfVector W.hom
            (relativeJetFunctor_affineSpace_coordinates (k := k) m r φ)).appTop.hom
              (AlgebraicGeometry.AffineSpace.coord U iq)) = φ
        have h : (fun iq => (AlgebraicGeometry.AffineSpace.homOfVector W.hom
            (relativeJetFunctor_affineSpace_coordinates (k := k) m r φ)).appTop.hom
              (AlgebraicGeometry.AffineSpace.coord U iq)) =
            relativeJetFunctor_affineSpace_coordinates (k := k) m r φ := by
          funext iq
          exact AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord _ _ _
        exact (congrArg (affineSpaceJetOfCoordinates (k := k) m r) h).trans
          (affineSpaceJetOfCoordinates_coordinates (k := k) m r φ) }
  homEquiv_comp {W W'} f g := by
    have h : (fun iq => (f ≫ g).left.appTop.hom (AlgebraicGeometry.AffineSpace.coord U iq)) =
        fun iq => f.left.appTop.hom
          (g.left.appTop.hom (AlgebraicGeometry.AffineSpace.coord U iq)) := by
      funext iq
      rw [CategoryTheory.Over.comp_left, AlgebraicGeometry.Scheme.Hom.comp_appTop,
        CommRingCat.comp_apply]
    exact (congrArg (affineSpaceJetOfCoordinates (k := k) m r) h).trans
      (affineSpaceJetOfCoordinates_map (k := k) m r f _)

/-! ## The targets -/

/-- The based jet scheme of `𝔸^m_U/U` at the zero section is `𝔸^{m·r}_U`, as a scheme over `U`. -/
theorem jetScheme_affineSpace {k : Type u} [Field k] {U : AlgebraicGeometry.Scheme.{u}}
    [U.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (m r : ℕ) :
    -- The `hom` of `Over.mk (𝔸 ↘ U)` does not unfold at instance-search transparency, so Mathlib's
    -- instance `IsAffineHom (𝔸(n; S) ↘ S)` has to be transported explicitly.
    letI : AlgebraicGeometry.IsAffineHom
        (CategoryTheory.Over.mk (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U)).hom :=
      inferInstanceAs (AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
    Nonempty (relativeJetScheme (k := k)
        (CategoryTheory.Over.mk (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
        (AlgebraicGeometry.AffineSpace.homOfVector (CategoryTheory.CategoryStruct.id U) 0)
        (by simp) r ≅
      CategoryTheory.Over.mk (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m × Fin r)) U ↘ U)) := by
  letI : AlgebraicGeometry.IsAffineHom
      (CategoryTheory.Over.mk (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U)).hom :=
    inferInstanceAs (AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
  exact ⟨(relativeJetScheme.representableBy (k := k) _ _ _ r).uniqueUpToIso
    (relativeJetFunctor.affineSpaceRepresentableBy (k := k) m r)⟩

/--
The affine-space jet chart, with the underlying Scheme isomorphism and its
compatibility with the structure morphism to `U` made explicit.

This is the form consumed by local-coordinate arguments: the original
`jetScheme_affineSpace` statement is intentionally retained in `Over U`, while
this companion theorem exposes its underlying morphism without losing the
projection equation carried by the `Over` morphism.
-/
theorem jetScheme_affineSpace_underlying {k : Type u} [Field k]
    {U : AlgebraicGeometry.Scheme.{u}}
    [U.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (m r : ℕ) :
    letI : AlgebraicGeometry.IsAffineHom
        (CategoryTheory.Over.mk (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U)).hom :=
      inferInstanceAs (AlgebraicGeometry.IsAffineHom
        (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
    ∃ e : (relativeJetScheme (k := k)
        (CategoryTheory.Over.mk (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
        (AlgebraicGeometry.AffineSpace.homOfVector (CategoryTheory.CategoryStruct.id U) 0)
        (by simp) r).left ≅
      AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m × Fin r)) U,
      e.hom ≫
          (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m × Fin r)) U ↘ U) =
        (relativeJetScheme (k := k)
          (CategoryTheory.Over.mk (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
          (AlgebraicGeometry.AffineSpace.homOfVector (CategoryTheory.CategoryStruct.id U) 0)
          (by simp) r).hom := by
  letI : AlgebraicGeometry.IsAffineHom
      (CategoryTheory.Over.mk (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U)).hom :=
    inferInstanceAs (AlgebraicGeometry.IsAffineHom
      (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
  obtain ⟨e⟩ := jetScheme_affineSpace (k := k) (U := U) m r
  exact ⟨(CategoryTheory.Over.forget U).mapIso e, e.hom.w⟩

end
