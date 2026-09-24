import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.LocalJetInFrame
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.GenericAffineJetPoint
import MiyaokaMori.RingTheory.WeightedHomogeneousEvalZpowRescale

/-! # The coefficient map of a framed honest chart and its generic values
(steps 1–2 of the proof of Lemma 3.1 of the paper)

The paper's normalized coefficients `a_{α,i,q} = γ^{-q} b_{α,i,q}` are regular functions on `U`
whose generic values are the rescaled coordinates of the affine jet `ĵ`. The local jet is the
`𝒪(U)`-point of the affine jet scheme `J_κ^s|_{V_α} ≅ V_α × A^N` with these coordinates, i.e. the
`Γ(V_α)`-algebra map `φ : S(V_α) = Γ(V_α)[x_{α,i,q}] → 𝒪(U)`, `x_{α,i,q} ↦ a_{α,i,q}`
(`exists_algHom_of_honestChart`). What the gluing and the coefficient computation need from `φ` is
only its **generic value on every homogeneous function**: for `y ∈ S_m(V_α)`,
`φ(y)(η) = γ^{-m} · y(ĵ)` (`y(ĵ) = affineJetCoord`); this is the content of the lemma, and it is what
makes the local jets independent of the chart (Lemma 3.1 of the paper: "these expressions agree under
changes of both the jet chart and the frame").

Notation: `jetCoordinateSection V y ∈ Γ(J_κ^s, π⁻¹V)` is the based-jet-algebra element `y ∈ J_κ(B_V, s^♯)`
seen as a function on the jet scheme (`relativeJetScheme.chartSections`, transported along
`hom_preimage_chartOpen`); `affineJetValue ρ ĵ hV g ∈ K(C̃)` is the value of such a function at `ĵ`, and
`affineJetCoeff ρ ĵ hV n c := affineJetValue (jetCoordinateSection V (d_{n-1} c))` the value of the jet
coordinate `d_{n-1} c = coeffClass n c`. `affineJetCoord ρ ĵ hV m x = affineJetValue ρ ĵ hV (partι x)`
by definition (`affineJetCoord_eq_affineJetValue`).

-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace jetNeighborhood

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
  (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ)

/-- An element `y ∈ J_κ(B_V, s^♯)` of the based jet algebra of the cone over the affine open `V` as a
function on the affine jet scheme over `V`: `chartSections` followed by the identification
`π⁻¹V = chartOpen V` (`relativeJetScheme.hom_preimage_chartOpen`). -/
def jetCoordinateSection (V : C.toScheme.AffineZariskiSite) (y : coneJetAlgebra f κ V.1) :
    Γ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left,
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V.1) :=
  ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left.presheaf.map
      (CategoryTheory.eqToHom (relativeJetScheme.hom_preimage_chartOpen (k := k) (MMSetup.cone f)
        (MMSetup.seed f).1 (MMSetup.seed f).2 κ V)).op).hom
    ((relativeJetScheme.chartSections (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ V).hom y)

/-- `jetCoordinateSection V` is the chart identification `relativeJetScheme.chartEquiv V`
(`chartEquiv_eq_chartSections`). -/
theorem jetCoordinateSection_eq_chartEquiv (V : C.toScheme.AffineZariskiSite) (y : coneJetAlgebra f κ V.1) :
    jetCoordinateSection f κ V y =
      relativeJetScheme.chartEquiv (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ V y :=
  (relativeJetScheme.chartEquiv_eq_chartSections (k := k) (MMSetup.cone f) (MMSetup.seed f).1
    (MMSetup.seed f).2 κ V _ y).symm

/-- Every function on the affine jet scheme over the affine open `V` is a `jetCoordinateSection`
(`chartEquiv` is a ring isomorphism). -/
theorem jetCoordinateSection_surjective (V : C.toScheme.AffineZariskiSite)
    (g : Γ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left,
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V.1)) :
    ∃ y : coneJetAlgebra f κ V.1, jetCoordinateSection f κ V y = g :=
  ⟨(relativeJetScheme.chartEquiv (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ V).symm g,
    (jetCoordinateSection_eq_chartEquiv f κ V _).trans (RingEquiv.apply_symm_apply _ g)⟩

variable (ρ : FiniteCover k C)

/-- The value in `K(C̃)` of a function `g ∈ Γ(J_κ^s, π⁻¹V)` at a `κ(η_{C̃})`-point `ĵ` of `J_κ^s` lying
over `V` (`ĵ^♯ g`, read through `ΓSpecIso` and `functionFieldIsoResidueField`; cf. `affineJetCoord`). -/
def affineJetValue
    (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    {V : C.toScheme.Opens}
    (hV : (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V))
    (g : Γ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left,
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V)) :
    ρ.source.toScheme.functionField :=
  haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  ρ.source.toScheme.functionFieldIsoResidueField.inv.hom
    ((AlgebraicGeometry.Scheme.ΓSpecIso
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).hom.hom
      ((ĵ.appLE _ ⊤ hV).hom g))

/-- `affineJetCoord` is `affineJetValue` of `partι x`. -/
theorem affineJetCoord_eq_affineJetValue
    (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    {V : C.toScheme.Opens}
    (hV : (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V))
    (m : ℕ) (x : (jetAlgebra f κ).sectionsPiece V m) :
    affineJetCoord ρ ĵ hV m x =
      affineJetValue f κ ρ ĵ hV ((BasedJet.partι f κ m).val.app (Opposite.op V) x) := rfl

/-- The value at `ĵ` of the jet coordinate `d_{n-1} c = coeffClass n c` (`c ∈ B_V`, `n ≤ κ`; for `n = 0`
it is the constant `s^♯ c`). -/
def affineJetCoeff
    (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    {V : C.toScheme.Opens} (hVa : AlgebraicGeometry.IsAffineOpen V)
    (hV : (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V))
    (n : ℕ) (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V)) : ρ.source.toScheme.functionField :=
  letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) V
  affineJetValue f κ ρ ĵ hV (jetCoordinateSection f κ ⟨V, hVa⟩
    (BasedJetAlgebra.coeffClass
      (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V) κ n c))

set_option linter.unusedVariables false in
/-- **The coefficient map of a framed honest chart, with its generic values**
(Lemma 3.1 of the paper). Data: an honest jet chart `chart` on the affine
open `V` of `C`; a `κ(η_{C̃})`-point `ĵ` of the affine jet scheme over `η_{C̃} ≫ ρ` (`hĵ`) lying over
`V` (`hĵV`); an affine open `U ∋ η_{C̃}` of `C̃` with `U ≤ ρ⁻¹V`; a scalar `γ ∈ K(C̃)` (the coefficient
of the rational section in the chosen frame) and regular functions `a i q ∈ 𝒪(U)` with generic values
`γ^{-(q+1)} · x_{i,q}(ĵ)` (`ha`; these are the normalized coefficients, given by `hreg` of the parent).
Conclusion: a `Γ(V)`-algebra map `φ : J_κ(B_V, s^♯) → 𝒪(U)` (`𝒪(U)` a `Γ(V)`-algebra through `ρ^♯`,
`baseAlgebra`) such that for every `m`, every `x ∈ S_m(V)` and every `y ∈ J_κ(B_V, s^♯)` representing
`x` (`partι x = jetCoordinateSection V y`), the generic value of `φ y` is `γ^{-m} · x(ĵ)`:
`(φ y)(η) = γ^{-m} · affineJetCoord ρ ĵ hĵV m x`.

Natural-language proof. Write `S := (jetAlgebra f κ).sectionsRing V = ⊕_m S_m(V)` and
`A := J_κ(B_V, s^♯)` (= `relativeJetScheme.chartRing V`).
1. **The chart.** `chart.honest` gives `ε : S ≃+* Γ(V)[x_p]` with `ε(sectionsUnitHom r) = C r`,
   `ε(ofPiece (chart.coords p)) = X p`, and `a ∈ S_m ↔ ε a` weighted homogeneous of weight `m`
   (`jetChart.IsHonest`). Let `ev_a : Γ(V)[x_p] →+* 𝒪(U)` be `MvPolynomial.eval₂Hom (ρ^♯) (p ↦ a p.down)`
   and `φ₀ := ev_a ∘ ε : S →+* 𝒪(U)`.
2. **The bridge `A ≃+* S`.** `Θ := weightPartιRingHom (jetRescalingAction …) V : S →+* Γ(J, π⁻¹V)`
   is bijective on the affine `V` (`relativeJetScheme.weightPartιRingHom_bijective`) and
   `Θ (ofPiece m x) = partι x` (`weightPartιRingHom_ofPiece`; `weightPartιApp` is `kernel.ι` on
   sections, which is `partι`); `jetCoordinateSection V : A →+* Γ(J, π⁻¹V)` is the ring isomorphism
   `chartEquiv` (`jetCoordinateSection_eq_chartEquiv`). Put `β := Θ⁻¹ ∘ jetCoordinateSection : A ≃+* S`
   and `φ := φ₀ ∘ β`; it is `Γ(V)`-linear because `β (algebraMap r) = sectionsUnitHom r`
   (`chartEquiv_unitHom`, `weightPartιRingHom_sectionsUnitHom`) and `φ₀ (sectionsUnitHom r) = ev_a (C r) = ρ^♯ r`.
3. **The rescaled evaluation at `ĵ`.** `Ξ : S →+* K(C̃)`, `Ξ := affineJetValue ρ ĵ hĵV ∘ Θ`, is a ring
   homomorphism with `Ξ (ofPiece m x) = affineJetCoord ρ ĵ hĵV m x`. Define
   `Ξ_γ : S →+* K(C̃)` on the direct sum by `ofPiece m x ↦ γ^{-m} · Ξ (ofPiece m x)` (`DirectSum.toSemiring`):
   multiplicative because `Ξ` respects `sectionsGMul` and `γ^{-(m+n)} = γ^{-m} γ^{-n}` (also for `γ = 0`,
   where both sides vanish unless `m = n = 0`), unital because `γ^0 = 1`.
4. **`germ ∘ φ₀ = Ξ_γ`.** Both are ring homomorphisms `Γ(V)[x_p] → K(C̃)` after `ε⁻¹`
   (`MvPolynomial.ringHom_ext`): on `C r`, `germ (ev_a (C r)) = germ (ρ^♯ r)` and
   `Ξ_γ (sectionsUnitHom r) = Ξ (sectionsUnitHom r) = affineJetValue (π^♯ r) = (η ≫ ρ)^♯ r = germ (ρ^♯ r)`
   (weight `0`, `hĵ`, `Scheme.Hom.appLE_comp_appLE`, `fromSpecResidueField` on functions is the germ
   followed by the residue map, `functionFieldIsoResidueField`); on `X p`, `germ (ev_a (X p)) = germ (a p)
   = γ^{-w p} · affineJetCoord (coords p) = Ξ_γ (ofPiece (coords p))` (`ha`).
5. **Conclusion.** For `x ∈ S_m(V)` and `y` with `partι x = jetCoordinateSection V y`: `Θ (ofPiece m x)
   = partι x = jetCoordinateSection V y`, so `β y = ofPiece m x` (`Θ` injective) and
   `germ (φ y) = germ (φ₀ (ofPiece m x)) = Ξ_γ (ofPiece m x) = γ^{-m} · affineJetCoord ρ ĵ hĵV m x`. ∎

The formal proof follows these lines, with two simplifications: step 3's `Ξ_γ` is not
built as a ring homomorphism — instead both `germ (φ₀ (ofPiece m x))` and `affineJetCoord m x` are written
as evaluations of the weighted-homogeneous polynomial `P := ε (ofPiece m x)` (`eval₂_comp_left`, and
`Ξ ∘ ε⁻¹ = eval₂Hom (germ ∘ ρ^♯) (p ↦ affineJetCoord (coords p))` by `MvPolynomial.ringHom_ext`, where
`Ξ := ι_K⁻¹ ∘ affineJetSectionsHom ĵ` has `Ξ (ofPiece n z) = affineJetCoord n z`,
`affineJetCoord_eq_affineJetSectionsHom`, and `Ξ (unitHom r) = germ (ρ^♯ r)`,
`affineJetSectionsHom_unit_eq_germ`), and the rescaling `eval₂ g (γ^{-w p} c p) P = γ^{-m} eval₂ g c P` is the
pure algebra lemma `MvPolynomial.IsWeightedHomogeneous.eval₂_zpow_neg_weight`
Edge cases: `κ = 0` (`Fin κ` empty, `a` vacuous, `S = Γ(V)`,
`φ = ρ^♯` on the constants, weight `0` only); `γ = 0` (`0^{-n} = 0` kills positive weights; consistent with
`ha`; the algebra lemma needs no `γ ≠ 0`); `U` must contain `η` for the germs. The affineness `hU` of `U` is
**not used** by this lemma (it is kept in the statement because the parent `exists_basedJet_of_regular_coefficients`
passes it to all lemmas uniformly). -/
theorem exists_algHom_of_honestChart {V : C.toScheme.Opens} (chart : HonestJetChart f κ V)
    (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    (hĵ : ĵ ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom =
      ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)
    (hĵV : (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V))
    {U : ρ.source.toScheme.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    (hηU : genericPoint ρ.source.toScheme ∈ U) (hUV : U ≤ ρ.hom ⁻¹ᵁ V)
    (γ : ρ.source.toScheme.functionField)
    (a : Fin (X.toVariety.dim + 1) → Fin κ → Γ(ρ.source.toScheme, U))
    (ha : ∀ (i : Fin (X.toVariety.dim + 1)) (q : Fin κ),
      (haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
       haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
       (ρ.source.toScheme.germToFunctionField U).hom (a i q)) =
        γ ^ (-((q : ℕ) + 1 : ℤ)) * affineJetCoord ρ ĵ hĵV _ (chart.coords (i, q))) :
    ∃ φ : (letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) V
        letI := baseAlgebra ρ hUV
        coneJetAlgebra f κ V →ₐ[Γ(C.toScheme, V)] Γ(ρ.source.toScheme, U)),
      ∀ (m : ℕ) (x : (jetAlgebra f κ).sectionsPiece V m) (y : coneJetAlgebra f κ V),
        (BasedJet.partι f κ m).val.app (Opposite.op V) x = jetCoordinateSection f κ ⟨V, chart.isAffineOpen⟩ y →
        (haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
         haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
         (ρ.source.toScheme.germToFunctionField U).hom (φ y)) =
          γ ^ (-(m : ℤ)) * affineJetCoord ρ ĵ hĵV m x := by
  classical
  haveI hint : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  haveI hne : Nonempty U := ⟨⟨_, hηU⟩⟩
  letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) V
  letI := baseAlgebra ρ hUV
  let α := jetRescalingAction (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ
  let J := relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ
  have hVa : AlgebraicGeometry.IsAffineOpen V := chart.isAffineOpen
  -- the germ map `𝒪(U) → K(C̃)` and `ρ^♯ : Γ(V) → 𝒪(U)`
  let germK : Γ(ρ.source.toScheme, U) →+* ρ.source.toScheme.functionField :=
    (ρ.source.toScheme.germToFunctionField U).hom
  let ρsh : Γ(C.toScheme, V) →+* Γ(ρ.source.toScheme, U) := (ρ.hom.appLE V U hUV).hom
  -- step 1: the chart
  obtain ⟨ε, -, -, hgr, hunit, hcoords, -, -⟩ := chart.honest
  let ev : MvPolynomial (ULift.{u} (Fin (X.toVariety.dim + 1) × Fin κ)) Γ(C.toScheme, V) →+*
      Γ(ρ.source.toScheme, U) :=
    MvPolynomial.eval₂Hom ρsh (fun p => a p.down.1 p.down.2)
  let φ₀ : (jetAlgebra f κ).sectionsRing V →+* Γ(ρ.source.toScheme, U) := ev.comp ε.toRingHom
  -- step 2: the bridge `Θ : S(V) ≃+* Γ(J, π⁻¹V)` and `χ : A ≃+* Γ(J, π⁻¹V)`
  obtain ⟨Θe, hΘe⟩ : ∃ Θe : (jetAlgebra f κ).sectionsRing V ≃+* Γ(J.left, J.hom ⁻¹ᵁ V),
      ∀ x, Θe x = GroupSchemeAction.weightPartιRingHom α V x :=
    ⟨RingEquiv.ofBijective _ (relativeJetScheme.weightPartιRingHom_bijective (k := k) (MMSetup.cone f)
      (MMSetup.seed f).1 (MMSetup.seed f).2 κ ⟨V, hVa⟩), fun _ => rfl⟩
  let χ : coneJetAlgebra f κ V →+* Γ(J.left, J.hom ⁻¹ᵁ V) :=
    (relativeJetScheme.chartEquiv (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ
      ⟨V, hVa⟩).toRingHom
  let φ' : coneJetAlgebra f κ V →+* Γ(ρ.source.toScheme, U) := φ₀.comp (Θe.symm.toRingHom.comp χ)
  have hcomm : ∀ r : Γ(C.toScheme, V),
      φ' (algebraMap Γ(C.toScheme, V) (coneJetAlgebra f κ V) r) = ρsh r := by
    intro r
    have h1 : χ (algebraMap Γ(C.toScheme, V) (coneJetAlgebra f κ V) r) = (J.hom.app V).hom r :=
      relativeJetScheme.chartEquiv_unitHom (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ
        ⟨V, hVa⟩ r
    have h2 : Θe ((jetAlgebra f κ).sectionsUnitHom V r) = (J.hom.app V).hom r :=
      (hΘe _).trans (GroupSchemeAction.weightPartιRingHom_sectionsUnitHom α V r)
    show φ₀ (Θe.symm (χ (algebraMap Γ(C.toScheme, V) (coneJetAlgebra f κ V) r))) = ρsh r
    rw [h1, ← h2, Θe.symm_apply_apply]
    show ev (ε ((jetAlgebra f κ).sectionsUnitHom V r)) = ρsh r
    rw [hunit r, MvPolynomial.eval₂Hom_C]
  refine ⟨{ toRingHom := φ', commutes' := hcomm }, ?_⟩
  intro m x y hxy
  -- step 5: `β y = ofPiece m x`
  have hβ : Θe.symm (χ y) = (jetAlgebra f κ).ofPiece V m x := by
    apply Θe.injective
    rw [Θe.apply_symm_apply, hΘe]
    have h3 : GroupSchemeAction.weightPartιRingHom α V ((jetAlgebra f κ).ofPiece V m x) =
        GroupSchemeAction.weightPartιApp α m V x :=
      GroupSchemeAction.weightPartιRingHom_ofPiece α V m x
    refine Eq.trans ?_ h3.symm
    exact ((jetCoordinateSection_eq_chartEquiv f κ ⟨V, hVa⟩ y).symm.trans hxy.symm)
  show germK (φ₀ (Θe.symm (χ y))) = γ ^ (-(m : ℤ)) * affineJetCoord ρ ĵ hĵV m x
  rw [hβ]
  -- step 3: the evaluation `Ξ : S(V) →+* K(C̃)` at `ĵ`, read on the pieces and on the constants
  let Ξ : (jetAlgebra f κ).sectionsRing V →+* ρ.source.toScheme.functionField :=
    ρ.source.toScheme.functionFieldIsoResidueField.inv.hom.comp (affineJetSectionsHom ĵ hĵV)
  have hΞ : ∀ (n : ℕ) (z : (jetAlgebra f κ).sectionsPiece V n),
      Ξ ((jetAlgebra f κ).ofPiece V n z) = affineJetCoord ρ ĵ hĵV n z :=
    fun n z => (affineJetCoord_eq_affineJetSectionsHom ρ ĵ hĵV n z).symm
  have hηV : genericPoint ρ.source.toScheme ∈ ρ.hom ⁻¹ᵁ V := hUV hηU
  haveI : Nonempty (ρ.hom ⁻¹ᵁ V) := ⟨⟨_, hηV⟩⟩
  have hΞC : ∀ r : Γ(C.toScheme, V), Ξ ((jetAlgebra f κ).sectionsUnitHom V r) = germK (ρsh r) := by
    intro r
    have h1 := affineJetSectionsHom_unit_eq_germ ρ ĵ hĵ hĵV (genericPoint ρ.source.toScheme) hηV r
    rw [AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField] at h1
    refine h1.trans ?_
    show (ρ.source.toScheme.germToFunctionField (ρ.hom ⁻¹ᵁ V)).hom ((ρ.hom.app V).hom r) =
      (ρ.source.toScheme.germToFunctionField U).hom
        ((ρ.source.toScheme.presheaf.map (homOfLE hUV).op).hom ((ρ.hom.app V).hom r))
    exact (ρ.source.toScheme.presheaf.germ_res_apply (homOfLE hUV) (genericPoint ρ.source.toScheme) hηU
      ((ρ.hom.app V).hom r)).symm
  -- step 4: both sides are evaluations of the weighted-homogeneous polynomial `P = ε (ofPiece m x)`
  have hPhom : (ε ((jetAlgebra f κ).ofPiece V m x)).IsWeightedHomogeneous
      (jetWeights.{u} X.toVariety.dim κ) m :=
    (hgr m _).mp ⟨x, rfl⟩
  let c : ULift.{u} (Fin (X.toVariety.dim + 1) × Fin κ) → ρ.source.toScheme.functionField :=
    fun p => affineJetCoord ρ ĵ hĵV _ (chart.coords p.down)
  have hL : germK (φ₀ ((jetAlgebra f κ).ofPiece V m x)) =
      MvPolynomial.eval₂ (germK.comp ρsh)
        (fun p => γ ^ (-(jetWeights.{u} X.toVariety.dim κ p : ℤ)) * c p)
        (ε ((jetAlgebra f κ).ofPiece V m x)) := by
    show germK (MvPolynomial.eval₂ ρsh (fun p => a p.down.1 p.down.2) (ε ((jetAlgebra f κ).ofPiece V m x))) = _
    rw [MvPolynomial.eval₂_comp_left]
    congr 1
    funext p
    have hw : ((jetWeights.{u} X.toVariety.dim κ p : ℕ) : ℤ) = ((p.down.2 : ℕ) : ℤ) + 1 := by
      simp [jetWeights]
    rw [hw]
    exact ha p.down.1 p.down.2
  have hR : affineJetCoord ρ ĵ hĵV m x =
      MvPolynomial.eval₂ (germK.comp ρsh) c (ε ((jetAlgebra f κ).ofPiece V m x)) := by
    rw [← hΞ m x]
    have key : Ξ.comp ε.symm.toRingHom = MvPolynomial.eval₂Hom (germK.comp ρsh) c := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
      · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
        show Ξ (ε.symm (MvPolynomial.C r)) = germK (ρsh r)
        rw [← hunit r, ε.symm_apply_apply]
        exact hΞC r
      · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
        show Ξ (ε.symm (MvPolynomial.X ⟨p.down⟩)) = c p
        rw [← hcoords p.down, ε.symm_apply_apply]
        exact hΞ _ _
    have hk := DFunLike.congr_fun key (ε ((jetAlgebra f κ).ofPiece V m x))
    rw [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      ε.symm_apply_apply] at hk
    exact hk
  rw [hL, hR]
  exact hPhom.eval₂_zpow_neg_weight _ (germK.comp ρsh) c γ

end jetNeighborhood

end
