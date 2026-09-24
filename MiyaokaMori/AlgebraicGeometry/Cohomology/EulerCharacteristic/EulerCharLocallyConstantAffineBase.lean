import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexBaseChange
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.CechAltHomologyFinite
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharacteristic
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.FlatComplexFiberEulerChar
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt

/-! # Local constancy of the Euler characteristic over an affine base

Let `A` be a Noetherian ring, `f : X → Spec A` proper, and `M` coherent and flat over `A`. Then
`p ↦ χ_{κ(p)}(X_{κ(p)}, M_{κ(p)})` is a locally constant function on `Spec A`, where
`X_{κ(p)} = X ×_{Spec A} Spec κ(p)` and `M_{κ(p)}` is the pullback of `M` along the first projection.

Proof sketch:
1. `f` proper ⇒ `X` quasi-compact; take a finite affine open cover `U_1..U_n`
   (`isCompact_iff_finite_and_eq_biUnion_affineOpens`); `f` is separated.
2. Base change of the Čech complex: the alternating Čech complex `K^•` has flat terms, is nonzero only in
   degrees `[0, n)`, and for every `p` and `i ∈ ℕ`, `H^i(X_{κ(p)}, M_{κ(p)}) ≅ H^i(K^• ⊗_A κ(p))`
   (`κ(p)`-linearly).
3. `H^i(K^•)` is a finite `A`-module (`CechAltHomologyFinite.lean`).
4. `p ↦ Σ_{i<n} (−1)^i dim H^i(K^• ⊗ κ(p))` is locally constant (`FlatComplexFiberEulerChar.lean`).
5. `χ` is defined as a `finsum` over `ℕ`; for `i ≥ n`, `(K ⊗ κ(p))^i = 0`, so `H^i = 0` and the term
   vanishes; the `finsum` reduces to a finite sum over `range n`, which agrees pointwise with the function
   of step 4.

Source: the argument of Hartshorne III.12.2 + III.9.9; Stacks 07VK, 0B9T.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- A finite affine open cover: `X` is quasi-compact. -/
private theorem exists_fin_affine_cover (X : AlgebraicGeometry.Scheme.{u}) [CompactSpace X] :
    ∃ (n : ℕ) (U : Fin n → X.Opens), (∀ i, AlgebraicGeometry.IsAffineOpen (U i)) ∧ ⨆ i, U i = ⊤ := by
  obtain ⟨s, hs, hcov⟩ := (AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens
    (U := (⊤ : X.Opens))).mp (by simpa using isCompact_univ)
  have := hs.to_subtype
  let e := (Finite.equivFin s).symm
  refine ⟨Nat.card s, fun i => ((e i : s) : X.affineOpens), fun i => (e i : X.affineOpens).2, ?_⟩
  rw [hcov]
  apply le_antisymm
  · exact iSup_le fun i => le_iSup₂_of_le ((e i : s) : X.affineOpens) (e i).2 le_rfl
  · refine iSup₂_le fun V hV => ?_
    refine le_iSup_of_le (e.symm ⟨V, hV⟩) ?_
    show (V : X.Opens) ≤ ((e (e.symm ⟨V, hV⟩) : s) : X.affineOpens)
    rw [Equiv.apply_symm_apply]

/-- `χ_{κ(p)}(X_{κ(p)}, M_{κ(p)})`: `X ×_{Spec A} Spec κ(p)` viewed as a `κ(p)`-scheme via the second
projection, with `M` pulled back along the first projection. -/
def AlgebraicGeometry.baseChangeResidueFieldEulerChar {A : CommRingCat.{u}}
    {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec A) (M : X.Modules)
    (p : PrimeSpectrum A) : ℤ :=
  letI : (pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (algebraMap A p.asIdeal.ResidueField)))).Over
      (AlgebraicGeometry.Spec (CommRingCat.of p.asIdeal.ResidueField)) := ⟨pullback.snd _ _⟩
  AlgebraicGeometry.sheafEulerCharacteristic (k := p.asIdeal.ResidueField)
    (pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (algebraMap A p.asIdeal.ResidueField))))
    ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.fst f _)).obj M)

theorem AlgebraicGeometry.eulerChar_baseChange_residueField_isLocallyConstant
    {A : CommRingCat.{u}} [IsNoetherianRing A]
    {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec A) [AlgebraicGeometry.IsProper f]
    (M : X.Modules) [M.IsCoherent]
    (hM : AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.FlatOver f M) :
    IsLocallyConstant (AlgebraicGeometry.baseChangeResidueFieldEulerChar f M) := by
  have : CompactSpace X := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨n, U, hU, hcov⟩ := exists_fin_affine_cover X
  have : M.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
  obtain ⟨hflat, hbdd, hiso⟩ :=
    AlgebraicGeometry.cechComplexAlt_computes_baseChange f U hU hcov M hM
  have hfin := fun i => AlgebraicGeometry.cechComplexAlt_homology_finite f U hU hcov M hM i
  obtain ⟨-, hlc⟩ := CochainComplex.fiberEulerChar_isLocallyConstant _ n hflat hbdd hfin
  refine cast (congrArg IsLocallyConstant (funext fun p => ?_)) hlc
  symm
  -- the `finsum` of `χ` reduces to a finite sum over `range n`; use the Čech comparison isomorphism termwise
  let φ : A ⟶ CommRingCat.of p.asIdeal.ResidueField :=
    CommRingCat.ofHom (algebraMap A p.asIdeal.ResidueField)
  let _ : (pullback f (AlgebraicGeometry.Spec.map φ)).Over
      (AlgebraicGeometry.Spec (CommRingCat.of p.asIdeal.ResidueField)) := ⟨pullback.snd _ _⟩
  unfold AlgebraicGeometry.baseChangeResidueFieldEulerChar AlgebraicGeometry.sheafEulerCharacteristic
  rw [finsum_eq_sum_of_support_subset (s := Finset.range n)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨e⟩ := hiso (CommRingCat.of p.asIdeal.ResidueField) φ i
    rw [e.finrank_eq]
  · intro i hi
    by_contra hin
    have hni : (n : ℤ) ≤ (i : ℤ) := by
      have : ¬ i < n := by simpa using hin
      exact_mod_cast not_lt.mp this
    obtain ⟨e⟩ := hiso (CommRingCat.of p.asIdeal.ResidueField) φ i
    refine hi ?_
    have hz : IsZero ((((ModuleCat.extendScalars φ.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj _).X (i : ℤ)) :=
      (ModuleCat.extendScalars φ.hom).map_isZero (hbdd (i : ℤ) (Or.inr hni))
    have hz' := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
      (HomologicalComplex.ExactAt.of_isZero hz)
    have hsub := ModuleCat.isZero_iff_subsingleton.mp hz'
    have : Subsingleton _ := e.toEquiv.subsingleton
    simp [Module.finrank_zero_of_subsingleton]

end
