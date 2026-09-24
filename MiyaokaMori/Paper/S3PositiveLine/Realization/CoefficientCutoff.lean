import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.CoefficientSections
import MiyaokaMori.Paper.S3PositiveLine.Realization.NonnegDegreeVanishing
import MiyaokaMori.Paper.S3PositiveLine.Realization.R0GeOne

/-! # Coefficient cutoff

The ambient coefficients `B_{ℓ,q} = J.coefficient ℓ q ∈ H⁰(C̃, ρ^*A ⊗ L^{-q})` of a based jet
`J : C̃_(κ)(L) → 𝒵` (4.1) and the cutoff
`r_k = ⌊a·deg ρ / deg L⌋` (in Lean the integer division
`A.degree * ρ.degree / L.degree` with `A = f^*O_X(1)`, which is the floor because `deg L > 0`).

* `BasedJet.mul_degree_le_of_coefficient_ne_zero`: a nonzero `B_{ℓ,q}` forces
  `q·deg L ≤ a·deg ρ` (a line bundle of negative degree on a smooth projective curve has no nonzero
  global section, `coefficient_degree_bound`).
* `BasedJet.coefficient_eq_zero_of_gt_r0`: `B_{ℓ,q} = 0` for `q > r_k` — item (i) of
  Lemma 4.1.
* `BasedJet.one_le_r0_of_not_genericallyScalar`: if `J` is not generically scalar, some `B_{ℓ,q}`
  with `q ≥ 1` is nonzero (`jet_coefficient_ne_zero_of_not_scalar`), so `deg L ≤ q·deg L ≤ a·deg ρ` and
  `r_k ≥ 1` ("some positive-order coefficient survives").

The only technical point is that `J.coefficient ℓ q` lives in `((ρ^*A)^{⊗1} ⊗ L^{-q})` (the
`zpow 1` spelling of `BasedJet.coefficient`), while `coefficient_degree_bound` /
`coefficient_eq_zero_of_gt_r0` take sections of `ρ^*A ⊗ L^{-q}`; `coefficientTransport` is the
canonical isomorphism between the two (`LineBundle.zpowOneIso` tensored with the identity), and an
isomorphism of modules sends a global section to `0` iff it is `0`
(`coefficientTransport_map_eq_zero_iff`). This is the transport used by `realization` and by `R0Bound`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The canonical identification `(B^{⊗1} ⊗ L^{-q}) ≅ (B ⊗ L^{-q})` of the underlying modules of two
spellings of the coefficient bundle (`LineBundle.zpowOneIso` on the first factor). -/
def coefficientTransport {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (B L : LineBundle C.toVariety) (q : ℕ) :
    ((B.zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules ≅
      (B.tensor (L.zpow (-(q : ℤ)))).toModules :=
  (CategoryTheory.eqToIso (LineBundle.tensor_toModules (B.zpow 1) (L.zpow (-(q : ℤ))))) ≪≫
    ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
        (B.zpow 1).toModules (L.zpow (-(q : ℤ))).toModules) ≪≫
      (CategoryTheory.MonoidalCategory.tensorIso B.zpowOneIso (CategoryTheory.Iso.refl _)) ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj B.toModules
        (L.zpow (-(q : ℤ))).toModules).symm) ≪≫
    (CategoryTheory.eqToIso (LineBundle.tensor_toModules B (L.zpow (-(q : ℤ))))).symm

/-- An isomorphism of sheaves of modules sends a global section to `0` iff the section is `0`. -/
theorem modules_iso_app_top_eq_zero_iff {k : Type u} [Field k]
    {Y : AlgebraicGeometry.Scheme} {M N : Y.Modules} (τ : M ≅ N)
    (x : (M.val.obj (Opposite.op ⊤) : Type u)) :
    (τ.hom.val.app (Opposite.op ⊤)).hom x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hcomp := congrArg (fun g => (g.val.app (Opposite.op ⊤)).hom x) τ.hom_inv_id
    change (τ.inv.val.app (Opposite.op ⊤)).hom
        ((τ.hom.val.app (Opposite.op ⊤)).hom x) = x at hcomp
    rw [hx, map_zero] at hcomp
    exact hcomp.symm
  · intro hx
    rw [hx, map_zero]

/-- **A nonzero ambient coefficient bounds its order**: if `B_{ℓ,q} = J.coefficient ℓ q ≠ 0` then
`q · deg L ≤ deg(f^*O_X(1)) · deg ρ` (the coefficient bundle
`ρ^*A ⊗ L^{-q}` has degree `a·deg ρ − q·deg L`, and a line bundle of negative degree has no nonzero
global section). -/
theorem BasedJet.mul_degree_le_of_coefficient_ne_zero {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (ℓ : Fin (X.embDim + 1)) (q : ℕ) (hq : J.coefficient ℓ q ≠ 0) :
    (q : ℤ) * L.degree ≤
      (LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree * (ρ.degree : ℤ) := by
  let A : LineBundle C.toVariety := LineBundle.pullback (X := C.toVariety) f (X.OX 1)
  let B : LineBundle ρ.source.toVariety := LineBundle.pullback ρ.hom A
  let c' : ((B.tensor (L.zpow (-(q : ℤ)))).toModules.val.obj (Opposite.op ⊤) : Type u) :=
    ((coefficientTransport B L q).hom.val.app (Opposite.op ⊤)).hom (J.coefficient ℓ q)
  have hc' : c' ≠ 0 := by
    intro hz
    exact hq ((modules_iso_app_top_eq_zero_iff (k := k) (Y := ρ.source.toScheme)
      (coefficientTransport B L q) (J.coefficient ℓ q)).mp hz)
  exact coefficient_degree_bound A ρ L q c' hc'

/-- **Item (i) of Lemma 4.1**:
the ambient coefficients of order `q > r_k = ⌊a·deg ρ / deg L⌋` vanish, because
`deg(ρ^*A ⊗ L^{-q}) = a·deg ρ − q·deg L < 0`. Stated for every `q > r_k` (for `q > κ` the
coefficient is `0` by the definition of `xiCoefficientThickening` anyway), which covers the
paper's range `r_k < q ≤ k`. -/
theorem BasedJet.coefficient_eq_zero_of_gt_r0 {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (hL : 0 < L.degree) (ℓ : Fin (X.embDim + 1)) (q : ℕ)
    (hq : (LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree * (ρ.degree : ℤ) / L.degree
      < (q : ℤ)) :
    J.coefficient ℓ q = 0 := by
  by_contra hne
  have hbound := BasedJet.mul_degree_le_of_coefficient_ne_zero J ℓ q hne
  have hle : (q : ℤ) ≤
      (LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree * (ρ.degree : ℤ) / L.degree :=
    (Int.le_ediv_iff_mul_le hL).2 hbound
  exact (not_le_of_gt hq) hle

/-- **A surviving positive-order coefficient.** A based jet that is not generically scalar has a
nonzero ambient coefficient `B_{ℓ,q}` with `1 ≤ q ≤ κ` (`jet_coefficient_ne_zero_of_not_scalar`,
restated with `q : ℕ` in the paper's range). -/
theorem BasedJet.exists_coefficient_ne_zero_of_not_genericallyScalar {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (hns : ¬ J.IsGenericallyScalar) :
    ∃ (ℓ : Fin (X.embDim + 1)) (q : ℕ), 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0 := by
  obtain ⟨ℓ, q, hq⟩ := jet_coefficient_ne_zero_of_not_scalar J hns
  exact ⟨ℓ, (q : ℕ) + 1, by omega, by omega, hq⟩

/-- **`r_k ≥ 1`**: a based jet that is not generically scalar
has a nonzero coefficient of some order `q ≥ 1`, so `deg L ≤ q·deg L ≤ a·deg ρ`
(`BasedJet.mul_degree_le_of_coefficient_ne_zero`) and the floor `⌊a·deg ρ / deg L⌋` is at least `1`
(`r0_ge_one`). -/
theorem BasedJet.one_le_r0_of_not_genericallyScalar {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (hL : 0 < L.degree) (hns : ¬ J.IsGenericallyScalar) :
    1 ≤ (LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree * (ρ.degree : ℤ) / L.degree := by
  obtain ⟨ℓ, q, hq1, -, hne⟩ := BasedJet.exists_coefficient_ne_zero_of_not_genericallyScalar J hns
  have hbound := BasedJet.mul_degree_le_of_coefficient_ne_zero J ℓ q hne
  have hq1' : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq1
  have hmul : L.degree ≤ (q : ℤ) * L.degree := by nlinarith
  exact r0_ge_one hL (le_trans hmul hbound)

end
