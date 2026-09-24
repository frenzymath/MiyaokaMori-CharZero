import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.NormalizedTupleNowhereZero
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ConeCoordinateFiniteXiExpansionSectionExt
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ConeCoordinateFiniteXiExpansionConstantMonomial
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ConeCoordinateFiniteXiExpansionZeroSection
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ConeCoordinateFiniteXiExpansionSeedCoordinate

/-! # The finite `ξ`-expansion of the cone coordinates of a based jet

Every cone coordinate of a truncated jet based over a finite cover `ρ` equals the restriction of the pullback of
the seed coordinate to the total space of the line bundle, plus a finite sum of `ξ`-monomials of orders `1` to `κ`;
the coefficients of the monomials are `BasedJet.coefficient` (equation (4.1) of
Lemma 4.1 of the paper).

Proof (by comparison of coefficients):
1. A section on the thickening is determined by its `κ + 1` `ξ`-coefficients: `jetNeighborhood_section_ext`
   (`…SectionExt`).
2. Take the coefficients of the right-hand side termwise: `xiCoefficientThickening` is additive
   (`xiCoefficientThickening_add/sum`); `xiCoefficient_restrictToThickening` (restriction does not change the
   coefficients for `q ≤ κ`, `ThickeningSectionsTruncated`) turns each term into an `xiCoefficient` on `Tot(L)`;
   `sectionPullbackAlong_totalSpace_eq_xiMonomial_zero` (`…ConstantMonomial`) writes `π^*(ρ^*f_ℓ)` as a monomial of
   degree `0`; `xiCoefficient_xiMonomial` (`TotSectionsPolynomial`) computes the coefficients of a monomial: a
   monomial of order `q` is nonzero only in the `q`-th coefficient.
3. The `q ≥ 1`-th coefficient of the left-hand side is `J.coefficient ℓ q` by definition (`rfl`); the `0`-th
   coefficient equals `ρ^*f_ℓ` by `xiCoefficientThickening_zero_eq_restrictToZeroSection` (`…ZeroSection`) and
   `BasedJet.restrictToZeroSection_coneCoordinate` (`…SeedCoordinate`, from `BasedJet.restrict`).
4. The variable-level lemma `thickening_section_expansion_of_zero_coefficient` assembles everything; the concrete
   statement follows from it by a single `exact`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The `q`-th `ξ`-coefficient of `c·ξ^q` is `c` (the `dif_pos` branch of `xiCoefficient_xiMonomial`). -/
theorem xiCoefficient_xiMonomial_self {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) (q : ℕ)
    (c : ((((M.zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u)) :
    xiCoefficient L M (xiMonomial L M q c) q = c := by
  rw [xiCoefficient_xiMonomial, dif_pos rfl]

/-- The `q'`-th `ξ`-coefficient of `c·ξ^q` is `0` for `q' ≠ q` (the `dif_neg` branch of `xiCoefficient_xiMonomial`). -/
theorem xiCoefficient_xiMonomial_of_ne {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) {q q' : ℕ} (h : q ≠ q')
    (c : ((((M.zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u)) :
    xiCoefficient L M (xiMonomial L M q c) q' = 0 := by
  rw [xiCoefficient_xiMonomial, dif_neg h]

/-- **The expansion at variable level**: if the `0`-th `ξ`-coefficient of a section `P` on the thickening is `s₀`
(through `coefficientZeroIso⁻¹`), then
`P = restrict(π^*s₀) + Σ_{q<κ} restrict((the (q+1)-th coefficient of P)·ξ^{q+1})`.

Proof: by `jetNeighborhood_section_ext` it suffices to compare the coefficients for every `q ≤ κ`. On the
right-hand side, `xiCoefficientThickening_add/sum`, `xiCoefficient_restrictToThickening` and
`sectionPullbackAlong_totalSpace_eq_xiMonomial_zero` reduce to
`xiCoefficient (s₀·ξ^0) q + Σ_{q'} xiCoefficient (c_{q'+1}·ξ^{q'+1}) q`; for `q = 0`,
`xiCoefficient_xiMonomial_self/of_ne` give `s₀ + 0`, matching the hypothesis `h0`; for `q = q'+1` one gets
`0 + c_{q'+1}` (`Finset.sum_eq_single ⟨q', _⟩`), which is the left-hand side by definition.
The lemma is stated at variable level so that the two nested `LineBundle.pullback`s of the concrete line bundle
`ρ^* f^* O_X(1)` never enter the motive of a `rw` (see the explanation in `SeedBundlePullback.lean`). -/
theorem thickening_section_expansion_of_zero_coefficient {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (κ : ℕ)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
      M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (s₀ : (M.toModules.val.obj (Opposite.op ⊤) : Type u))
    (h0 : xiCoefficientThickening L M κ 0 P
      = ((coefficientZeroIso L M).inv.val.app (Opposite.op ⊤)).hom s₀) :
    P = restrictToThickening L M κ
          (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom s₀)
        + ∑ q : Fin κ, restrictToThickening L M κ
            (xiMonomial L M ((q : ℕ) + 1) (xiCoefficientThickening L M κ ((q : ℕ) + 1) P)) := by
  apply jetNeighborhood_section_ext L M κ
  intro q hq
  rw [xiCoefficientThickening_add, xiCoefficientThickening_sum,
    xiCoefficient_restrictToThickening L M κ q hq,
    sectionPullbackAlong_totalSpace_eq_xiMonomial_zero L M s₀]
  simp only [xiCoefficient_restrictToThickening L M κ q hq]
  rcases q with _ | q'
  · rw [xiCoefficient_xiMonomial_self, h0, Finset.sum_eq_zero, add_zero]
    intro i _
    exact xiCoefficient_xiMonomial_of_ne L M (Nat.succ_ne_zero _) _
  · rw [xiCoefficient_xiMonomial_of_ne L M (Nat.zero_ne_add_one q'), zero_add]
    have hq' : q' < κ := Nat.lt_of_succ_le hq
    rw [Finset.sum_eq_single ⟨q', hq'⟩]
    · exact (xiCoefficient_xiMonomial_self L M (q' + 1) _).symm
    · intro i _ hi
      apply xiCoefficient_xiMonomial_of_ne
      intro hcontra
      apply hi
      ext
      exact Nat.succ_injective hcontra
    · intro habs
      exact absurd (Finset.mem_univ _) habs

/-- **Equation (4.1)**: `P_ℓ^{(κ)} = restrict(π^*ρ^*f_ℓ) + Σ_{q=1}^{κ} restrict(c_{ℓ,q} ξ^q)` with
`c_{ℓ,q} = J.coefficient ℓ q`. Apply the variable-level lemma `thickening_section_expansion_of_zero_coefficient` with
`P` = the cone coordinate and `s₀ = ρ^*f_ℓ`; the hypothesis on the `0`-th coefficient comes from
`xiCoefficientThickening_zero_eq_restrictToZeroSection` and `BasedJet.restrictToZeroSection_coneCoordinate`;
`J.coefficient ℓ (q+1)` and `xiCoefficientThickening … (q+1) (coneCoordinate J ℓ)` agree by definition (`rfl`).
Source: Lemma 4.1 of the paper. -/
theorem BasedJet.coneCoordinate_finite_xi_expansion {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (ℓ : Fin (X.embDim + 1)) :
    BasedJet.coneCoordinate J ℓ
      = restrictToThickening L
          (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
            (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))) κ
          (sectionPullbackAlong
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
            (sectionPullbackAlong ρ.hom
            ((((AlgebraicGeometry.Scheme.Modules.pullback f).map
              (CategoryTheory.eqToHom (X.OX_toModules 1).symm)).val.app (Opposite.op ⊤)).hom
                (D.coord ℓ))))
        + ∑ q : Fin κ,
            restrictToThickening L
              (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
                (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))) κ
              (xiMonomial L
                (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
                  (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1)))
                ((q : ℕ) + 1) (BasedJet.coefficient J ℓ ((q : ℕ) + 1))) :=
  thickening_section_expansion_of_zero_coefficient L
    (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))) κ
    (BasedJet.coneCoordinate J ℓ)
    (sectionPullbackAlong ρ.hom
      ((((AlgebraicGeometry.Scheme.Modules.pullback f).map
        (CategoryTheory.eqToHom (X.OX_toModules 1).symm)).val.app (Opposite.op ⊤)).hom
          (D.coord ℓ)))
    (by rw [xiCoefficientThickening_zero_eq_restrictToZeroSection,
          BasedJet.restrictToZeroSection_coneCoordinate]
        rfl)

end
