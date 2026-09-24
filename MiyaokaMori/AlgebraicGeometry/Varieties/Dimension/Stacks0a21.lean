import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0a213
import MiyaokaMori.RingTheory.Dimension.FiniteTypeDomainHeightAddQuotientDim

/-! # Height plus coheight equals the dimension (Stacks 0A21 (4))

A consequence of Stacks 0A21 (4): in an integral scheme locally of finite type over a field, of
finite dimension `d`, every point `x` satisfies `dim closure {x} + dim O_{X,x} = d` (all maximal
chains of irreducible closed subsets have length `d`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The Krull dimension of the underlying space of a scheme (specialization preorder) is the
topological Krull dimension. -/
private theorem krullDim_scheme_eq_topologicalKrullDim (X : AlgebraicGeometry.Scheme.{u}) :
    Order.krullDim X = topologicalKrullDim X :=
  (Order.krullDim_eq_of_orderIso
    (@irreducibleSetEquivPoints X _ _ _ : IrreducibleCloseds X ≃o X)).symm

/-- On a prime spectrum, `dim A/𝔭` is the coheight of `𝔭` in `PrimeSpectrum A`. -/
private theorem ringKrullDim_quotient_eq_coheight {A : Type u} [CommRing A]
    (P : PrimeSpectrum A) :
    ringKrullDim (A ⧸ P.asIdeal) = (Order.coheight P : ℕ∞) := by
  have hset : PrimeSpectrum.zeroLocus (R := A) P.asIdeal = Set.Ici P := by
    ext q
    rw [PrimeSpectrum.mem_zeroLocus]
    exact Iff.rfl
  rw [ringKrullDim_quotient, hset, Order.coheight_eq_krullDim_Ici]

/-- An open immersion is strictly monotone for the specialization preorder, so it does not lower
the height of points. -/
private theorem height_le_height_of_isOpenImmersion {Y X : AlgebraicGeometry.Scheme.{u}}
    (g : Y ⟶ X) [AlgebraicGeometry.IsOpenImmersion g] (y : Y) :
    Order.height y ≤ Order.height (g y) := by
  refine Order.height_le_height_apply_of_strictMono _ (fun a b hab => ?_) y
  have hiff : ∀ a b : Y, g a ≤ g b ↔ a ≤ b := fun a b =>
    g.isOpenEmbedding.isInducing.specializes_iff
  rw [lt_iff_le_not_ge] at hab ⊢
  rwa [hiff, hiff]

/-- Stacks 0A21 (4): `height x + coheight x = dim X` for an integral scheme locally of finite type
over a field. -/
theorem AlgebraicGeometry.height_add_coheight_eq_of_locallyOfFiniteType {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (d : ℕ) (hd : topologicalKrullDim X = d) (x : X) :
    Order.height x + Order.coheight x = d := by
  -- (≤): height + coheight is at most the Krull dimension
  have hle : ((Order.height x + Order.coheight x : ℕ∞) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
    have : Nonempty X := ⟨x⟩
    rw [← hd, ← krullDim_scheme_eq_topologicalKrullDim,
      Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, WithBot.coe_le_coe]
    exact le_iSup (fun a : X => Order.height a + Order.coheight a) x
  -- (≥): take an affine open neighbourhood `U = Spec A` of `x`
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let f := X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
  let φ : k →+* Γ(X, U) :=
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ U le_top).hom
  have hφ : φ.FiniteType := by
    have h1 : (f.appLE ⊤ U le_top).hom.FiniteType :=
      f.finiteType_appLE (AlgebraicGeometry.isAffineOpen_top _) hU _
    have h2 : ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective
    exact h1.comp h2
  let _ : Algebra k Γ(X, U) := φ.toAlgebra
  have : Algebra.FiniteType k Γ(X, U) := hφ
  let P : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨x, hxU⟩
  -- dim A = dim U = dim X = d
  have hdimA : ringKrullDim Γ(X, U) = (d : WithBot ℕ∞) := by
    rw [← hd, ← AlgebraicGeometry.topologicalKrullDim_opens_eq_of_irreducible (k := k) X U
        ⟨x, hxU⟩,
      ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)]
    exact (IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph).symm
  -- coheight x = height 𝔭
  have hco : ((Order.coheight x : ℕ∞) : WithBot ℕ∞) = (P.asIdeal.height : WithBot ℕ∞) := by
    let _ : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
    have hloc := hU.isLocalization_stalk ⟨x, hxU⟩
    rw [← AlgebraicGeometry.ringKrullDim_stalk_eq_coheight x]
    exact IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal (X.presheaf.stalk x)
  -- dim A/𝔭 ≤ height x
  have hht : ringKrullDim (Γ(X, U) ⧸ P.asIdeal) ≤ ((Order.height x : ℕ∞) : WithBot ℕ∞) := by
    rw [ringKrullDim_quotient_eq_coheight, WithBot.coe_le_coe]
    have h1 : Order.coheight P = Order.height (show AlgebraicGeometry.Spec Γ(X, U) from P) := by
      rw [← Order.height_orderIso (AlgebraicGeometry.specOrderIsoPrimeSpectrum Γ(X, U))]
      rfl
    have := hU.isOpenImmersion_fromSpec
    have h2 := height_le_height_of_isOpenImmersion hU.fromSpec
      (show AlgebraicGeometry.Spec Γ(X, U) from P)
    rw [show hU.fromSpec (show AlgebraicGeometry.Spec Γ(X, U) from P) = x from
      hU.fromSpec_primeIdealOf ⟨x, hxU⟩] at h2
    exact h1.le.trans h2
  have hH := ringKrullDim_quotient_add_height_eq (k := k) Γ(X, U) P.asIdeal
  have hge : (d : WithBot ℕ∞) ≤ ((Order.height x + Order.coheight x : ℕ∞) : WithBot ℕ∞) := by
    rw [← hdimA, ← hH, WithBot.coe_add, hco]
    gcongr
  exact_mod_cast le_antisymm hle hge

end
