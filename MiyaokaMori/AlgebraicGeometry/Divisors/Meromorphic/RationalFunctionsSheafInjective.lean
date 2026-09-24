import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalFunctionsSheafSheafify

/-! # Injectivity of `O_X ⟶ 𝒦_X`

The map `O_X ⟶ 𝒦_X` from the structure sheaf to the sheaf of rational functions is injective on every
open.

Proof: `𝒦_X` is by definition the sheafification of the presheaf `P` of total quotient rings, and
`O_X ⟶ 𝒦_X` is `O_X ⟶ P` followed by the sheafification unit.
* `O_X ⟶ P` is injective on every open: Mathlib's `TopCat.Presheaf.instMonoToTotalQuotientPresheaf`
  (localization at the nonzerodivisors is injective).
* The sheafification unit `P ⟶ 𝒦_X` is locally injective (`Presheaf.isLocallyInjective_toSheafify`).
* `O_X` is a sheaf, so sections with equal germs are equal (`TopCat.Sheaf.section_ext`).

This is the key input for `O_X(D)` of a Cartier divisor being an invertible sheaf: it is the injectivity
of the local trivialization `r ↦ r·g⁻¹`. Source: Stacks 01X1 (`O_X ⊆ 𝒦_X` on an integral scheme); here for
any scheme.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `O_X(V) ⟶ P(V)` (the presheaf of total quotient rings) is injective. -/

theorem AlgebraicGeometry.Scheme.toTotalQuotientPresheaf_app_injective
    (X : AlgebraicGeometry.Scheme.{u}) (V : (X.Opens)ᵒᵖ) :
    Function.Injective (X.presheaf.toTotalQuotientPresheaf.app V).hom := by
  have hm : Mono (X.sheaf.presheaf.toTotalQuotientPresheaf) := inferInstance
  have hmv : Mono (X.presheaf.toTotalQuotientPresheaf.app V) :=
    (NatTrans.mono_iff_mono_app X.sheaf.presheaf.toTotalQuotientPresheaf).mp hm V
  exact (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp hmv

/-- `O_X ⟶ 𝒦_X` is injective on every open. -/

theorem AlgebraicGeometry.Scheme.toRationalFunctionsSheaf_app_injective
    (X : AlgebraicGeometry.Scheme.{u}) (U : X.Opens) :
    Function.Injective (X.toRationalFunctionsSheaf.hom.app (Opposite.op U)).hom := by
  intro s t hst
  have hst' :
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
            X.presheaf.totalQuotientPresheaf).app (Opposite.op U)
          ((X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom s) =
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
            X.presheaf.totalQuotientPresheaf).app (Opposite.op U)
          ((X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom t) := hst
  have hsieve := CategoryTheory.Presheaf.equalizerSieve_mem
    (J := Opens.grothendieckTopology X)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      X.presheaf.totalQuotientPresheaf)
    ((X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom s)
    ((X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom t) hst'
  apply TopCat.Presheaf.section_ext X.sheaf U s t
  intro x hx
  obtain ⟨V, f, hf, hxV⟩ := hsieve x hx
  have hnat : ∀ r : X.presheaf.obj (Opposite.op U),
      X.presheaf.totalQuotientPresheaf.map f.op
          ((X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom r) =
        (X.presheaf.toTotalQuotientPresheaf.app (Opposite.op V)).hom
          (X.presheaf.map f.op r) := by
    intro r
    exact (congrArg (fun q => q.hom r)
      (X.presheaf.toTotalQuotientPresheaf.naturality f.op)).symm
  have hres : X.presheaf.map f.op s = X.presheaf.map f.op t :=
    AlgebraicGeometry.Scheme.toTotalQuotientPresheaf_app_injective X (Opposite.op V)
      (((hnat s).symm.trans hf).trans (hnat t))
  have := congrArg (X.presheaf.germ V x hxV) hres
  rwa [X.presheaf.germ_res_apply f x hxV s, X.presheaf.germ_res_apply f x hxV t] at this

end
