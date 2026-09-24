import MiyaokaMori.Prelude
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Homology and restriction of scalars

Let `a' : A' → B` be a homomorphism of commutative rings, `C` a cochain complex of `B`-modules and
`L` a cochain complex of `A'`-modules with `L ≅ C_{A'}` (`C` with scalars restricted along `a'`
termwise). If `H` is a `B`-module carrying a compatible `A'`-module structure (`t • x = a'(t) • x`)
and `H ≃ H^i(C)` `B`-linearly, then `H ≃ H^i(L)` `A'`-linearly.

Proof: restriction of scalars is an exact functor and hence commutes with homology,
`H^i(C_{A'}) ≅ (H^i(C))_{A'}`; a `B`-linear isomorphism is automatically `A'`-linear for the
compatible `A'`-structures.

Reference: standard homological algebra (exact functors commute with homology; Weibel 1.6; Mathlib's
`ShortComplex.mapHomologyIso`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u w

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- A `B`-linear identification `H ≃ H^i(C)` yields an `A'`-linear identification `H ≃ H^i(L)` when
`L ≅ C_{A'}` and the `A'`-action on `H` is the one induced along `a'`.

Proof sketch: `ModuleCat.restrictScalars a'` is both a left and a right adjoint, hence exact and
homology-preserving, so `H^i(C_{A'}) ≅ (H^i C)_{A'}` (`ShortComplex.mapHomologyIso`); `χ` gives
`H^i(L) ≅ H^i(C_{A'})`; and `r` is `A'`-linear for the restricted structure by `hsmul` together with
the `B`-linearity of `r`. -/
theorem ModuleCat.nonempty_linearEquiv_homology_of_restrictScalars_iso {A' B : Type u}
    [CommRing A'] [CommRing B] (a' : A' →+* B)
    (C : CochainComplex (ModuleCat.{u} B) ℤ) (L : CochainComplex (ModuleCat.{u} A') ℤ)
    (χ : L ≅ ((ModuleCat.restrictScalars a').mapHomologicalComplex _).obj C) (i : ℤ)
    {H : Type w} [AddCommGroup H] [Module B H] [Module A' H]
    (hsmul : ∀ (t : A') (x : H), t • x = a' t • x)
    (r : H ≃ₗ[B] C.homology i) :
    Nonempty (H ≃ₗ[A'] L.homology i) := by
  have e1 : L.homology i ≅
      (((ModuleCat.restrictScalars a').mapHomologicalComplex _).obj C).homology i :=
    (HomologicalComplex.homologyFunctor _ _ i).mapIso χ
  have e2 : (((ModuleCat.restrictScalars a').mapHomologicalComplex _).obj C).homology i ≅
      (ModuleCat.restrictScalars a').obj (C.homology i) :=
    (C.sc i).mapHomologyIso (ModuleCat.restrictScalars a')
  let r' : H ≃ₗ[A'] ↑((ModuleCat.restrictScalars a').obj (C.homology i)) :=
    { r.toAddEquiv with
      map_smul' := fun t x => by
        show r (t • x) = a' t • r x
        rw [hsmul, map_smul] }
  exact ⟨r'.trans (e2.symm ≪≫ e1.symm).toLinearEquiv⟩

end
