import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldEqResidueFieldAtGenericPoint
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.DominantAffineAlgebraic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Finite function field extension and the generic fiber

Stacks Project, Tag 02NX ((2) ⇔ (4)): for a dominant morphism, locally of finite type, between
integral schemes, the function field extension is finite if and only if the generic point of the
source is the only point mapping to the generic point of the target. (Used to see that a nonconstant
map between curves has degree at least one, Lemma 5.1 of the paper.)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open Classical in
theorem AlgebraicGeometry.functionField_finite_iff_generic_fiber {X Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y] (f : X ⟶ Y)
    [AlgebraicGeometry.LocallyOfFiniteType f] (hf : f.base (genericPoint X) = genericPoint Y) :
    (f.residueFieldMap (genericPoint X)).hom.Finite ↔
      f.base ⁻¹' {f.base (genericPoint X)} = {genericPoint X} := by
  constructor
  · intro hfin
    apply Set.Subset.antisymm
    · intro x hx
      have hfx : f.base x = genericPoint Y := by
        have hfx' : f.base x = f.base (genericPoint X) := by simpa using hx
        exact hfx'.trans hf
      obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open
          (Set.mem_univ (genericPoint Y)) isOpen_univ
      letI : Nonempty U := ⟨⟨genericPoint Y, hηU⟩⟩
      have hfxU : f.base x ∈ U := by rw [hfx]; exact hηU
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hfxU (f ⁻¹ᵁ U).isOpen
      letI : Nonempty V := ⟨⟨x, hxV⟩⟩
      have hηV : genericPoint X ∈ V :=
        AlgebraicGeometry.genericPoint_mem_of_nonempty V ⟨x, hxV⟩
      letI : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
      have halg : Algebra.IsAlgebraic Γ(Y, U) Γ(X, V) :=
        AlgebraicGeometry.appLE_isAlgebraic_of_genericPoint f hfin hU V hVU hηV
      let q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
      have hqcomap : q.comap (f.appLE U V hVU).hom = ⊥ := by
        have hcomap := AlgebraicGeometry.IsAffineOpen.comap_primeIdealOf_appLE
          (f := f) U hU V hV hVU hxV
        have htarget :
            (hU.primeIdealOf ⟨f.base x, hVU hxV⟩).asIdeal = ⊥ := by
          have hpoint : (⟨f.base x, hVU hxV⟩ : U) = ⟨genericPoint Y, hηU⟩ :=
            Subtype.ext hfx
          rw [hpoint, hU.primeIdealOf_genericPoint,
            genericPoint_eq_bot_of_affine]
          rfl
        exact (congrArg PrimeSpectrum.asIdeal hcomap).trans htarget
      have hqbot : q = ⊥ := by
        apply le_antisymm
        · intro b hb
          by_contra hb0
          exact (Ideal.comap_ne_bot_of_algebraic_mem hb0 hb
            (halg.isAlgebraic b)) hqcomap
        · exact bot_le
      have hqgen : hV.primeIdealOf ⟨x, hxV⟩ =
          genericPoint (AlgebraicGeometry.Spec Γ(X, V)) := by
        apply PrimeSpectrum.ext
        rw [genericPoint_eq_bot_of_affine]
        exact hqbot
      have hηprime := hV.primeIdealOf_genericPoint
      have hp : hV.primeIdealOf ⟨x, hxV⟩ =
          hV.primeIdealOf ⟨genericPoint X, hηV⟩ := hqgen.trans hηprime.symm
      have hp' := congrArg hV.fromSpec hp
      show x = genericPoint X
      simpa only [hV.fromSpec_primeIdealOf] using hp'
    · intro x hx
      have hx' : x = genericPoint X := by simpa only [Set.mem_singleton_iff] using hx
      subst x
      simpa only [Set.mem_preimage, Set.mem_singleton_iff, hf]
  · intro hfiber
    have hopen : IsOpen ({f.asFiber (genericPoint X)} :
        Set (f.fiber (f.base (genericPoint X)))) := by
      have hall : ({f.asFiber (genericPoint X)} :
          Set (f.fiber (f.base (genericPoint X)))) = Set.univ := by
        ext z
        simp only [Set.mem_singleton_iff, Set.mem_univ, iff_true]
        apply (f.fiberι (f.base (genericPoint X))).isEmbedding.injective
        rw [f.fiberι_asFiber]
        have hz : f.fiberι (f.base (genericPoint X)) z ∈
            f.base ⁻¹' {f.base (genericPoint X)} := by
          rw [← f.range_fiberι]
          exact Set.mem_range_self z
        have hz' : f.fiberι (f.base (genericPoint X)) z ∈
            ({genericPoint X} : Set X) := by
          rwa [← hfiber]
        simpa only [Set.mem_singleton_iff] using hz'
      rw [hall]
      exact isOpen_univ
    have hqf : f.QuasiFiniteAt (genericPoint X) :=
      Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr hopen
    change (f.stalkMap (genericPoint X)).hom.QuasiFinite at hqf
    let e := Y.presheaf.stalkCongr (.of_eq hf.symm)
    have heqf : e.hom.hom.QuasiFinite :=
      RingHom.QuasiFinite.of_finite e.commRingCatIsoToRingEquiv.finite
    have hgqf : (e.hom ≫ f.stalkMap (genericPoint X)).hom.QuasiFinite := by
      exact RingHom.QuasiFinite.comp hqf heqf
    have hgfin : (e.hom ≫ f.stalkMap (genericPoint X)).hom.Finite := by
      letI := (e.hom ≫ f.stalkMap (genericPoint X)).hom.toAlgebra
      letI : Algebra.QuasiFinite
          (Y.presheaf.stalk (genericPoint Y)) (X.presheaf.stalk (genericPoint X)) := hgqf
      exact Module.Finite.of_quasiFinite
    have hstalk : (f.stalkMap (genericPoint X)).hom.Finite := by
      exact RingHom.Finite.of_comp_finite hgfin
    have hsourceResidue : (X.residue (genericPoint X)).hom.Finite :=
      RingHom.Finite.of_surjective _ (X.residue_surjective (genericPoint X))
    have hcomp : ((X.residue (genericPoint X)).hom.comp
        (f.stalkMap (genericPoint X)).hom).Finite :=
      RingHom.Finite.comp hsourceResidue hstalk
    have hcomp' : ((f.residueFieldMap (genericPoint X)).hom.comp
        (Y.residue (f.base (genericPoint X))).hom).Finite := by
      have heq := congrArg CommRingCat.Hom.hom
        (AlgebraicGeometry.Scheme.residue_residueFieldMap f (genericPoint X))
      simp only [CommRingCat.hom_comp] at heq
      rw [heq]
      exact hcomp
    exact RingHom.Finite.of_comp_finite hcomp'

end
