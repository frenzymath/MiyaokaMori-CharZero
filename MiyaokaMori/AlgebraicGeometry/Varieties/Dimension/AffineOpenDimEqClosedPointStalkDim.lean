import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Dimension.FiniteTypeIrreducibleMaximalHeight

/-! # Dimension of an affine open equals the dimension of the stalk at a closed point

Let `k` be a field, `X` an irreducible scheme locally of finite type over `k` (not necessarily
reduced or separated), `V ⊆ X` an affine open and `z ∈ V` a closed point of `X`. Then
`dim V = dim O_{X,z}`.

Proof sketch:
1. `A = Γ(X, V)` is a finitely generated `k`-algebra (`Scheme.Hom.finiteType_appLE` composed with
   `k ≅ Γ(Spec k, ⊤)`, `Scheme.ΓSpecIso`).
2. `V ≅ Spec A` is a homeomorphism (`IsAffineOpen.isoSpec`), so `dim V = dim Spec A = dim A`
   (`IsHomeomorph.topologicalKrullDim_eq`, `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`).
3. `X` is irreducible, so the nonempty open `V` is irreducible (`IsPreirreducible.open_subset`),
   hence `Spec A` is irreducible, i.e. the nilradical of `A` is prime
   (`PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`).
4. `z` is closed in `X`, hence in `V`; under the homeomorphism the corresponding prime
   `𝔪 = hV.primeIdealOf z` is a closed point of `Spec A`, i.e. a maximal ideal
   (`PrimeSpectrum.isClosed_singleton_iff_isMaximal`).
5. `O_{X,z} = A_𝔪` (`IsAffineOpen.isLocalization_stalk`) and `dim A_𝔪 = height 𝔪`
   (`IsLocalization.AtPrime.ringKrullDim_eq_height`).
6. `height 𝔪 = dim A` by the irreducible (not necessarily reduced) version of Stacks 00OS.

Source: the local step in the proof of Stacks 0A21 (3).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- For an irreducible scheme locally of finite type over a field, the dimension of an affine open
equals the Krull dimension of the stalk at any closed point of `X` lying in it. -/
theorem topologicalKrullDim_affineOpen_eq_ringKrullDim_stalk_of_isClosed {k : Type u} [Field k]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [IrreducibleSpace X] (V : X.Opens) (hV : IsAffineOpen V) (z : X) (hzV : z ∈ V)
    (hz : IsClosed ({z} : Set X)) :
    topologicalKrullDim V = ringKrullDim (X.presheaf.stalk z) := by
  let f := X ↘ Spec (CommRingCat.of k)
  let φ : k →+* Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom
  have hφ : φ.FiniteType := by
    have h1 : (f.appLE ⊤ V le_top).hom.FiniteType :=
      f.finiteType_appLE (isAffineOpen_top _) hV _
    have h2 : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective
    exact h1.comp h2
  let _ : Algebra k Γ(X, V) := φ.toAlgebra
  have : Algebra.FiniteType k Γ(X, V) := hφ
  let h := hV.isoSpec.hom.homeomorph
  have hirrV : IrreducibleSpace V := by
    refine Subtype.irreducibleSpace ⟨⟨z, hzV⟩, ?_⟩
    exact (IrreducibleSpace.isIrreducible_univ X).isPreirreducible.open_subset V.2
      (Set.subset_univ _)
  have hirr : IrreducibleSpace (PrimeSpectrum Γ(X, V)) :=
    h.surjective.irreducibleSpace h.continuous
  have hN : (nilradical Γ(X, V)).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp hirr
  have hmax : (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.IsMaximal := by
    rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    have hset : ({⟨z, hzV⟩} : Set V) = Subtype.val ⁻¹' ({z} : Set X) := by
      ext y
      exact ⟨fun hy => congrArg Subtype.val (Set.mem_singleton_iff.mp hy), fun hy => Subtype.ext (Set.mem_singleton_iff.mp hy)⟩
    have hzV' : IsClosed ({⟨z, hzV⟩} : Set V) := by
      rw [hset]; exact hz.preimage continuous_subtype_val
    have himg : h '' {⟨z, hzV⟩} = {hV.primeIdealOf ⟨z, hzV⟩} := Set.image_singleton
    have hcl := h.isClosedMap _ hzV'
    rw [himg] at hcl
    exact hcl
  let _ : Algebra Γ(X, V) (X.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨z, hzV⟩ : V)
  have hloc := hV.isLocalization_stalk ⟨z, hzV⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hV.primeIdealOf ⟨z, hzV⟩).asIdeal
      (X.presheaf.stalk z),
    Ideal.height_eq_ringKrullDim_of_isMaximal_of_isPrime_nilradical (k := k) Γ(X, V) hN,
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, V)]
  exact IsHomeomorph.topologicalKrullDim_eq _ h.isHomeomorph

end AlgebraicGeometry

end
