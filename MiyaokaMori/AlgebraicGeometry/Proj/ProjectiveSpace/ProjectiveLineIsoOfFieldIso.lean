import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLine
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjMapToSpecZero

/-! # The projective line along an isomorphism of fields

An isomorphism of fields `φ : K ≅ L` induces an isomorphism `P¹_K ≅ P¹_L` compatible with the
structure morphisms: `e ≫ (P¹_L → Spec L) = (P¹_K → Spec K) ≫ Spec φ⁻¹`.

Source: Stacks 01N2 (functoriality of `Proj`: a graded ring homomorphism `A → B` satisfying the
irrelevant-ideal condition induces `Proj B → Proj A`; here `A = L[T₀,T₁]`, `B = K[T₀,T₁]` and the
homomorphism is `MvPolynomial.map φ⁻¹`).

Use: the exceptional fibre of a point blow-up is `P¹_{κ(p)}` over the residue field `κ(p)`
(Stacks 0AGQ), whereas a smooth rational curve is required to be `P¹_k` over `k`; when `k` is
algebraically closed and `p` is a closed point, `κ(p) ≅ k` (Mathlib `residueFieldIsoBase`), and
this module transports `P¹` along that isomorphism.

Proof: `Proj.map` (Mathlib) along `MvPolynomial.map` gives morphisms in both directions, inverse
to each other by `Proj.map_comp`/`Proj.map_id`; the compatibility with the structure morphisms is
`proj_map_toSpecZero` (`Proj.map ≫ toSpecZero = toSpecZero ≫ Spec f₀`) followed by the comparison
of degree-zero parts `(R[T])₀ ≅ R` (`MvPolynomial.map_C`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `MvPolynomial.map f` as a graded ring homomorphism for the standard total-degree grading. -/
def MvPolynomial.gradedMap {R S : Type u} [CommRing R] [CommRing S] (σ : Type v) (f : R →+* S) :
    MvPolynomial.homogeneousSubmodule σ R →+*ᵍ MvPolynomial.homogeneousSubmodule σ S where
  __ := MvPolynomial.map f
  map_mem {i x} hx := by
    rw [MvPolynomial.mem_homogeneousSubmodule] at hx ⊢
    exact hx.map f

theorem MvPolynomial.gradedMap_apply {R S : Type u} [CommRing R] [CommRing S] (σ : Type v)
    (f : R →+* S) (x : MvPolynomial σ R) :
    MvPolynomial.gradedMap σ f x = MvPolynomial.map f x := rfl

theorem MvPolynomial.gradedMap_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (σ : Type v) (f : R →+* S) (g : S →+* T) :
    (MvPolynomial.gradedMap σ g).comp (MvPolynomial.gradedMap σ f) =
      MvPolynomial.gradedMap σ (g.comp f) := by
  refine GradedRingHom.ext fun x => ?_
  show MvPolynomial.map g (MvPolynomial.map f x) = MvPolynomial.map (g.comp f) x
  rw [MvPolynomial.map_map]

theorem MvPolynomial.gradedMap_id {R : Type u} [CommRing R] (σ : Type v) :
    MvPolynomial.gradedMap σ (RingHom.id R) = GradedRingHom.id _ := by
  refine GradedRingHom.ext fun x => ?_
  show MvPolynomial.map (RingHom.id R) x = x
  rw [MvPolynomial.map_id]

/-- A surjective graded homomorphism satisfies the irrelevant-ideal condition of `Proj.map`
(only the case of a graded one-sided inverse is needed here). -/
theorem MvPolynomial.irrelevant_le_map_gradedMap {R S : Type u} [CommRing R] [CommRing S]
    (σ : Type v) (f : R →+* S) (g : S →+* R) (hfg : ∀ s, f (g s) = s) :
    HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule σ S) ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule σ R)).map
        (MvPolynomial.gradedMap σ f) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi x hx
  have hx' : (x : MvPolynomial σ S) ∈ MvPolynomial.homogeneousSubmodule σ S i := hx
  have hgx : MvPolynomial.map g x ∈ MvPolynomial.homogeneousSubmodule σ R i := by
    rw [MvPolynomial.mem_homogeneousSubmodule] at hx' ⊢
    exact hx'.map g
  have hx_eq : MvPolynomial.gradedMap σ f (MvPolynomial.map g x) = x := by
    have hcomp : f.comp g = RingHom.id S := RingHom.ext hfg
    rw [MvPolynomial.gradedMap_apply, MvPolynomial.map_map, hcomp, MvPolynomial.map_id]
  show x ∈ ((HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule σ R)).map
    (MvPolynomial.gradedMap σ f)).toIdeal
  rw [HomogeneousIdeal.toIdeal_map, ← hx_eq]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ hi hgx)

end

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem proj_map_congr' {R S : Type u} [CommRing R] [CommRing S] {σ : Type v}
    {f g : MvPolynomial.homogeneousSubmodule σ R →+*ᵍ MvPolynomial.homogeneousSubmodule σ S}
    (e : f = g)
    (hf : HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule σ S) ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule σ R)).map f)
    (hg : HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule σ S) ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule σ R)).map g) :
    AlgebraicGeometry.Proj.map f hf = AlgebraicGeometry.Proj.map g hg := by
  subst e; rfl

/-- **Transport of `P¹` along a field isomorphism**: `φ : K ≅ L` (an isomorphism in `CommRingCat`)
gives `P¹_K ≅ P¹_L` with `e ≫ (P¹_L ↘ Spec L) = (P¹_K ↘ Spec K) ≫ Spec.map φ.inv`. -/
theorem ProjectiveLine.exists_iso_of_fieldIso {K L : Type u} [Field K] [Field L]
    (φ : CommRingCat.of K ≅ CommRingCat.of L) :
    ∃ e : ProjectiveLine K ≅ ProjectiveLine L,
      e.hom ≫ (ProjectiveLine L ↘ AlgebraicGeometry.Spec (CommRingCat.of L)) =
        (ProjectiveLine K ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) ≫
          AlgebraicGeometry.Spec.map φ.inv := by
  -- ψ : K → L and ψ' : L → K are mutually inverse
  set ψ : K →+* L := φ.hom.hom with hψ
  set ψ' : L →+* K := φ.inv.hom with hψ'
  have h1 : ∀ x, ψ' (ψ x) = x := fun x => by
    change (φ.hom ≫ φ.inv).hom x = x
    rw [φ.hom_inv_id]; rfl
  have h2 : ∀ x, ψ (ψ' x) = x := fun x => by
    change (φ.inv ≫ φ.hom).hom x = x
    rw [φ.inv_hom_id]; rfl
  -- graded homomorphisms L[T] → K[T] (for e.hom) and K[T] → L[T] (for e.inv)
  have hf' := MvPolynomial.irrelevant_le_map_gradedMap (Fin 2) ψ' ψ h1
  have hg' := MvPolynomial.irrelevant_le_map_gradedMap (Fin 2) ψ ψ' h2
  have hcompK : (MvPolynomial.gradedMap (Fin 2) ψ').comp (MvPolynomial.gradedMap (Fin 2) ψ) =
      GradedRingHom.id (MvPolynomial.homogeneousSubmodule (Fin 2) K) := by
    rw [MvPolynomial.gradedMap_comp, ← MvPolynomial.gradedMap_id (R := K) (Fin 2)]
    congr 1
    exact RingHom.ext h1
  have hcompL : (MvPolynomial.gradedMap (Fin 2) ψ).comp (MvPolynomial.gradedMap (Fin 2) ψ') =
      GradedRingHom.id (MvPolynomial.homogeneousSubmodule (Fin 2) L) := by
    rw [MvPolynomial.gradedMap_comp, ← MvPolynomial.gradedMap_id (R := L) (Fin 2)]
    congr 1
    exact RingHom.ext h2
  have hom_inv : AlgebraicGeometry.Proj.map (MvPolynomial.gradedMap (Fin 2) ψ') hf' ≫
      AlgebraicGeometry.Proj.map (MvPolynomial.gradedMap (Fin 2) ψ) hg' =
      𝟙 (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) := by
    rw [← AlgebraicGeometry.Proj.map_comp, proj_map_congr' hcompK _ (by simp)]
    exact AlgebraicGeometry.Proj.map_id
  have inv_hom : AlgebraicGeometry.Proj.map (MvPolynomial.gradedMap (Fin 2) ψ) hg' ≫
      AlgebraicGeometry.Proj.map (MvPolynomial.gradedMap (Fin 2) ψ') hf' =
      𝟙 (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) L)) := by
    rw [← AlgebraicGeometry.Proj.map_comp, proj_map_congr' hcompL _ (by simp)]
    exact AlgebraicGeometry.Proj.map_id
  let e : ProjectiveLine K ≅ ProjectiveLine L :=
    { hom := AlgebraicGeometry.Proj.map (MvPolynomial.gradedMap (Fin 2) ψ') hf'
      inv := AlgebraicGeometry.Proj.map (MvPolynomial.gradedMap (Fin 2) ψ) hg'
      hom_inv_id := hom_inv
      inv_hom_id := inv_hom }
  refine ⟨e, ?_⟩
  show AlgebraicGeometry.Proj.map (MvPolynomial.gradedMap (Fin 2) ψ') hf' ≫
      (AlgebraicGeometry.Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) L) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (algebraMap L (MvPolynomial.homogeneousSubmodule (Fin 2) L 0)))) =
    (AlgebraicGeometry.Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) K) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (algebraMap K (MvPolynomial.homogeneousSubmodule (Fin 2) K 0)))) ≫
      AlgebraicGeometry.Spec.map φ.inv
  rw [← Category.assoc, AlgebraicGeometry.Proj.proj_map_toSpecZero (MvPolynomial.gradedMap (Fin 2) ψ') hf',
    Category.assoc, Category.assoc,
    ← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro l
  apply Subtype.ext
  show ((MvPolynomial.gradedMap (Fin 2) ψ').gradedZeroRingHom
    (algebraMap L (MvPolynomial.homogeneousSubmodule (Fin 2) L 0) l) : MvPolynomial (Fin 2) K) =
    (algebraMap K (MvPolynomial.homogeneousSubmodule (Fin 2) K 0) (ψ' l) : MvPolynomial (Fin 2) K)
  simp [MvPolynomial.gradedMap_apply, MvPolynomial.algebraMap_eq]

end
