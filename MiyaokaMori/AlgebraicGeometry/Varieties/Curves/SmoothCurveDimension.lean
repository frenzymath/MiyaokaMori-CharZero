import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SchemeOverResidue
import MiyaokaMori.RingTheory.Dimension.StandardSmoothCurveDimension
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.AlgebraicCycles
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Dimension of a curve smooth of relative dimension one over the field

The actual standard-smooth affine charts of the specified structure morphism have dimension one.
Their base opens are the whole spectrum of the field, and their coordinate rings are nonzero
because they contain the given point. An open-neighbourhood argument using irreducible closed
sets gives the global upper bound; nonemptiness of the original connected curve gives the lower
bound. Neither integrality nor projectivity is needed for these dimension arguments.

With an explicitly supplied integral-scheme instance, the closure of the canonical generic point
is the whole curve. Its dimension therefore supplies the dimension hypothesis for the original
seed's fundamental one-cycle. No instance or helper uses the pending integrality theorem.

Sources: Stacks, Morphisms, `definition-smooth-relative-dimension`; Topology,
`lemma-dimension-supremum-local-dimensions`.

The theorems are stated for an arbitrary scheme with a structure morphism `π : C ⟶ Spec k` smooth
of relative dimension one (`[SmoothOfRelativeDimension 1 π]`), with `[Nonempty C]` where
nonemptiness is needed; they are applied to `ProjectiveLine k ↘ Spec k`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme
open MiyaokaMori.RingTheory

universe u

/-- Open neighbourhoods with a common dimension bound bound the dimension of the whole space. -/
theorem dimension_le_of_open_neighborhoods
    {X : Type u} [TopologicalSpace X] (d : WithBot ℕ∞)
    (h : ∀ x : X, ∃ U : TopologicalSpace.Opens X,
      x ∈ U ∧ topologicalKrullDim U ≤ d) :
    topologicalKrullDim X ≤ d := by
  rw [topologicalKrullDim, Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun Z ↦ ?_
  obtain ⟨x, hx⟩ := Z.isIrreducible.nonempty
  obtain ⟨U, hxU, hU⟩ := h x
  let e := TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding
    (Subtype.val : U → X) U.isOpenEmbedding'
  let ZU := e.symm ⟨Z, ⟨⟨x, hxU⟩, hx⟩⟩
  have hZU :
      TopologicalSpace.IrreducibleCloseds.map
        (Subtype.val : U → X) U.isOpenEmbedding'.continuous ZU = Z := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨Z, ⟨⟨x, hxU⟩, hx⟩⟩)
  rw [← hZU, Topology.IsOpenEmbedding.coheight_map U.isOpenEmbedding' ZU]
  exact (Order.coheight_le_krullDim ZU).trans hU

variable {k : Type u} [Field k]

/-- Every point of a scheme smooth of relative dimension one over the field has an actual affine open
neighbourhood of dimension one. -/
theorem exists_affineOpen_dimension_one_of_smoothOfRelativeDimension
    {C : Scheme.{u}} (π : C ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 π] (x : C) :
    ∃ V : C.Opens, IsAffineOpen V ∧ x ∈ V ∧ topologicalKrullDim V = 1 := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := 1) (f := π) x
  have hUtop : U = ⊤ := by
    apply le_antisymm le_top
    intro y _
    have hy : y = π x := Subsingleton.elim _ _
    rw [hy]
    exact e hx
  subst U
  letI : Field Γ(Spec (CommRingCat.of k), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  have hd : ringKrullDim Γ(C, V) = 1 :=
    ringKrullDim_eq_one_of_standardSmooth
      Γ(Spec (CommRingCat.of k), ⊤) Γ(C, V) (π.appLE ⊤ V e).hom hf
  refine ⟨V, hV, hx, ?_⟩
  calc
    topologicalKrullDim V = topologicalKrullDim (Spec Γ(C, V)) :=
      IsHomeomorph.topologicalKrullDim_eq _ hV.isoSpec.hom.homeomorph.isHomeomorph
    _ = ringKrullDim Γ(C, V) := by
      change topologicalKrullDim (PrimeSpectrum Γ(C, V)) =
        ringKrullDim Γ(C, V)
      exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(C, V)
    _ = 1 := hd

/-- Smooth relative dimension one and nonemptiness give dimension one. -/
theorem topologicalKrullDim_eq_one_of_smoothOfRelativeDimension
    {C : Scheme.{u}} (π : C ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 π] [Nonempty C] :
    topologicalKrullDim C = 1 := by
  apply le_antisymm
  · apply dimension_le_of_open_neighborhoods 1
    intro x
    obtain ⟨V, _, hx, hV⟩ := exists_affineOpen_dimension_one_of_smoothOfRelativeDimension π x
    exact ⟨V, hx, hV.le⟩
  · obtain ⟨x⟩ := (inferInstance : Nonempty C)
    obtain ⟨V, _, _, hV⟩ := exists_affineOpen_dimension_one_of_smoothOfRelativeDimension π x
    rw [← hV]
    exact topologicalKrullDim_subspace_le C (V : Set C)

/-- Under an explicit integral-scheme instance the generic closure has the curve's dimension. -/
theorem genericPoint_closureDimension_eq_one_of_smoothOfRelativeDimension
    {C : Scheme.{u}} (π : C ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 π] [IsIntegral C] :
    Intersection.pointClosureDimension C (genericPoint C) = 1 := by
  rw [Intersection.pointClosureDimension_eq_topologicalKrullDim_closure, genericPoint_closure]
  exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ C)
    (Homeomorph.Set.univ C).isHomeomorph).trans
    (topologicalKrullDim_eq_one_of_smoothOfRelativeDimension π)

end AlgebraicGeometry.Scheme
