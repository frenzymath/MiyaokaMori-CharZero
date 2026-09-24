import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffCartierCanonical
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimensionFinite
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOfNowhereZeroTuple
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.PointClosureKrullDim
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.Stacks0bcn

/-! # Dimension of an effective Cartier divisor, and the trivial divisor

The projective step of the comparison of Snapper's intersection number with the Chow-theoretic one
(Stacks 0BFI, second half) needs, for an effective Cartier divisor `D` on the integral proper `X` of
dimension `d + 1`:

* `EffectiveCartierDivisor.toScheme_dimension_eq`: if `D ≠ ∅` (i.e. `I_D ≠ O_X`) then `dim D = d`.
  Proof: the underlying space of `D` is the closed subset `V(I_D)`; heights of its points are
  computed in `X` (`Scheme.Hom.height_of_isClosedImmersion`). Every point lies below a maximal
  point (the generic point of an irreducible component, `Scheme.exists_le_isMax`); a maximal point
  of `D` has coheight `1` in `X` (Krull's Hauptidealsatz, Stacks 0BCN,
  `EffectiveCartierDivisor.coheight_eq_one_of_isMax`), hence height `d` by
  `height + coheight = dim X` for finite type over a field (Stacks 0A21,
  `Scheme.height_eq_of_coheight_eq_one`). So `sup height = d`, i.e. `topologicalKrullDim D = d`.
  Here `height x = dim closure {x}` (`x ≤ y ↔ y ⤳ x`, `Scheme.le_iff_specializes`).
* `EffectiveCartierDivisor.nonempty_lineBundle_iso_unit_of_eq_top`: if `I_D = O_X` then
  `O_X(D) ≅ O_X`. Proof: the canonical section `1_D` is a frame on all of `X`: on every affine open
  `W` with a frame `e` of `O_X(D)`, the coordinate of `1_D` generates `I_D(W) = Γ(X, W)`
  (`EffCartier.one_isZeroIdeal`), so it is a unit and `1_D|_W` is a frame
  (`IsFrame.of_isUnit_coord`); frames glue (`IsFrame.of_iSup`); a global frame trivialises
  (`IsFrame.topTrivialization`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- Every point of a scheme lies below a maximal point: the generic point of an irreducible
component containing it (`x ≤ y ↔ y ⤳ x`, so maximal points are generic points of components). -/
theorem Scheme.exists_le_isMax (Y : Scheme.{u}) (ξ : Y) : ∃ ξ' : Y, ξ ≤ ξ' ∧ IsMax ξ' := by
  have hirr : IsIrreducible (irreducibleComponent ξ) := isIrreducible_irreducibleComponent
  have hcl : IsClosed (irreducibleComponent ξ) := isClosed_irreducibleComponent
  have hgen : IsGenericPoint hirr.genericPoint (irreducibleComponent ξ) :=
    hirr.isGenericPoint_genericPoint hcl
  refine ⟨hirr.genericPoint, ?_, ?_⟩
  · rw [Scheme.le_iff_specializes]
    exact hgen.specializes mem_irreducibleComponent
  · intro y hy
    rw [Scheme.le_iff_specializes] at hy ⊢
    have h1 : irreducibleComponent ξ ⊆ closure ({y} : Set Y) := by
      rw [← hgen.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hy))
        isClosed_closure
    have h2 : closure ({y} : Set Y) = irreducibleComponent ξ :=
      eq_irreducibleComponent isIrreducible_singleton.closure.isPreirreducible h1
    rw [specializes_iff_mem_closure, hgen.def, ← h2]
    exact subset_closure rfl

/-- **Dimension of a nonempty effective Cartier divisor** on an integral scheme proper over `k` of
dimension `d + 1`: `dim D = d` (Stacks 0BCN + 0A21; see the module docstring). -/
theorem EffectiveCartierDivisor.toScheme_dimension_eq {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] (hX : IsProperOver k X) [IsIntegral X]
    [IsLocallyNoetherian X] {d : ℕ} (hd : X.dimension = d + 1) (D : EffectiveCartierDivisor X)
    (hD : D.idealSheaf ≠ ⊤) : D.toScheme.dimension = d := by
  have hprop : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
  have hft : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k)) := hprop.toLocallyOfFiniteType
  have hdim : topologicalKrullDim X = ((d + 1 : ℕ) : WithBot ℕ∞) := by
    rw [X.topologicalKrullDim_eq_dimension (topologicalKrullDim_ne_top_of_isProperOver X hX), hd]
  -- maximal points of `D` have height `d` in `X`, hence in `D`
  have hmax : ∀ ξ : D.toScheme, IsMax ξ → Order.height ξ = (d : ℕ∞) := by
    intro ξ hξ
    rw [← D.idealSheaf.subschemeι.height_of_isClosedImmersion ξ]
    exact Scheme.height_eq_of_coheight_eq_one (X ↘ Spec (CommRingCat.of k)) hdim
      (D.coheight_eq_one_of_isMax ξ hξ)
  have hle : ∀ ξ : D.toScheme, Order.height ξ ≤ (d : ℕ∞) := by
    intro ξ
    obtain ⟨ξ', hle, hmax'⟩ := D.toScheme.exists_le_isMax ξ
    rw [← hmax ξ' hmax']
    exact Order.height_mono hle
  -- `D` is nonempty
  have hne : Nonempty D.toScheme := by
    have hsupp : (D.idealSheaf.support : Set X) ≠ ∅ := by
      intro h
      apply hD
      rw [← Scheme.IdealSheafData.support_eq_bot_iff]
      exact TopologicalSpace.Closeds.ext h
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hsupp
    rw [← Scheme.IdealSheafData.range_subschemeι] at hx
    obtain ⟨ξ, -⟩ := hx
    exact ⟨ξ⟩
  have hkrull : topologicalKrullDim D.toScheme = ((d : ℕ) : WithBot ℕ∞) := by
    rw [← krullDim_eq_topologicalKrullDim, Order.krullDim_eq_iSup_height_of_nonempty]
    have : (⨆ ξ : D.toScheme, Order.height ξ) = (d : ℕ∞) := by
      obtain ⟨ξ₀⟩ := hne
      obtain ⟨ξ', -, hmax'⟩ := D.toScheme.exists_le_isMax ξ₀
      exact le_antisymm (iSup_le hle) (le_iSup_of_le ξ' (hmax ξ' hmax').ge)
    rw [this]
    rfl
  unfold Scheme.dimension
  rw [hkrull]
  simp

/-- If `I_D = O_X` (i.e. `D = ∅`), the canonical section `1_D` is a frame of `O_X(D)` on all of `X`. -/
theorem EffectiveCartierDivisor.isFrame_canonicalSection_of_eq_top {X : Scheme.{u}}
    (D : EffectiveCartierDivisor X) (hD : D.idealSheaf = ⊤) :
    Scheme.Modules.IsFrame D.lineBundle ⊤ D.canonicalSection := by
  classical
  have key : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      Scheme.Modules.IsFrame D.lineBundle W (D.lineBundle.res le_top D.canonicalSection) := by
    intro x
    obtain ⟨W, hW, -, hxW, e, he⟩ :=
      Scheme.Modules.exists_affine_frame_le D.lineBundle (U := ⊤) (p := x) trivial
    refine ⟨W, hxW, he.of_isUnit_coord ?_⟩
    have h1 := Scheme.EffCartier.one_isZeroIdeal D ⟨W, hW⟩ e he
    rw [← Ideal.span_singleton_eq_top, ← h1]
    change D.idealSheaf.ideal ⟨W, hW⟩ = ⊤
    rw [hD]
    rfl
  choose W hxW hfr using key
  exact Scheme.Modules.IsFrame.of_iSup W (fun _ => le_top)
    (fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩) hfr

/-- `D = ∅` (i.e. `I_D = O_X`) ⇒ `O_X(D) ≅ O_X` (the canonical section trivialises). -/
theorem EffectiveCartierDivisor.nonempty_lineBundle_iso_unit_of_eq_top {X : Scheme.{u}}
    (D : EffectiveCartierDivisor X) (hD : D.idealSheaf = ⊤) :
    Nonempty (D.lineBundle ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :=
  ⟨(D.isFrame_canonicalSection_of_eq_top hD).topTrivialization.symm⟩

end AlgebraicGeometry

end
