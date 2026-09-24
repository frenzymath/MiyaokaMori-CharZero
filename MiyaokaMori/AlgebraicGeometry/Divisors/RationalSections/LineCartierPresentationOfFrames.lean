import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrame
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineRationalSectionCartier

/-! # Cartier presentations from frames

Let `X` be integral and locally Noetherian, `M` an `O_X`-module sheaf and `A` a `CartierLocalData`. If on
every `A.opens i` a frame `e_i` of `M` is given (`IsFrame`), and an element `s` of the generic stalk
satisfies `s = A.equation i • (e_i)_η` for every nonempty `A.opens i`, then there is a Cartier presentation
`P : LineCartierPresentation X M s` with `P.cartier = A`. Also, `nonemptyPart` removes the empty opens
from Cartier data without changing the equations.

Proof:
1. A frame gives `M|_{U_i} ≅ O_{U_i}` (`IsFrame.restrictIso`, taking coordinates and sending `e_i` to `1`),
   composed with `O ≅ free(Fin 1)`.
2. `lineStalkEquivOfTrivialization_germ` computes the generic coordinate as the germ of the coordinate
   section, so the coordinate of `(e_i)_η` is `1` and that of `s` is `A.equation i` (the coordinate map is
   `K(X)`-linear).
3. `s ≠ 0` because its coordinate `A.equation i` on a chart containing the generic point is nonzero.
Source: Hartshorne II.6.13.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.LineCartierPresentationOfFrames

open AlgebraicGeometry.Divisors AlgebraicGeometry.Proj

set_option backward.isDefEq.respectTransparency false

section Frame

variable {X : Scheme.{u}} [IsIntegral X] {M : X.Modules} {U : X.Opens} {e : Γ(M, U)}

/-- The rank-one trivialization `M|_U ≅ free(Fin 1)` given by a frame. -/
def frameIso (hf : Scheme.Modules.IsFrame M U e) :
    M.restrict U.ι ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)) :=
  hf.restrictIso ≪≫ (LineGenericCoordinates.moduleFreeOneIsoUnit U.toScheme).symm

omit [IsIntegral X] in
theorem frameIso_trans_hom (hf : Scheme.Modules.IsFrame M U e) :
    (frameIso hf ≪≫ LineGenericCoordinates.moduleFreeOneIsoUnit U.toScheme).hom =
      hf.restrictIso.hom := by
  simp [frameIso]

/-- The germ of the frame element at the generic point has coordinate `1` in the trivialization given by the
frame. -/
theorem genericCoordinate_frameIso_germ (hf : Scheme.Modules.IsFrame M U e) (hU : Nonempty U) :
    LineGenericCoordinates.genericCoordinate X M U hU (frameIso hf)
      (M.presheaf.germ U (genericPoint X)
        (LineGenericCoordinates.genericPoint_mem_of_nonempty X U hU) e) = 1 := by
  have hη := LineGenericCoordinates.genericPoint_mem_of_nonempty X U hU
  have h1 : M.presheaf.germ U (genericPoint X) hη e =
      M.presheaf.germ (U.ι ''ᵁ ⊤) (genericPoint X) ⟨⟨genericPoint X, hη⟩, trivial, rfl⟩
        (show Γ(M.restrict U.ι, ⊤) from M.res (Scheme.Modules.image_ι_le U ⊤) e) :=
    (M.presheaf.germ_res_apply (homOfLE (Scheme.Modules.image_ι_le U ⊤)) (genericPoint X) _ e).symm
  rw [h1]
  unfold LineGenericCoordinates.genericCoordinate
  rw [LineGenericCoordinates.lineStalkEquivOfTrivialization_germ X M U ⟨genericPoint X, hη⟩
    (frameIso hf) ⊤ trivial, frameIso_trans_hom, hf.restrictIso_hom_app_frame ⊤]
  exact map_one _

end Frame

/-- Remove the empty opens from Cartier local data. -/
def nonemptyPart {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (A : Intersection.CartierLocalData X) : Intersection.CartierLocalData X where
  index := {i : A.index // Nonempty (A.opens i)}
  opens i := A.opens i.1
  cover := by
    refine Set.eq_univ_of_forall fun x => ?_
    exact Set.mem_iUnion.mpr ⟨⟨A.indexAt x, ⟨⟨x, A.indexAt_mem x⟩⟩⟩, A.indexAt_mem x⟩
  locallyFinite := A.locallyFinite.comp_injective Subtype.val_injective
  equation i := A.equation i.1
  equation_ne_zero i := A.equation_ne_zero i.1
  ratio_unit i j := A.ratio_unit i.1 j.1

variable {k : Type u} [Field k]

/-- Frames together with "the coordinate of `s` in each frame is the local equation" give a presentation with
Cartier data `A`. -/
theorem exists_presentation_of_frames (X : SchemeOver k) [IsIntegral X.scheme]
    [IsLocallyNoetherian X.scheme] (M : X.scheme.Modules)
    (A : Intersection.CartierLocalData X.scheme)
    (e : ∀ i, Γ(M, A.opens i)) (he : ∀ i, Scheme.Modules.IsFrame M (A.opens i) (e i))
    (s : M.presheaf.stalk (genericPoint X.scheme))
    (hs : ∀ i (hU : Nonempty (A.opens i)), s =
      (A.equation i : X.scheme.presheaf.stalk (genericPoint X.scheme)) •
        M.presheaf.germ (A.opens i) (genericPoint X.scheme)
          (LineGenericCoordinates.genericPoint_mem_of_nonempty X.scheme (A.opens i) hU) (e i)) :
    ∃ P : LineCartierPresentation X M s, P.cartier = A := by
  have hcoord : ∀ i (hU : Nonempty (A.opens i)), A.equation i =
      LineGenericCoordinates.genericCoordinate X.scheme M (A.opens i) hU (frameIso (he i)) s := by
    intro i hU
    have h := congrArg
      (LineGenericCoordinates.genericCoordinate X.scheme M (A.opens i) hU (frameIso (he i))) (hs i hU)
    rw [h, map_smul, genericCoordinate_frameIso_germ (he i) hU]
    exact (mul_one _).symm
  refine ⟨{ section_ne_zero := ?_, cartier := A, frame := fun i => frameIso (he i),
            equation_eq := hcoord }, rfl⟩
  intro h0
  let i := A.indexAt (genericPoint X.scheme)
  have hU : Nonempty (A.opens i) := ⟨⟨_, A.indexAt_mem _⟩⟩
  have h := hcoord i hU
  rw [h0, map_zero] at h
  exact A.equation_ne_zero i h

end MiyaokaMori.LineCartierPresentationOfFrames

end
