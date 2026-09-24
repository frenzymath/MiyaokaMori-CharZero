import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SchemeOverResidue
import Mathlib.Tactic.Ring
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace

/-!
# Local coordinates of a homogeneous tuple on the canonical projective line

On `D₊(Hᵢ)`, the equal-degree fraction `Hₗ/Hᵢ` gives an actual structure-sheaf
section. On the intersection with `D₊(Hⱼ)`, the fractions `Hⱼ²/(HᵢHⱼ)` and
`Hᵢ²/(HᵢHⱼ)` are inverse units and give the common change of coordinates.
All fractions, units, and restriction identities are constructed directly.

The homogeneous degree may be zero and some coordinates may vanish identically.
No affine-chart isomorphism requiring positive degree is used. These local data
are on the existing `ProjectiveSpace 1 k`; a cover, the global morphism, its affine
comparison, and its pullback of O(1) are separate obligations.

Sources: Theorem 4.2 of the paper (§4); Stacks Project, `constructions.tex`,
`lemma-proj-scheme` and its degree-zero localization restriction calculation.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry.Proj.HomogeneousTupleLocalCoordinates

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {N d : ℕ}
    (H : Fin (N + 1) → MvPolynomial (Fin 2) k)
    (hH : ∀ i, (H i).IsHomogeneous d)

/-- The original Proj basic open where the selected homogeneous coordinate does not vanish. -/
def coordinateOpen (i : Fin (N + 1)) : (ProjectiveSpace 1 k).Opens :=
  Proj.basicOpen (projectiveGrading k 1) (H i)

/-- The actual homogeneous localization fraction `Hₗ/Hᵢ`. -/
def ratioElement (i l : Fin (N + 1)) : Away (projectiveGrading k 1) (H i) :=
  Away.mk (projectiveGrading k 1) (hH i) 1 (H l) (by simpa using hH l)

/-- A coordinate divided by itself is one, including on an empty coordinate open. -/
theorem ratioElement_self (i : Fin (N + 1)) : ratioElement H hH i i = 1 := by
  apply HomogeneousLocalization.val_injective
  simp [ratioElement, Away.val_mk]

/-- The numerator `Hₗ²` over `HᵢHⱼ`, used for both directions of a frame change. -/
def squareRatio (i j l : Fin (N + 1)) :
    Away (projectiveGrading k 1) (H i * H j) :=
  Away.mk (projectiveGrading k 1) ((hH i).mul (hH j)) 1 (H l ^ 2)
    (by simpa [pow_two] using (hH l).mul (hH l))

/-- The two displayed square fractions are inverse by an actual localization calculation. -/
theorem squareRatio_mul_reverse (i j : Fin (N + 1)) :
    squareRatio H hH i j j * squareRatio H hH i j i = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [squareRatio, HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    Away.val_mk, pow_one, Localization.mk_mul]
  rw [← Localization.mk_one]
  apply Localization.mk_eq_mk_iff.mpr
  apply Localization.r_of_eq
  simp only [Submonoid.coe_mul, Submonoid.coe_one, one_mul, mul_one]
  ring

/-- The real unit `Hⱼ/Hᵢ` on the homogeneous localization of the intersection. -/
def transitionElement (i j : Fin (N + 1)) :
    (Away (projectiveGrading k 1) (H i * H j))ˣ where
  val := squareRatio H hH i j j
  inv := squareRatio H hH i j i
  val_inv := squareRatio_mul_reverse H hH i j
  inv_val := (mul_comm _ _).trans (squareRatio_mul_reverse H hH i j)

/-- The equal-degree fractions satisfy the coordinate change after actual localization maps. -/
theorem ratioElement_overlap (i j l : Fin (N + 1)) :
    awayMap (projectiveGrading k 1) (hH j) rfl (ratioElement H hH i l) =
      (transitionElement H hH i j : Away (projectiveGrading k 1) (H i * H j)) *
        awayMap (projectiveGrading k 1) (hH i) (mul_comm (H i) (H j))
          (ratioElement H hH j l) := by
  apply HomogeneousLocalization.val_injective
  simp only [ratioElement, awayMap_mk, transitionElement, squareRatio,
    HomogeneousLocalization.val_mul, Away.val_mk, pow_one, Localization.mk_mul]
  apply Localization.mk_eq_mk_iff.mpr
  apply Localization.r_of_eq
  simp only [Submonoid.coe_mul]
  ring

/-- The coordinate fraction as an actual section of the projective-line structure sheaf. -/
def ratioSection (i l : Fin (N + 1)) :
    Γ(ProjectiveSpace 1 k, coordinateOpen H i) :=
  Proj.awayToSection (projectiveGrading k 1) (H i) (ratioElement H hH i l)

/-- The selected coordinate section is one. -/
theorem ratioSection_self (i : Fin (N + 1)) : ratioSection H hH i i = 1 := by
  simp [ratioSection, ratioElement_self]

/-- The homogeneous localization over the product maps to the actual intersection sections. -/
def intersectionSectionMap (i j : Fin (N + 1)) :
    CommRingCat.of (Away (projectiveGrading k 1) (H i * H j)) ⟶
      Γ(ProjectiveSpace 1 k, coordinateOpen H i ⊓ coordinateOpen H j) :=
  Proj.awayToSection (projectiveGrading k 1) (H i * H j) ≫
    (ProjectiveSpace 1 k).presheaf.map
      (homOfLE (Proj.basicOpen_mul (projectiveGrading k 1) (H i) (H j)).ge).op

private theorem awayToIntersection_left (i j : Fin (N + 1)) :
    CommRingCat.ofHom (awayMap (projectiveGrading k 1) (hH j) rfl) ≫
        intersectionSectionMap H i j =
      Proj.awayToSection (projectiveGrading k 1) (H i) ≫
        (ProjectiveSpace 1 k).presheaf.map
          (homOfLE (inf_le_left : coordinateOpen H i ⊓ coordinateOpen H j ≤ _)).op := by
  unfold intersectionSectionMap
  dsimp only [ProjectiveSpace, ProjectiveSpaceOver]
  rw [← Category.assoc, Proj.awayMap_awayToSection, Category.assoc, ← Functor.map_comp]
  rfl

private theorem awayToIntersection_right (i j : Fin (N + 1)) :
    CommRingCat.ofHom
        (awayMap (projectiveGrading k 1) (hH i) (mul_comm (H i) (H j))) ≫
        intersectionSectionMap H i j =
      Proj.awayToSection (projectiveGrading k 1) (H j) ≫
        (ProjectiveSpace 1 k).presheaf.map
          (homOfLE (inf_le_right : coordinateOpen H i ⊓ coordinateOpen H j ≤ _)).op := by
  unfold intersectionSectionMap
  dsimp only [ProjectiveSpace, ProjectiveSpaceOver]
  rw [← Category.assoc, Proj.awayMap_awayToSection, Category.assoc, ← Functor.map_comp]
  rfl

/-- The actual invertible structure-sheaf section changing the two local coordinate frames. -/
def transitionSection (i j : Fin (N + 1)) :
    Γ(ProjectiveSpace 1 k, coordinateOpen H i ⊓ coordinateOpen H j)ˣ :=
  Units.map (intersectionSectionMap H i j).hom (transitionElement H hH i j)

/-- Restricting either coordinate tuple to its intersection gives the same tuple up to its unit. -/
theorem ratioSection_overlap (i j l : Fin (N + 1)) :
    (ProjectiveSpace 1 k).presheaf.map (homOfLE inf_le_left).op
        (ratioSection H hH i l) =
      (transitionSection H hH i j :
          Γ(ProjectiveSpace 1 k, coordinateOpen H i ⊓ coordinateOpen H j)) *
        (ProjectiveSpace 1 k).presheaf.map (homOfLE inf_le_right).op
          (ratioSection H hH j l) := by
  have hl := congrArg (fun f ↦ f (ratioElement H hH i l))
    (awayToIntersection_left H hH i j)
  have hr := congrArg (fun f ↦ f (ratioElement H hH j l))
    (awayToIntersection_right H hH i j)
  change intersectionSectionMap H i j
      (awayMap (projectiveGrading k 1) (hH j) rfl (ratioElement H hH i l)) =
    (ProjectiveSpace 1 k).presheaf.map (homOfLE inf_le_left).op
      (ratioSection H hH i l) at hl
  change intersectionSectionMap H i j
      (awayMap (projectiveGrading k 1) (hH i) (mul_comm (H i) (H j))
        (ratioElement H hH j l)) =
    (ProjectiveSpace 1 k).presheaf.map (homOfLE inf_le_right).op
      (ratioSection H hH j l) at hr
  rw [← hl, ← hr, ratioElement_overlap, map_mul]
  rfl

/-- Transfer to the open subschemes commutes with the actual restriction of sections. -/
theorem topIso_inv_restrict {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V)
    (s : Γ(X, V)) :
    (X.homOfLE h).appTop (V.topIso.inv s) =
      U.topIso.inv (X.presheaf.map (homOfLE h).op s) := by
  have hmap : V.topIso.inv ≫ (X.homOfLE h).appTop =
      X.presheaf.map (homOfLE h).op ≫ U.topIso.inv := by
    simp only [Scheme.Opens.topIso_inv, Scheme.homOfLE_appTop, ← Functor.map_comp]
    rfl
  exact congrArg (fun f ↦ f s) hmap

/-- The same fraction on the whole open subscheme, via its genuine global-section isomorphism. -/
def localCoordinate (i l : Fin (N + 1)) : Γ((coordinateOpen H i).toScheme, ⊤) :=
  (coordinateOpen H i).topIso.inv (ratioSection H hH i l)

/-- The selected global coordinate of each open subscheme is one. -/
theorem localCoordinate_self (i : Fin (N + 1)) : localCoordinate H hH i i = 1 := by
  simp [localCoordinate, ratioSection_self]

/-- The transition unit as a global section on the actual intersection subscheme. -/
def localTransition (i j : Fin (N + 1)) :
    Γ((coordinateOpen H i ⊓ coordinateOpen H j).toScheme, ⊤)ˣ :=
  Units.map ((coordinateOpen H i ⊓ coordinateOpen H j).topIso.inv.hom)
    (transitionSection H hH i j)

/-- Open-subscheme pullback gives the common-unit compatibility required by projective gluing. -/
theorem localCoordinate_overlap (i j l : Fin (N + 1)) :
    ((ProjectiveSpace 1 k).homOfLE inf_le_left).appTop (localCoordinate H hH i l) =
      (localTransition H hH i j :
          Γ((coordinateOpen H i ⊓ coordinateOpen H j).toScheme, ⊤)) *
        ((ProjectiveSpace 1 k).homOfLE inf_le_right).appTop
          (localCoordinate H hH j l) := by
  simp only [localCoordinate, topIso_inv_restrict]
  rw [ratioSection_overlap, map_mul]
  rfl

end AlgebraicGeometry.Proj.HomogeneousTupleLocalCoordinates
