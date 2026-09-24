import MiyaokaMori.Prelude

/-! # The local ring of a fiber at a point

Stacks Project, Tag 0HA1: for `f : X → S` and `x ∈ X` mapping to `s`, the local ring of the fiber
`X_s` at `x` is `O_{X,x}/m_s O_{X,x}` (used as in the proof of Debarre, *Higher-Dimensional
Algebraic Geometry*, 6.11).

## Route: no affine reduction

Write `O := 𝒪_{X,x}`, `R := 𝒪_{S,f x}`, `φ := f.stalkMap x : R → O`, `I := φ(𝔪_R) O`, `B := O/I`
(a local ring, since `φ` is local so `I ⊆ 𝔪_O`), and `x' := f.asFiber x` the point of the fibre
`X_{f x} = X ×_S Spec κ(f x)` over `x`. The fibre inclusion `ι := f.fiberι (f x)` is a preimmersion
(Mathlib), so `s := ι.stalkMap x' : 𝒪_{X,ι x'} → 𝒪_{X_{fx},x'}` is surjective. It remains to
identify `ker s = I`:

* `I ⊆ ker s`: the fibre square `ι ≫ f = (X_{fx} → Spec κ(fx)) ≫ (Spec κ(fx) → S)` gives on stalks
  `s ∘ φ = (fibre → Spec κ) ∘ (Spec κ(fx) → S)`, and the stalk map of `Spec κ(fx) → S` is a local
  homomorphism into (the stalk of `Spec κ(fx)`, which is) the field `κ(fx)`, so it kills `𝔪_R`.
* `ker s ⊆ I`: the local homomorphism `π : O → B` and `κ(fx) → B` (induced by `φ`) give
  `Spec B → X` (namely `Spec π ≫ (Spec O → X)`) and `Spec B → Spec κ(fx)` agreeing over `S`, hence
  `g : Spec B → X_{fx}` with `g(closed point) = x'` and `g ≫ ι = Spec π ≫ (Spec O → X)`. Applying
  Mathlib's `Spec R ⟶ X ≃ {(x, local hom 𝒪_{X,x} → R)}` (`SpecToEquivOfLocalRing`) to this equation
  yields `t ∘ s = π` for the local homomorphism `t := stalkClosedPointTo g : 𝒪_{X_{fx},x'} → B`,
  so `ker s ⊆ ker π = I`.

Everything is done at the point `x' := f.asFiber x` of the fibre over `f x`; the identification
`ι x' = x` (`fiberι_asFiber`) is transported through `stalkCongr`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace IsLocalRing
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

section local_hom_to_field

/-- The stalk map of `Spec κ(y) → S` at the (unique) point of `Spec κ(y)` kills the maximal ideal
of `𝒪_{S,y}`: composed with the isomorphism `𝒪_{Spec κ(y), pt} ≅ κ(y)` it is the local homomorphism
`stalkClosedPointTo`, and a local homomorphism into a field kills the maximal ideal. -/
lemma fromSpecResidueField_stalkMap_eq_zero (y : S) (p : Spec (S.residueField y))
    (a : S.presheaf.stalk (S.fromSpecResidueField y p)) (ha : a ∈ maximalIdeal _) :
    (S.fromSpecResidueField y).stalkMap p a = 0 := by
  obtain rfl : p = closedPoint (S.residueField y) := Subsingleton.elim _ _
  have h0 : Scheme.stalkClosedPointTo (S.fromSpecResidueField y) a = 0 := by
    by_contra hne
    exact ha (IsLocalHom.map_nonunit a (isUnit_iff_ne_zero.mpr hne))
  rw [Scheme.stalkClosedPointTo, CommRingCat.comp_apply] at h0
  have hinj : Function.Injective (stalkClosedPointIso (S.residueField y)).hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  apply hinj
  rw [h0, map_zero]

end local_hom_to_field

section fiber_square

/-- `𝔪_{f x}` is killed by `𝒪_{X, ι x'} → 𝒪_{X_y, x'}` for every point `x'` of the fibre
`X_y`, `ι` the fibre inclusion (from the fibre square and
`fromSpecResidueField_stalkMap_eq_zero`). -/
lemma fiberι_stalkMap_stalkMap_eq_zero (y : S) (x' : f.fiber y)
    (a : S.presheaf.stalk (f (f.fiberι y x'))) (ha : a ∈ maximalIdeal _) :
    (f.fiberι y).stalkMap x' (f.stalkMap (f.fiberι y x') a) = 0 := by
  have key : ∀ b ∈ maximalIdeal (S.presheaf.stalk ((f.fiberι y ≫ f) x')),
      (f.fiberι y ≫ f).stalkMap x' b = 0 := by
    rw [f.fiber_fac]
    intro b hb
    have h0 := fromSpecResidueField_stalkMap_eq_zero (S := S) y (f.fiberToSpecResidueField y x') b hb
    rw [Scheme.Hom.stalkMap_comp]
    erw [CommRingCat.comp_apply]
    exact (congrArg (fun z ↦ (f.fiberToSpecResidueField y).stalkMap x' z) h0).trans (map_zero _)
  have := key a ha
  rw [Scheme.Hom.stalkMap_comp] at this
  erw [CommRingCat.comp_apply] at this
  exact this

end fiber_square

section quotient

variable (x : X)

/-- The ideal `𝔪_{f x} 𝒪_{X,x}` of `𝒪_{X,x}`. -/
abbrev Scheme.Hom.fiberStalkIdeal : Ideal (X.presheaf.stalk x) :=
  Ideal.map (f.stalkMap x).hom (maximalIdeal (S.presheaf.stalk (f x)))

lemma Scheme.Hom.fiberStalkIdeal_ne_top : f.fiberStalkIdeal x ≠ ⊤ :=
  (map_maximalIdeal_lt_top (f.stalkMap x).hom).ne

/-- The local ring `𝒪_{X,x} / 𝔪_{f x} 𝒪_{X,x}`, as an object of `CommRingCat`. -/
def Scheme.Hom.fiberStalkQuot : CommRingCat.{u} :=
  .of (X.presheaf.stalk x ⧸ f.fiberStalkIdeal x)

instance : Nontrivial (f.fiberStalkQuot x) :=
  Ideal.Quotient.nontrivial_iff.mpr (f.fiberStalkIdeal_ne_top x)

instance : IsLocalRing (f.fiberStalkQuot x) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (f.fiberStalkIdeal x)) Ideal.Quotient.mk_surjective

/-- The quotient map `𝒪_{X,x} → 𝒪_{X,x} / 𝔪_{f x} 𝒪_{X,x}`. -/
def Scheme.Hom.fiberStalkQuotMk : X.presheaf.stalk x ⟶ f.fiberStalkQuot x :=
  CommRingCat.ofHom (Ideal.Quotient.mk (f.fiberStalkIdeal x))

instance : IsLocalHom (f.fiberStalkQuotMk x).hom :=
  haveI : Nontrivial (X.presheaf.stalk x ⧸ f.fiberStalkIdeal x) :=
    Ideal.Quotient.nontrivial_iff.mpr (f.fiberStalkIdeal_ne_top x)
  IsLocalHom.of_surjective (Ideal.Quotient.mk (f.fiberStalkIdeal x)) Ideal.Quotient.mk_surjective

lemma Scheme.Hom.fiberStalkQuotMk_stalkMap_eq_zero (a : S.presheaf.stalk (f x))
    (ha : a ∈ maximalIdeal _) : f.fiberStalkQuotMk x (f.stalkMap x a) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)

/-- The map `κ(f x) → 𝒪_{X,x} / 𝔪_{f x} 𝒪_{X,x}` induced by `f.stalkMap x`. -/
def Scheme.Hom.fiberStalkQuotFromResidueField : S.residueField (f x) ⟶ f.fiberStalkQuot x :=
  CommRingCat.ofHom (Ideal.Quotient.lift (maximalIdeal (S.presheaf.stalk (f x)))
    ((f.fiberStalkQuotMk x).hom.comp (f.stalkMap x).hom)
    fun a ha ↦ f.fiberStalkQuotMk_stalkMap_eq_zero x a ha)

lemma Scheme.Hom.residue_fiberStalkQuotFromResidueField :
    S.residue (f x) ≫ f.fiberStalkQuotFromResidueField x =
      f.stalkMap x ≫ f.fiberStalkQuotMk x := by
  ext a
  rfl

/-- The morphism `Spec (𝒪_{X,x} / 𝔪_{f x} 𝒪_{X,x}) → X_{f x}` into the fibre, induced by
`Spec (𝒪_{X,x}/𝔪_{f x}𝒪_{X,x}) → Spec 𝒪_{X,x} → X` and `Spec (…) → Spec κ(f x)`. -/
def Scheme.Hom.fiberStalkQuotTo : Spec (f.fiberStalkQuot x) ⟶ f.fiber (f x) :=
  pullback.lift (Spec.map (f.fiberStalkQuotMk x) ≫ X.fromSpecStalk x)
    (Spec.map (f.fiberStalkQuotFromResidueField x)) (by
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.fromSpecResidueField,
        ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
        Scheme.Hom.residue_fiberStalkQuotFromResidueField])

lemma Scheme.Hom.fiberStalkQuotTo_fiberι :
    f.fiberStalkQuotTo x ≫ f.fiberι (f x) = Spec.map (f.fiberStalkQuotMk x) ≫ X.fromSpecStalk x :=
  pullback.lift_fst _ _ _

lemma Scheme.Hom.fiberStalkQuotTo_closedPoint :
    f.fiberStalkQuotTo x (closedPoint (f.fiberStalkQuot x)) = f.asFiber x := by
  apply (f.fiberι (f x)).isEmbedding.injective
  have h := congrArg (fun h : Spec (f.fiberStalkQuot x) ⟶ X ↦ h (closedPoint (f.fiberStalkQuot x)))
    (f.fiberStalkQuotTo_fiberι x)
  dsimp only at h
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Spec_closedPoint,
    Scheme.fromSpecStalk_closedPoint] at h
  rw [Scheme.Hom.fiberι_asFiber]
  exact h

end quotient

section kernel

variable (x : X)

/-- The stalk map of the fibre inclusion at `f.asFiber x`, precomposed with the identification
`𝒪_{X,x} ≅ 𝒪_{X, ι (asFiber x)}` (`fiberι_asFiber`). -/
def Scheme.Hom.fiberStalkFromStalk :
    X.presheaf.stalk x ⟶ (f.fiber (f x)).presheaf.stalk (f.asFiber x) :=
  (X.presheaf.stalkCongr (.of_eq (f.fiberι_asFiber x).symm)).hom ≫
    (f.fiberι (f x)).stalkMap (f.asFiber x)

lemma Scheme.Hom.fiberStalkFromStalk_surjective :
    Function.Surjective (f.fiberStalkFromStalk x) := by
  intro b
  obtain ⟨a, rfl⟩ := (f.fiberι (f x)).stalkMap_surjective (f.asFiber x) b
  refine ⟨(X.presheaf.stalkCongr (.of_eq (f.fiberι_asFiber x).symm)).inv a, ?_⟩
  change ((X.presheaf.stalkCongr (.of_eq (f.fiberι_asFiber x).symm)).inv ≫
    f.fiberStalkFromStalk x) a = _
  rw [Scheme.Hom.fiberStalkFromStalk, Iso.inv_hom_id_assoc]

/-- `𝔪_{f x} 𝒪_{X,x} ⊆ ker (𝒪_{X,x} → 𝒪_{X_{fx}, asFiber x})`. -/
lemma Scheme.Hom.fiberStalkIdeal_le_ker :
    f.fiberStalkIdeal x ≤ RingHom.ker (f.fiberStalkFromStalk x).hom := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker]
  change (f.stalkMap x ≫ f.fiberStalkFromStalk x) a = 0
  have h := Scheme.Hom.stalkMap_congr_point f x _ (f.fiberι_asFiber x).symm
  unfold Scheme.Hom.fiberStalkFromStalk
  rw [← Category.assoc, h, Category.assoc, CommRingCat.comp_apply]
  refine fiberι_stalkMap_stalkMap_eq_zero f (f x) (f.asFiber x) _ ?_
  have : IsLocalHom (S.presheaf.stalkCongr
      (.of_eq (congrArg f (f.fiberι_asFiber x).symm))).hom.hom := isLocalHom_of_isIso _
  intro hu
  exact ha (IsLocalHom.map_nonunit a hu)

/-- `stalkClosedPointTo` of a morphism `Spec R ⟶ X` written as `Spec φ ≫ (Spec 𝒪_{X,x} → X)` is `φ`
(the `right_inv` half of `SpecToEquivOfLocalRing`, with the point transported). -/
lemma Scheme.stalkClosedPointTo_eq_of_eq_SpecMap_fromSpecStalk {R : CommRingCat.{u}} [IsLocalRing R]
    (h : Spec R ⟶ X) (x : X) (φ : X.presheaf.stalk x ⟶ R) [IsLocalHom φ.hom]
    (e : h = Spec.map φ ≫ X.fromSpecStalk x) :
    Scheme.stalkClosedPointTo h = (X.presheaf.stalkCongr (.of_eq (by
      rw [e, Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]))).hom ≫ φ := by
  subst e
  obtain ⟨h1, h2⟩ := SpecToEquivOfLocalRing_eq_iff.mp
    ((SpecToEquivOfLocalRing X R).right_inv ⟨x, φ, inferInstance⟩)
  exact h2

/-- Transport of a factorisation `ι.stalkMap z₁ ≫ t = (transport) ≫ π` along equalities of points. -/
lemma Scheme.Hom.stalkMap_comp_eq_transport {Z : Scheme.{u}} (ι : Z ⟶ X) {B : CommRingCat.{u}}
    {z₁ z₂ : Z} (hz : z₁ = z₂) {x : X} (hx : ι z₁ = x)
    (t : Z.presheaf.stalk z₁ ⟶ B) (π : X.presheaf.stalk x ⟶ B)
    (H : ι.stalkMap z₁ ≫ t = (X.presheaf.stalkCongr (.of_eq hx)).hom ≫ π) :
    (X.presheaf.stalkCongr (.of_eq (show x = ι z₂ by rw [← hz, hx]))).hom ≫ ι.stalkMap z₂ ≫
      (Z.presheaf.stalkCongr (.of_eq hz.symm)).hom ≫ t = π := by
  subst hz hx
  simpa using H

/-- `ker (𝒪_{X,x} → 𝒪_{X_{fx}, asFiber x}) ⊆ 𝔪_{f x} 𝒪_{X,x}`, via the morphism
`g : Spec (𝒪_{X,x}/𝔪_{fx}𝒪_{X,x}) → X_{fx}`: `g ≫ ι = Spec π ≫ (Spec 𝒪_{X,x} → X)`, so
`stalkClosedPointTo g ∘ ι.stalkMap = π` up to the identifications of points, and hence the
kernel of `ι.stalkMap` is contained in `ker π`. -/
lemma Scheme.Hom.ker_le_fiberStalkIdeal :
    RingHom.ker (f.fiberStalkFromStalk x).hom ≤ f.fiberStalkIdeal x := by
  intro a ha
  rw [RingHom.mem_ker] at ha
  have hg : f.fiberStalkQuotTo x (closedPoint (f.fiberStalkQuot x)) = f.asFiber x :=
    f.fiberStalkQuotTo_closedPoint x
  have hx : f.fiberι (f x) (f.fiberStalkQuotTo x (closedPoint (f.fiberStalkQuot x))) = x := by
    rw [hg, Scheme.Hom.fiberι_asFiber]
  have h1 := Scheme.stalkClosedPointTo_eq_of_eq_SpecMap_fromSpecStalk
    (f.fiberStalkQuotTo x ≫ f.fiberι (f x)) x (f.fiberStalkQuotMk x) (f.fiberStalkQuotTo_fiberι x)
  rw [Scheme.stalkClosedPointTo_comp] at h1
  have h2 := Scheme.Hom.stalkMap_comp_eq_transport (f.fiberι (f x)) hg hx
    (Scheme.stalkClosedPointTo (f.fiberStalkQuotTo x)) (f.fiberStalkQuotMk x) h1
  have h3 : f.fiberStalkFromStalk x ≫
      (((f.fiber (f x)).presheaf.stalkCongr (.of_eq hg.symm)).hom ≫
        Scheme.stalkClosedPointTo (f.fiberStalkQuotTo x)) = f.fiberStalkQuotMk x := by
    rw [← h2]
    rfl
  have h4 : f.fiberStalkQuotMk x a =
      ((((f.fiber (f x)).presheaf.stalkCongr (.of_eq hg.symm)).hom ≫
        Scheme.stalkClosedPointTo (f.fiberStalkQuotTo x))) (f.fiberStalkFromStalk x a) := by
    rw [← CommRingCat.comp_apply, h3]
  have ha' : f.fiberStalkFromStalk x a = 0 := ha
  refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
  change f.fiberStalkQuotMk x a = 0
  rw [h4, ha', map_zero]

lemma Scheme.Hom.ker_fiberStalkFromStalk :
    RingHom.ker (f.fiberStalkFromStalk x).hom = f.fiberStalkIdeal x :=
  le_antisymm (f.ker_le_fiberStalkIdeal x) (f.fiberStalkIdeal_le_ker x)

end kernel

end AlgebraicGeometry

/-- **Stacks 0HA1** (Schemes, Lemma "local ring of the fibre"): for `f : X → S` and `x ∈ X` with
image `s = f x`, the local ring of the scheme-theoretic fibre `X_s` at `x` is
`𝒪_{X,x} / 𝔪_s 𝒪_{X,x}`. Proof: `𝒪_{X,x} → 𝒪_{X_s,x}` is surjective (the fibre inclusion is a
preimmersion) with kernel `𝔪_s 𝒪_{X,x}` (`Scheme.Hom.ker_fiberStalkFromStalk`; see the module
docstring for the route, which avoids any affine reduction). -/
theorem AlgebraicGeometry.Scheme.Hom.fiber_stalk_iso {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (x : X) :
    Nonempty ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x) ≃+*
      X.presheaf.stalk x ⧸ Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f.base x)))) :=
  ⟨((f.fiberStalkFromStalk x).hom.quotientKerEquivOfSurjective
      (f.fiberStalkFromStalk_surjective x)).symm.trans
    (Ideal.quotEquivOfEq (f.ker_fiberStalkFromStalk x))⟩

end
