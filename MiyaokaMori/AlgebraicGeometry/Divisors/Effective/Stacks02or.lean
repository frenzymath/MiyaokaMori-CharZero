import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModuleSectionPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ConeScalingActionIdealSheafOfSectionLeKer

/-! # The zero scheme of a pulled-back section (Stacks 02OR)

Stacks 02OR (universal property of the zero scheme): `f^*s = 0` iff `f` factors through `Z(s)`.
Consequently the zero scheme of a pulled-back section is the scheme-theoretic preimage of the zero
scheme, `Z(f^*s) = f^{-1}(Z(s))` (for the restriction to a closed subscheme, `Z(s|_D) = D ∩ Z(s)`).
Source: Stacks 02OR (`divisors.tex`, `lemma-zero-scheme`, proof omitted there); the pullback of zero
schemes is used in the cone-section argument of Proposition 3.2 of the paper.

Proof route (through the section criterion rather than an affine-local computation of the fibre
product): Mathlib's `I.comap f := (pullback.fst f I.subschemeι).ker`, `I.map f := (I.subschemeι ≫ f).ker`,
and `comap · f ⊣ map · f` (`le_map_iff_comap_le`). Write `I := Z(s)`, `J := Z(f^*s)`.
* `J ≤ I.comap f`: by `idealSheafOfSection_le_ker_iff` (`Z(t) ≤ g.ker ↔ g^*t = 0`) this is equivalent to
  `fst^*(f^*s) = 0`; and `fst^*(f^*s) = (fst ≫ f)^*s = (snd ≫ ι)^*s = snd^*(ι^*s)` (`pullback_comp`,
  `pullback.condition`), where `ι^*s = 0` follows from `I ≤ ι.ker = I` (`ker_subschemeι`) and the same
  criterion.
* `I.comap f ≤ J ↔ I ≤ J.map f = (J.subschemeι ≫ f).ker ↔ (J.subschemeι ≫ f)^*s = 0 ↔ J.subschemeι^*(f^*s) = 0`,
  and the last statement follows from `J ≤ J.subschemeι.ker = J` and the criterion.
The second conclusion is Mathlib's `comapIso` transported along the first equality.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The component on `⊤` of an isomorphism of module sheaves sends a section to `0` iff the section is
`0`. -/
theorem AlgebraicGeometry.Scheme.Modules.iso_hom_app_top_eq_zero_iff
    {Y : AlgebraicGeometry.Scheme.{u}} {M N : Y.Modules} (e : M ≅ N)
    (x : (M.val.obj (Opposite.op ⊤) : Type u)) :
    e.hom.app ⊤ x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h1 : e.inv.app ⊤ (e.hom.app ⊤ x) = x := by
      change (e.hom ≫ e.inv).app ⊤ x = x
      rw [Iso.hom_inv_id]
      rfl
    rw [h, map_zero] at h1
    exact h1.symm
  · rintro rfl
    exact map_zero _

/-- A section pulled back along a composite is zero iff the iterated pullback is zero (compared through
`pullbackComp`; an isomorphism preserves "`= 0`"). -/
theorem sectionPullbackAlong_comp_eq_zero_iff {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {M : Z.Modules} (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    sectionPullbackAlong (f ≫ g) s = 0 ↔
      sectionPullbackAlong f (sectionPullbackAlong g s) = 0 := by
  rw [show sectionPullbackAlong (f ≫ g) s =
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).app M).hom.app ⊤
        (sectionPullbackAlong f (sectionPullbackAlong g s)) from
      (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp f g s).symm]
  exact AlgebraicGeometry.Scheme.Modules.iso_hom_app_top_eq_zero_iff _ _

/-- Pullback along equal morphisms: "`= 0`" is unchanged. -/
theorem sectionPullbackAlong_eq_zero_iff_of_eq {X Y : AlgebraicGeometry.Scheme.{u}}
    {f g : X ⟶ Y} (h : f = g) {M : Y.Modules} (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    sectionPullbackAlong f s = 0 ↔ sectionPullbackAlong g s = 0 := by
  subst h
  exact Iff.rfl

/-- The pullback of the zero section is zero. -/
theorem sectionPullbackAlong_zero {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) :
    sectionPullbackAlong g (0 : (M.val.obj (Opposite.op ⊤) : Type u)) = 0 :=
  map_zero _

theorem AlgebraicGeometry.Scheme.zeroScheme_pullback {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ X) (L : X.Modules) [L.IsLineBundle]
    (s : (L.val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.idealSheafOfSection
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L) (sectionPullbackAlong f s) =
      (AlgebraicGeometry.Scheme.idealSheafOfSection L s).comap f := by
  set I := AlgebraicGeometry.Scheme.idealSheafOfSection L s with hI
  set J := AlgebraicGeometry.Scheme.idealSheafOfSection
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L) (sectionPullbackAlong f s) with hJ
  -- ι^*s = 0 and ι_J^*(f^*s) = 0: a section vanishes on its own zero scheme
  have hιI : sectionPullbackAlong I.subschemeι s = 0 :=
    (AlgebraicGeometry.Scheme.idealSheafOfSection_le_ker_iff I.subschemeι L s).mp
      I.ker_subschemeι.ge
  have hιJ : sectionPullbackAlong J.subschemeι (sectionPullbackAlong f s) = 0 :=
    (AlgebraicGeometry.Scheme.idealSheafOfSection_le_ker_iff J.subschemeι _ _).mp
      J.ker_subschemeι.ge
  apply le_antisymm
  · -- J ≤ ker (pullback.fst f I.subschemeι)
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap,
      AlgebraicGeometry.Scheme.idealSheafOfSection_le_ker_iff,
      ← sectionPullbackAlong_comp_eq_zero_iff,
      sectionPullbackAlong_eq_zero_iff_of_eq (pullback.condition (f := f) (g := I.subschemeι)),
      sectionPullbackAlong_comp_eq_zero_iff, hιI]
    exact sectionPullbackAlong_zero _ _
  · rw [← AlgebraicGeometry.Scheme.IdealSheafData.le_map_iff_comap_le,
      AlgebraicGeometry.Scheme.IdealSheafData.map,
      AlgebraicGeometry.Scheme.idealSheafOfSection_le_ker_iff,
      sectionPullbackAlong_comp_eq_zero_iff]
    exact hιJ

theorem AlgebraicGeometry.Scheme.zeroScheme_pullback_iso {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ X) (L : X.Modules) [L.IsLineBundle]
    (s : (L.val.obj (Opposite.op ⊤) : Type u)) :
    Nonempty ((AlgebraicGeometry.Scheme.idealSheafOfSection
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L) (sectionPullbackAlong f s)).subscheme
      ≅ CategoryTheory.Limits.pullback f
          (AlgebraicGeometry.Scheme.idealSheafOfSection L s).subschemeι) := by
  rw [AlgebraicGeometry.Scheme.zeroScheme_pullback]
  exact ⟨(AlgebraicGeometry.Scheme.idealSheafOfSection L s).comapIso f⟩

end
