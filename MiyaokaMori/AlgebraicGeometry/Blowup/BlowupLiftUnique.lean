import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjSeparated
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks01og
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierComplementDense
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupIsoAwayFromCentre
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01rh
import MiyaokaMori.AlgebraicGeometry.Blowup.InvertibleIdealComplement

/-! # Uniqueness of the lift to the blowup

Uniqueness half of the universal property of the blowup (Stacks 0806): two factorizations of `f : Y → X`
through `b : Bl_I X → X` coincide when `f⁻¹I·O_Y` is invertible.

Source: Stacks 0806 (uniqueness: 02OS (1) + 07ZU + 01RH). The proof combines
`blowup_isIso_morphismRestrict_support_compl` (Stacks 02OS (1)),
`IsInvertibleIdeal.ker_ι_support_compl_eq_bot` (Stacks 07ZU), `relativeProj_isSeparated` and
`Scheme.Hom.ext_of_ker_ι_eq_bot` (Stacks 01RH).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Stacks 0806, uniqueness of the factorization.** If `J := I.comap f` is invertible and
`g ≫ b = f = g' ≫ b`, then `g = g'`.

Proof. Let `W := I.support.compl ⊆ X` and `U := J.support.compl = f⁻¹W ⊆ Y`
(`support_comap_compl_eq_preimage`). Both `U.ι ≫ g` and `U.ι ≫ g'` land in `b⁻¹W` (their composite with
`b` is `U.ι ≫ f`, which lands in `W`), so they factor as `g₀ ≫ (b⁻¹W).ι`, `g₀' ≫ (b⁻¹W).ι`
(`IsOpenImmersion.lift`). Then `g₀ ≫ (b ∣_ W) ≫ W.ι = g₀ ≫ (b⁻¹W).ι ≫ b = U.ι ≫ f`, likewise for `g₀'`;
`W.ι` is a monomorphism, so `g₀ ≫ (b ∣_ W) = g₀' ≫ (b ∣_ W)`, and `b ∣_ W` is an isomorphism
(Stacks 02OS(1), `blowup_isIso_morphismRestrict_support_compl`), hence `g₀ = g₀'` and
`U.ι ≫ g = U.ι ≫ g'`. Finally `U.ι.ker = ⊥` (Stacks 07ZU, `IsInvertibleIdeal.ker_ι_support_compl_eq_bot`)
and `b` is separated (`relativeProj_isSeparated`), so Stacks 01RH (`Scheme.Hom.ext_of_ker_ι_eq_bot`)
gives `g = g'`. -/
theorem AlgebraicGeometry.Scheme.blowup_lift_unique {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) {Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
    (hf : MiyaokaMori.Statement.IsInvertibleIdeal (I.comap f))
    {g g' : Y ⟶ (AlgebraicGeometry.Scheme.blowup I).left}
    (hg : g ≫ (AlgebraicGeometry.Scheme.blowup I).hom = f)
    (hg' : g' ≫ (AlgebraicGeometry.Scheme.blowup I).hom = f) : g = g' := by
  set b := (AlgebraicGeometry.Scheme.blowup I).hom with hb
  have : AlgebraicGeometry.IsSeparated b :=
    AlgebraicGeometry.Scheme.relativeProj_isSeparated I.reesAlgebra
  have : CategoryTheory.IsIso (b ∣_ I.support.compl) :=
    AlgebraicGeometry.Scheme.blowup_isIso_morphismRestrict_support_compl I
  set W : X.Opens := I.support.compl with hWdef
  set U : Y.Opens := (I.comap f).support.compl with hUdef
  have hUW : U = f ⁻¹ᵁ W := MiyaokaMori.Statement.support_comap_compl_eq_preimage I f
  have hU : U.ι.ker = ⊥ := hf.ker_ι_support_compl_eq_bot
  have hrange : ∀ h : Y ⟶ (AlgebraicGeometry.Scheme.blowup I).left, h ≫ b = f →
      Set.range (U.ι ≫ h) ⊆ Set.range (b ⁻¹ᵁ W).ι := by
    intro h hh
    rintro _ ⟨u, rfl⟩
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    have hu : U.ι u ∈ U := u.2
    have hu' : f (U.ι u) ∈ W := hUW.le hu
    have hcomp : (h ≫ b) (U.ι u) = f (U.ι u) := by rw [hh]
    rw [AlgebraicGeometry.Scheme.Hom.comp_apply] at hcomp
    rw [AlgebraicGeometry.Scheme.Hom.comp_apply]
    show b (h (U.ι u)) ∈ W
    rwa [hcomp]
  set g₀ := AlgebraicGeometry.IsOpenImmersion.lift (b ⁻¹ᵁ W).ι (U.ι ≫ g) (hrange g hg) with hg₀
  set g₀' := AlgebraicGeometry.IsOpenImmersion.lift (b ⁻¹ᵁ W).ι (U.ι ≫ g') (hrange g' hg') with hg₀'
  have h₀ : g₀ ≫ (b ⁻¹ᵁ W).ι = U.ι ≫ g := AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  have h₀' : g₀' ≫ (b ⁻¹ᵁ W).ι = U.ι ≫ g' := AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  have key : g₀ ≫ (b ∣_ W) = g₀' ≫ (b ∣_ W) := by
    rw [← cancel_mono W.ι, Category.assoc, Category.assoc, AlgebraicGeometry.morphismRestrict_ι,
      ← Category.assoc, h₀, ← Category.assoc, h₀', Category.assoc, Category.assoc, hg, hg']
  have hfg : U.ι ≫ g = U.ι ≫ g' := by
    rw [← h₀, ← h₀', (cancel_mono (b ∣_ W)).1 key]
  exact AlgebraicGeometry.Scheme.Hom.ext_of_ker_ι_eq_bot b (hg.trans hg'.symm) U hU hfg

end
