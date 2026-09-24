import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks01og
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0804
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupExceptionalInvertible
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0agrChartPresentation
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks0agrChartLocalRegular

/-! # The exceptional ideal sheaf of `Bl_𝔪 Spec A` is radical

Algebraic core of the second paragraph of Stacks 0AGT (`blowup_improve_support_finite`), replacing the
appeal to Stacks 0AGB ("codimension 1 part") by a direct argument:

* `support_le_of_eq_mul_of_pow_le`: if `IX = E^d · I'` and `E^n ≤ IX`, then `supp I' ⊆ supp E`;
* `le_of_support_le_of_radical`: Nullstellensatz for ideal sheaves — if `J` is radical and
  `supp J ⊆ supp I`, then `I ≤ J` (Mathlib's Galois connection `support` / `vanishingIdeal`);
* `Ideal.affineBlowup_maximalIdeal_span_isRadical`: on the affine chart `A[𝔪/a]` of `Bl_𝔪 Spec A`
  (`A` regular local of dimension `2`), the exceptional ideal `(a)` is radical: either `(a) = ⊤`
  (the chart misses `E`), or `a ∉ 𝔪²` and `A[𝔪/a]/(a) ≅ κ[T]` is a domain (Stacks 0AGR, steps 1–3);
* `blowup_regularLocalRing_dimTwo_exceptionalIdeal_radical`: hence the exceptional ideal sheaf
  `E = 𝔪·O_X` is radical (`E.radical = E`), i.e. the exceptional divisor is reduced.

Source: Stacks 0AGT proof, second paragraph; Stacks 0AGR (charts `A[𝔪/a]`, `A[𝔪/a]/(a) ≅ κ[T]`);
Stacks 0804 (affine charts of a blowup); Stacks 00E0 (`V(I) ⊆ V(J) ⇔ J ⊆ √I`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Polynomial
open scoped AlgebraicGeometry Pointwise

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- If `IX = E^d · I'` (affine-open by affine-open) and `E^n ≤ IX`, then `supp I' ⊆ supp E`:
`supp I' ⊆ supp (E^d · I') = supp IX ⊆ supp (E^n) ⊆ supp E` (`support_mul`, `support_antitone`,
`support_pow_succ`; for `n = 0`, `E^0 = ⊤` has empty support). -/
theorem support_le_of_eq_mul_of_pow_le {X : AlgebraicGeometry.Scheme.{u}}
    {E IX I' : X.IdealSheafData} (d n : ℕ)
    (hprod : ∀ U : X.affineOpens, IX.ideal U = E.ideal U ^ d * I'.ideal U) (hn : E ^ n ≤ IX) :
    I'.support ≤ E.support := by
  have hIX : IX = E ^ d * I' := by
    ext U : 2
    rw [hprod U, ideal_mul, Pi.mul_apply, ideal_pow, Pi.pow_apply]
  have h1 : I'.support ≤ IX.support := by
    rw [hIX, support_mul]
    exact le_sup_right
  have h2 : IX.support ≤ (E ^ n).support := support_antitone hn
  have h3 : (E ^ n).support ≤ E.support := by
    cases n with
    | zero => rw [pow_zero, one_eq_top, support_top]; exact bot_le
    | succ m => rw [support_pow_succ]
  exact h1.trans (h2.trans h3)

/-- **Nullstellensatz for ideal sheaves.** If `J` is radical (`J.radical = J`) and
`supp J ⊆ supp I`, then `I ≤ J`: `I ≤ vanishingIdeal (supp I) ≤ vanishingIdeal (supp J) = J.radical = J`
(`le_support_iff_le_vanishingIdeal`, `vanishingIdeal_antimono`, `vanishingIdeal_support`). -/
theorem le_of_support_le_of_radical {X : AlgebraicGeometry.Scheme.{u}} {I J : X.IdealSheafData}
    (hJ : J.radical = J) (h : J.support ≤ I.support) : I ≤ J := by
  have h1 : I ≤ vanishingIdeal I.support := le_support_iff_le_vanishingIdeal.mp le_rfl
  have h2 : vanishingIdeal I.support ≤ vanishingIdeal J.support := vanishingIdeal_antimono h
  rw [vanishingIdeal_support (I := J), hJ] at h2
  exact h1.trans h2

end AlgebraicGeometry.Scheme.IdealSheafData

namespace Ideal

variable {A : Type u} [CommRing A]

/-- **The exceptional ideal on a chart of `Bl_𝔪 Spec A` is radical** (`A` regular local of dimension
`2`, `J = 𝔪`, `a ∈ 𝔪`): the ideal `(a)` of the affine blowup algebra `A[𝔪/a]` is radical.

Proof. If `(a) = ⊤` there is nothing to prove. Otherwise `(a) ⊆ 𝔮` for a maximal ideal `𝔮`, and
`𝔪·A[𝔪/a] = (a)` (`MiyaokaMori.RingTheory.IdealFractionChart.centerExtension_eq_span`) gives `𝔪 ≤ 𝔮 ∩ A`, so
`a ∉ 𝔪²` (`notMem_sq_of_affineBlowup_le_comap`). Steps 1–3 of Stacks 0AGR
(as in `affineBlowup_isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal`): `𝔪 = (a, b)`,
`a, b` is a regular sequence, and `A[𝔪/a]/(a) ≅ κ[T]`
(`affineBlowup_quotient_span_algebraMap_equiv_polynomial`), a domain; hence `(a)` is prime
(`Ideal.Quotient.isDomain_iff_prime`), in particular radical. -/
theorem affineBlowup_maximalIdeal_span_isRadical [IsRegularLocalRing A] (hdim : ringKrullDim A = 2)
    (J : Ideal A) (hJ : J = IsLocalRing.maximalIdeal A) (a : A) (ha : a ∈ J) :
    (Ideal.span {algebraMap A (J.affineBlowup a) a}).IsRadical := by
  subst hJ
  by_cases htop : Ideal.span {algebraMap A ((IsLocalRing.maximalIdeal A).affineBlowup a) a} = ⊤
  · rw [htop]
    exact Ideal.radical_eq_iff.mp (Ideal.radical_top _)
  obtain ⟨𝔮, h𝔮max, h𝔮⟩ := Ideal.exists_le_maximal _ htop
  have hspan : (IsLocalRing.maximalIdeal A).map
      (algebraMap A ((IsLocalRing.maximalIdeal A).affineBlowup a)) =
        Ideal.span {algebraMap A ((IsLocalRing.maximalIdeal A).affineBlowup a) a} :=
    MiyaokaMori.RingTheory.IdealFractionChart.centerExtension_eq_span _ a ha
  have hle : IsLocalRing.maximalIdeal A ≤
      𝔮.comap (algebraMap A ((IsLocalRing.maximalIdeal A).affineBlowup a)) := by
    intro m hm
    rw [Ideal.mem_comap]
    exact h𝔮 (hspan ▸ Ideal.mem_map_of_mem _ hm)
  have := h𝔮max.isPrime
  -- Step 1: `𝔪 = (a, b)`.
  have ha2 : a ∉ IsLocalRing.maximalIdeal A ^ 2 :=
    Ideal.notMem_sq_of_affineBlowup_le_comap _ a ha 𝔮 hle
  have hrank : (IsLocalRing.maximalIdeal A).spanFinrank = 2 := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
    rw [hdim] at h
    exact_mod_cast h
  obtain ⟨s, hs, hspan'⟩ := IsLocalRing.exists_finset_span_insert_eq_maximalIdeal ha ha2
  rw [hrank] at hs
  obtain ⟨b, rfl⟩ : ∃ b, s = {b} := by
    rcases Nat.lt_or_ge s.card 1 with h | h
    · exfalso
      rw [Nat.lt_one_iff, Finset.card_eq_zero] at h
      subst h
      have h1 := Submodule.spanFinrank_span_le_ncard_of_finite
        (R := A) (M := A) (s := insert a ((∅ : Finset A) : Set A)) (by simp)
      rw [show Submodule.span A (insert a ((∅ : Finset A) : Set A)) = IsLocalRing.maximalIdeal A from
        hspan', hrank] at h1
      simp at h1
    · exact Finset.card_eq_one.mp (le_antisymm (by omega) h)
  rw [Finset.coe_singleton] at hspan'
  have hb : b ∈ IsLocalRing.maximalIdeal A := hspan' ▸ Ideal.subset_span (by simp)
  -- Step 2: `a, b` is a regular sequence.
  have hreg : RingTheory.Sequence.IsWeaklyRegular A [a, b] := by
    have hrange : Set.range ![a, b] = {a, b} := by
      ext x
      simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm]
    have := IsRegularLocalRing.isWeaklyRegular_of_span_eq_maximalIdeal hdim ![a, b]
      (by rw [hrange]; exact hspan')
    simpa [List.ofFn_succ] using this
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hreg
  obtain ⟨hreg_a, hreg_b⟩ := hreg
  have ha_nzd : a ∈ nonZeroDivisors A := by
    refine mem_nonZeroDivisors_iff_right.mpr fun x hx => ?_
    exact hreg_a (show a • x = a • 0 by rw [smul_zero, smul_eq_mul, mul_comm]; exact hx)
  have hsmul : (a • (⊤ : Submodule A A)) = (Ideal.span {a} : Ideal A) := by
    rw [← Submodule.ideal_span_singleton_smul]; simp
  have hb_nzd : ∀ x : A, b * x ∈ Ideal.span {a} → x ∈ Ideal.span {a} := by
    intro x hx
    have h1 : b • (Submodule.Quotient.mk x : QuotSMulTop a A) = b • 0 := by
      rw [smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hsmul]
      exact hx
    have h2 := hreg_b h1
    rw [Submodule.Quotient.mk_eq_zero, hsmul] at h2
    exact h2
  -- Step 3: `A[𝔪/a]/(a) ≅ κ[T]` is a domain, so `(a)` is prime.
  obtain ⟨e⟩ := (IsLocalRing.maximalIdeal A).affineBlowup_quotient_span_algebraMap_equiv_polynomial
    a b hb hspan'.symm ha_nzd hb_nzd
  have : IsDomain ((IsLocalRing.maximalIdeal A).affineBlowup a ⧸
      Ideal.span {algebraMap A ((IsLocalRing.maximalIdeal A).affineBlowup a) a}) :=
    MulEquiv.isDomain ((A ⧸ IsLocalRing.maximalIdeal A)[X]) e.toMulEquiv
  exact (Ideal.Quotient.isDomain_iff_prime _).mp this |>.isRadical

end Ideal

/-- **The exceptional divisor of `Bl_𝔪 Spec A` is reduced** (`A` regular local of dimension `2`):
the exceptional ideal sheaf `E = 𝔪·O_X` satisfies `E.radical = E`.

Proof. Radicality is checked on the affine charts `V_a ≅ Spec A[𝔪/a]` (`a ∈ 𝔪`) of Stacks 0804
(`blowup_preimage_affine_cover` for the affine open `⊤` of `Spec A`), which cover `X`
(`ext_of_iSup_eq_top`). As in the proof of `blowup_exceptional_isInvertibleIdeal`
(`comap_ideal_eq_map_appLE`, `appLE_eq_of_iso_spec`, `Ideal.map_comp_eq_span_singleton_of_bijective`),
`E(V_a)` is the image of `(a) ⊆ A[𝔪/a]` under the ring isomorphism `ψ : A[𝔪/a] ≅ Γ(X, V_a)`. The
ideal `(a)` is radical (`Ideal.affineBlowup_maximalIdeal_span_isRadical`, applied to the regular local
ring `Γ(Spec A, ⊤) ≅ A`), and radicality is transported along `ψ` (`Ideal.map_radical_of_surjective`). -/
theorem AlgebraicGeometry.blowup_regularLocalRing_dimTwo_exceptionalIdeal_radical
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    let e := (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    let J : (AlgebraicGeometry.Spec (CommRingCat.of A)).IdealSheafData :=
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop ((IsLocalRing.maximalIdeal A).map e)
    (AlgebraicGeometry.Scheme.blowup.exceptionalIdeal J).radical =
      AlgebraicGeometry.Scheme.blowup.exceptionalIdeal J := by
  intro e J
  -- transport regularity and dimension of `A` to `Γ(Spec A, ⊤)` along `ΓSpecIso`
  let ε : A ≃+* Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤) :=
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
  have : IsRegularLocalRing Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤) :=
    IsRegularLocalRing.of_ringEquiv ε
  have hdim' : ringKrullDim Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤) = 2 := by
    rw [← ringKrullDim_eq_of_ringEquiv ε, hdim]
  have hmax : (IsLocalRing.maximalIdeal A).map
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom =
        IsLocalRing.maximalIdeal Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤) :=
    IsLocalRing.map_ringEquiv_maximalIdeal ε
  let U : (AlgebraicGeometry.Spec (CommRingCat.of A)).affineOpens :=
    ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩
  have hJ : J.ideal U = IsLocalRing.maximalIdeal Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤) := by
    show (AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop _).ideal ⟨⊤, _⟩ = _
    simpa using hmax
  -- the charts of Stacks 0804
  obtain ⟨V, hV, hE, hcov⟩ := AlgebraicGeometry.Scheme.blowup_preimage_affine_cover J U
  choose ch hch using hE
  have hWaff : ∀ a, AlgebraicGeometry.IsAffineOpen (V a) := fun a =>
    AlgebraicGeometry.IsAffine.of_isIso (ch a).hom
  refine AlgebraicGeometry.Scheme.IdealSheafData.ext_of_iSup_eq_top (fun a => ⟨V a, hWaff a⟩) ?_ ?_
  · rw [hcov]
    ext x
    exact ⟨fun _ => trivial, fun _ => trivial⟩
  intro a
  -- `E(V_a)` is the image of `(a)` under the chart isomorphism
  have hideal := AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE J
    (AlgebraicGeometry.Scheme.blowup J).hom U ⟨V a, hWaff a⟩ (hV a)
  rw [AlgebraicGeometry.Scheme.Hom.appLE_eq_of_iso_spec _ U (V a) (hV a) _ _ (ch a) (hch a)] at hideal
  let ψ : CommRingCat.of (Ideal.affineBlowup (J.ideal U) (a : Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U))) ⟶
      Γ((AlgebraicGeometry.Scheme.blowup J).left, V a) :=
    (AlgebraicGeometry.Scheme.ΓSpecIso _).inv ≫ (ch a).hom.appTop ≫ (V a).topIso.hom
  have hbij : Function.Bijective ψ.hom := ConcreteCategory.bijective_of_isIso
    ((AlgebraicGeometry.Scheme.ΓSpecIso _).symm ≪≫ AlgebraicGeometry.Scheme.Γ.mapIso (ch a).op ≪≫
      (V a).topIso).hom
  obtain ⟨-, h2⟩ := Ideal.map_comp_eq_span_singleton_of_bijective (J.ideal U)
    (algebraMap Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U)
      (Ideal.affineBlowup (J.ideal U) (a : Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U)))) ψ.hom hbij a
    (MiyaokaMori.RingTheory.IdealFractionChart.centerExtension_eq_span _ _ a.2)
    (MiyaokaMori.RingTheory.IdealFractionChart.generator_mul_eq_zero _ _)
  have hEV : (AlgebraicGeometry.Scheme.blowup.exceptionalIdeal J).ideal ⟨V a, hWaff a⟩ =
      Ideal.map ψ.hom (Ideal.span {algebraMap Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U)
        (Ideal.affineBlowup (J.ideal U) (a : Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U))) a}) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact hideal.trans h2
  -- `(a)` is radical in `A[𝔪/a]`, and radicality is transported along `ψ`
  have hrad := Ideal.affineBlowup_maximalIdeal_span_isRadical hdim' (J.ideal U) hJ
    (a : Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U)) a.2
  show ((AlgebraicGeometry.Scheme.blowup.exceptionalIdeal J).ideal ⟨V a, hWaff a⟩).radical = _
  have hker : RingHom.ker ψ.hom ≤ Ideal.span {algebraMap Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U)
      (Ideal.affineBlowup (J.ideal U) (a : Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U))) a} := by
    rw [(RingHom.injective_iff_ker_eq_bot ψ.hom).mp hbij.1]
    exact bot_le
  rw [hEV, ← Ideal.map_radical_of_surjective hbij.2 hker, Ideal.radical_eq_iff.mpr hrad]

end
