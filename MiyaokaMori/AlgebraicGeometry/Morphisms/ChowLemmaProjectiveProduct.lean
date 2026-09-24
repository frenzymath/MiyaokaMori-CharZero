import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphismComp
import MiyaokaMori.AlgebraicGeometry.Morphisms.ChowLemmaProjectiveMorphismAux

/-! # Finite fibre products of projective `S`-schemes

Step 2 of Chow's lemma over a Noetherian affine base (`ChowLemmaNoetherianAffineBase.lean`,
Stacks 0200 proof): given finitely many projective morphisms
`f i : Z i ⟶ S` (nonempty finite index set) there is a projective `fP : P ⟶ S` with `S`-projections
`p i : P ⟶ Z i` such that every family of `S`-morphisms `t i : T ⟶ Z i` factors through `P`
(existence of the lift only; uniqueness is not needed). Induction on a nonempty `Finset` of indices, the step
being the fibre product over `S`: `pullback.fst` is projective as a base change
(`isProjectiveMorphism_pullback_fst`) and `pullback.fst ≫ fP` is projective by `IsProjectiveMorphism.comp`
(which needs `S` quasi-compact and quasi-separated). This replaces the Segre embedding of Stacks 0200 and is
the relative form of `exists_isProjectiveOver_product` (`Stacks0200_ChowAssembly_Product.lean`, over a field). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- Fibre products over `S` of projective `S`-schemes indexed by a nonempty finite set of indices, with the
lifting property for families of `S`-morphisms (Stacks 0200 proof, step "`P := ∏ Z_i`"). -/
theorem exists_isProjectiveMorphism_product_finset {S : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] {ι : Type v} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ S)
    [∀ i, IsProjectiveMorphism (f i)] (s : Finset ι) (hs : s.Nonempty) :
    ∃ (P : Scheme.{u}) (fP : P ⟶ S), IsProjectiveMorphism fP ∧
      ∃ p : ∀ i, i ∈ s → (P ⟶ Z i), (∀ i (hi : i ∈ s), p i hi ≫ f i = fP) ∧
        ∀ (T : Scheme.{u}) (tT : T ⟶ S) (t : ∀ i, T ⟶ Z i), (∀ i, t i ≫ f i = tT) →
          ∃ h : T ⟶ P, ∀ i (hi : i ∈ s), h ≫ p i hi = t i := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    refine ⟨Z a, f a, inferInstance,
      fun i hi => eqToHom (congrArg Z (Finset.mem_singleton.mp hi).symm), ?_, ?_⟩
    · intro i hi
      obtain rfl := Finset.mem_singleton.mp hi
      simp
    · intro T tT t ht
      refine ⟨t a, fun i hi => ?_⟩
      obtain rfl := Finset.mem_singleton.mp hi
      simp
  | cons a s ha hs ih =>
    obtain ⟨P, fP, hP, p, hp, hlift⟩ := ih
    let P' := pullback fP (f a)
    let fP' : P' ⟶ S := pullback.fst fP (f a) ≫ fP
    have hfst : IsProjectiveMorphism (pullback.fst fP (f a)) := isProjectiveMorphism_pullback_fst fP (f a)
    have hP' : IsProjectiveMorphism fP' := IsProjectiveMorphism.comp _ _
    refine ⟨P', fP', hP', fun i hi =>
      if h : i = a then pullback.snd _ _ ≫ eqToHom (congrArg Z h.symm)
      else pullback.fst _ _ ≫ p i ((Finset.mem_cons.mp hi).resolve_left h), ?_, ?_⟩
    · intro i hi
      by_cases h : i = a
      · subst h
        simp only [dif_pos, eqToHom_refl, Category.comp_id, fP']
        exact pullback.condition.symm
      · simp only [dif_neg h, Category.assoc, hp i _, fP']
    · intro T tT t ht
      obtain ⟨h', hh'⟩ := hlift T tT t ht
      have hcomp : h' ≫ fP = t a ≫ f a := by
        obtain ⟨b, hb⟩ := hs
        rw [ht a, ← ht b, ← hh' b hb, Category.assoc, hp b hb]
      refine ⟨pullback.lift h' (t a) hcomp, fun i hi => ?_⟩
      by_cases h : i = a
      · subst h
        simp only [dif_pos, eqToHom_refl, Category.comp_id, pullback.lift_snd]
      · simp only [dif_neg h, pullback.lift_fst_assoc, hh']

/-- Fibre products over `S` of finitely many projective `S`-schemes (nonempty finite index type), with
`S`-projections and the lifting property for families of `S`-morphisms. -/
theorem exists_isProjectiveMorphism_product {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    {ι : Type v} [Finite ι] [Nonempty ι] (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ S)
    [∀ i, IsProjectiveMorphism (f i)] :
    ∃ (P : Scheme.{u}) (fP : P ⟶ S), IsProjectiveMorphism fP ∧
      ∃ p : ∀ i, P ⟶ Z i, (∀ i, p i ≫ f i = fP) ∧
        ∀ (T : Scheme.{u}) (tT : T ⟶ S) (t : ∀ i, T ⟶ Z i), (∀ i, t i ≫ f i = tT) →
          ∃ h : T ⟶ P, ∀ i, h ≫ p i = t i := by
  let _ := Fintype.ofFinite ι
  obtain ⟨P, fP, hP, p, hp, hlift⟩ :=
    exists_isProjectiveMorphism_product_finset Z f Finset.univ Finset.univ_nonempty
  refine ⟨P, fP, hP, fun i => p i (Finset.mem_univ i), fun i => hp i _, ?_⟩
  intro T tT t ht
  obtain ⟨h, hh⟩ := hlift T tT t ht
  exact ⟨h, fun i => hh i _⟩

end AlgebraicGeometry

end
