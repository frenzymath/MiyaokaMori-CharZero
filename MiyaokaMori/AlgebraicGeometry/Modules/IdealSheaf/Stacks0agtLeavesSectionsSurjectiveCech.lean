import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.ReesAlgebraSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.Stacks0agtLeavesQuotFamilies

/-! # A two-chart Čech criterion for `Γ(X, O_X) ↠ Γ(X, O_X/J)`

For an ideal sheaf `J` on a scheme `X` covered by two affine opens `U₁`, `U₂` with affine
intersection `U₁₂`: if `J(U₁₂) = res(J(U₁)) + res(J(U₂))` (the Čech `H¹` of `J` on this cover
vanishes), then every compatible family `(s_U)_U ∈ J.quotFamilies` (= `Γ(X, O_X/J)`) lifts to
`Γ(X, O_X)`.

Proof. Lift `s_{U₁}, s_{U₂}` to `t₁, t₂`; compatibility on `U₁₂` gives `t₁ − t₂ ∈ J(U₁₂)`, so
`t₁ − t₂ = c₁ + c₂` on `U₁₂` with `cᵢ ∈ J(Uᵢ)`; then `t₁ − c₁` and `t₂ + c₂` agree on `U₁ ⊓ U₂` and
glue to `g ∈ Γ(X, ⊤)` (`TopCat.Sheaf.objSupIsoProdEqLocus`). The family `toQuotFamilies g − s`
vanishes on `U₁`, `U₂`, hence (compatibility + locality of membership in `J`,
`mem_ideal_of_forall_exists_basicOpen`) on every affine open.

Source: Stacks 0AGT proof, second paragraph (Čech form of 0AGS(3)).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : AlgebraicGeometry.Scheme.{u}} (J : X.IdealSheafData)

/-- A compatible family vanishing on the members of an affine open cover vanishes: on an affine `V`,
`s_V = [z]` with `z|_W ∈ J(W)` for every affine basic open `W ⊆ V ⊓ U i`, and membership in `J(V)`
is local (`mem_ideal_of_forall_exists_basicOpen`). -/
theorem quotFamilies_eq_zero_of_iSup_eq_top (s : J.quotFamilies) {ι : Type*}
    (U : ι → X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤) (hs : ∀ i, s.1 (U i) = 0) : s = 0 := by
  apply Subtype.ext
  funext V
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (s.1 V)
  show s.1 V = 0
  rw [← hz, Ideal.Quotient.eq_zero_iff_mem]
  refine J.mem_ideal_of_forall_exists_basicOpen V z ?_
  rintro ⟨p, hp⟩
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge (Set.mem_univ p))
  obtain ⟨f, hfle, hpf⟩ := V.2.exists_basicOpen_le (V := (V : X.Opens) ⊓ (U i).1) ⟨p, hp, hi⟩ hp
  refine ⟨f, hpf, ?_⟩
  have hWV : X.affineBasicOpen f ≤ V := X.basicOpen_le f
  have hWU : X.affineBasicOpen f ≤ U i := fun y hy => (hfle hy).2
  have h1 := s.2 (X.affineBasicOpen f) V hWV
  have h2 := s.2 (X.affineBasicOpen f) (U i) hWU
  rw [← hz, quotRes_mk] at h1
  rw [hs i, map_zero] at h2
  have h3 : X.presheaf.map (homOfLE hWV).op z ∈ J.ideal (X.affineBasicOpen f) :=
    Ideal.Quotient.eq_zero_iff_mem.1 (h1.trans h2.symm)
  exact h3

/-- **Two-chart Čech criterion.** `U₁ ⊔ U₂ = X`, `U₁₂ = U₁ ⊓ U₂` all affine, and
`J(U₁₂) = res J(U₁) + res J(U₂)` ⟹ `Γ(X, ⊤) → J.quotFamilies` is surjective. -/
theorem toQuotFamilies_surjective_of_two_affineOpens (U₁ U₂ U₁₂ : X.affineOpens)
    (h₁ : U₁₂ ≤ U₁) (h₂ : U₁₂ ≤ U₂) (hinf : U₁.1 ⊓ U₂.1 ≤ U₁₂.1) (hcov : U₁.1 ⊔ U₂.1 = ⊤)
    (hsplit : ∀ z ∈ J.ideal U₁₂, ∃ c₁ ∈ J.ideal U₁, ∃ c₂ ∈ J.ideal U₂,
      z = X.presheaf.map (homOfLE h₁).op c₁ + X.presheaf.map (homOfLE h₂).op c₂) :
    Function.Surjective J.toQuotFamilies := by
  intro s
  obtain ⟨t₁, ht₁⟩ := Ideal.Quotient.mk_surjective (s.1 U₁)
  obtain ⟨t₂, ht₂⟩ := Ideal.Quotient.mk_surjective (s.1 U₂)
  -- the difference of the two lifts lies in `J(U₁₂)`
  have hd : X.presheaf.map (homOfLE h₁).op t₁ - X.presheaf.map (homOfLE h₂).op t₂ ∈
      J.ideal U₁₂ := by
    rw [← Ideal.Quotient.eq, ← quotRes_mk, ← quotRes_mk, ht₁, ht₂, s.2 U₁₂ U₁ h₁, s.2 U₁₂ U₂ h₂]
  obtain ⟨c₁, hc₁, c₂, hc₂, hc⟩ := hsplit _ hd
  -- `t₁ - c₁` and `t₂ + c₂` agree on `U₁ ⊓ U₂`
  have hagree : X.presheaf.map (homOfLE (inf_le_left : U₁.1 ⊓ U₂.1 ≤ U₁.1)).op (t₁ - c₁) =
      X.presheaf.map (homOfLE (inf_le_right : U₁.1 ⊓ U₂.1 ≤ U₂.1)).op (t₂ + c₂) := by
    have e₁ : X.presheaf.map (homOfLE (inf_le_left : U₁.1 ⊓ U₂.1 ≤ U₁.1)).op =
        X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE hinf).op := by
      rw [← Functor.map_comp]; rfl
    have e₂ : X.presheaf.map (homOfLE (inf_le_right : U₁.1 ⊓ U₂.1 ≤ U₂.1)).op =
        X.presheaf.map (homOfLE h₂).op ≫ X.presheaf.map (homOfLE hinf).op := by
      rw [← Functor.map_comp]; rfl
    rw [e₁, e₂, CommRingCat.comp_apply, CommRingCat.comp_apply]
    congr 1
    rw [map_sub, map_add]
    linear_combination hc
  -- glue
  let pr : RingHom.eqLocus
      (RingHom.comp (X.sheaf.obj.map (homOfLE inf_le_left : U₁.1 ⊓ U₂.1 ⟶ U₁.1).op).hom
        (RingHom.fst (X.sheaf.obj.obj (op U₁.1)) (X.sheaf.obj.obj (op U₂.1))))
      (RingHom.comp (X.sheaf.obj.map (homOfLE inf_le_right : U₁.1 ⊓ U₂.1 ⟶ U₂.1).op).hom
        (RingHom.snd (X.sheaf.obj.obj (op U₁.1)) (X.sheaf.obj.obj (op U₂.1)))) :=
    ⟨(t₁ - c₁, t₂ + c₂), hagree⟩
  let g' : Γ(X, U₁.1 ⊔ U₂.1) := (X.sheaf.objSupIsoProdEqLocus U₁.1 U₂.1).inv pr
  have hg'₁ : X.presheaf.map (homOfLE le_sup_left).op g' = t₁ - c₁ :=
    TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst X.sheaf U₁.1 U₂.1 pr
  have hg'₂ : X.presheaf.map (homOfLE le_sup_right).op g' = t₂ + c₂ :=
    TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd X.sheaf U₁.1 U₂.1 pr
  let g : Γ(X, ⊤) := X.presheaf.map (homOfLE (hcov.ge : ⊤ ≤ U₁.1 ⊔ U₂.1)).op g'
  have hg₁ : X.presheaf.map (homOfLE le_top).op g = t₁ - c₁ := by
    rw [← hg'₁]
    show (X.presheaf.map (homOfLE hcov.ge).op ≫ X.presheaf.map (homOfLE le_top).op) g' = _
    rw [← Functor.map_comp]; rfl
  have hg₂ : X.presheaf.map (homOfLE le_top).op g = t₂ + c₂ := by
    rw [← hg'₂]
    show (X.presheaf.map (homOfLE hcov.ge).op ≫ X.presheaf.map (homOfLE le_top).op) g' = _
    rw [← Functor.map_comp]; rfl
  refine ⟨g, ?_⟩
  -- `toQuotFamilies g - s` vanishes on `U₁` and `U₂`, hence everywhere
  rw [← sub_eq_zero]
  refine J.quotFamilies_eq_zero_of_iSup_eq_top _ (fun b : Bool => cond b U₁ U₂) ?_ ?_
  · rw [iSup_bool_eq]; exact hcov
  · intro b
    cases b
    · show (J.toQuotFamilies g).1 U₂ - s.1 U₂ = 0
      rw [toQuotFamilies_apply_coe, hg₂, ← ht₂, map_add, add_sub_cancel_left,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hc₂
    · show (J.toQuotFamilies g).1 U₁ - s.1 U₁ = 0
      rw [toQuotFamilies_apply_coe, hg₁, ← ht₁, map_sub, sub_sub_cancel_left, neg_eq_zero,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hc₁

end AlgebraicGeometry.Scheme.IdealSheafData

end
