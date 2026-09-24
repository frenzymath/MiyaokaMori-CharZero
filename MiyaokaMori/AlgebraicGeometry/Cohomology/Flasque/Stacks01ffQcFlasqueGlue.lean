import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks01ffQcFlasque

/-! # The two-open gluing step for qc-flasque sheaves

The two-open gluing step of Kempf's argument (Kempf 1980, §2; the same step as in the proof of Hartshorne
III.2.5 / Mathlib `TopCat.Sheaf.IsFlasque.epi_of_shortExact`, but using only restriction maps between
quasi-compact opens): given a short exact sequence `0 → F → G → H → 0` of abelian sheaves with `F` qc-flasque,
a section `s ∈ H(U)` and lifts of `s` to `G` over quasi-compact opens `W₁, W₂ ≤ U`, there is a lift over
`W₁ ⊔ W₂`. Used by `IsQcFlasque.surjective_app_of_shortExact` (induction over a finite cover). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- Restricting twice is restricting once (functoriality of `F.obj`; the category `Opens X` is thin). -/
theorem res_res (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {A B C : TopologicalSpace.Opens X} (h₁ : A ≤ B) (h₂ : B ≤ C) (x : F.obj.obj (op C)) :
    F.obj.map (homOfLE h₁).op (F.obj.map (homOfLE h₂).op x) = F.obj.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Naturality of a morphism of sheaves on sections, elementwise. -/
theorem app_res {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (φ : F ⟶ G)
    {A B : TopologicalSpace.Opens X} (h : A ≤ B) (x : F.obj.obj (op B)) :
    φ.hom.app (op A) (F.obj.map (homOfLE h).op x) = G.obj.map (homOfLE h).op (φ.hom.app (op B) x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, φ.hom.naturality]

/-- (Two-open step; Kempf 1980 §2, cf. Hartshorne III.2.5 / Mathlib
`TopCat.Sheaf.IsFlasque.epi_of_shortExact`). Let `X` be quasi-separated, `0 → F → G → H → 0` short exact in
`Sh(X, Ab)` with `F` qc-flasque, `s ∈ H(U)`, and `W₁, W₂ ≤ U` quasi-compact opens with sections `a ∈ G(W₁)`,
`b ∈ G(W₂)` lifting `s|_{W₁}`, `s|_{W₂}`. Then `s|_{W₁ ⊔ W₂}` lifts to `G(W₁ ⊔ W₂)`.

**Proof.** Put `Z := W₁ ⊓ W₂`; it is quasi-compact since `X` is quasi-separated
(`IsCompact.inter_of_isOpen`). The difference `d := a|_Z − b|_Z ∈ G(Z)` maps to `s|_Z − s|_Z = 0` in `H(Z)`
(naturality of `g`), so by exactness on sections (`TopCat.Sheaf.sections_exact_of_left_exact`: the sequence
`0 → F(Z) → G(Z) → H(Z)` is exact because `Sheaf.forget` is left exact) `d = f(c₀)` for some `c₀ ∈ F(Z)`.
As `F` is qc-flasque and `Z ≤ W₂` are quasi-compact, `c₀ = c|_Z` for some `c ∈ F(W₂)`. Replace `b` by
`b' := b + f(c)`: still `g(b') = s|_{W₂}` because `g ∘ f = 0`, and now `a|_Z = b'|_Z` (naturality of `f`).
By the sheaf condition (`TopCat.Sheaf.existsUnique_gluing'` for the cover `W₁, W₂` of `W₁ ⊔ W₂`; the
compatibility condition on `W₁ ⊓ W₂` and `W₂ ⊓ W₁` follows from `a|_Z = b'|_Z` by restricting) `a` and `b'`
glue to `e ∈ G(W₁ ⊔ W₂)`, and `g(e) = s|_{W₁ ⊔ W₂}` because both sides restrict to `s|_{W_i}` on `W_i`
(`TopCat.Sheaf.eq_of_locally_eq'`). Edge cases: `W₁ = ∅` or `W₂ = ∅` are covered by the same argument
(`Z = ∅`, `F(∅) = 0`). -/
theorem IsQcFlasque.exists_lift_sup [QuasiSeparatedSpace X]
    {S : CategoryTheory.ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (h₁ : TopCat.Sheaf.IsQcFlasque S.X₁) {U W₁ W₂ : TopologicalSpace.Opens X}
    (hW₁ : IsCompact (W₁ : Set X)) (hW₂ : IsCompact (W₂ : Set X)) (e₁ : W₁ ≤ U) (e₂ : W₂ ≤ U)
    (s : S.X₃.obj.obj (op U))
    (a : S.X₂.obj.obj (op W₁)) (ha : S.g.hom.app (op W₁) a = S.X₃.obj.map (homOfLE e₁).op s)
    (b : S.X₂.obj.obj (op W₂)) (hb : S.g.hom.app (op W₂) b = S.X₃.obj.map (homOfLE e₂).op s) :
    ∃ c : S.X₂.obj.obj (op (W₁ ⊔ W₂)),
      S.g.hom.app (op (W₁ ⊔ W₂)) c = S.X₃.obj.map (homOfLE (sup_le e₁ e₂)).op s := by
  -- `Z := W₁ ⊓ W₂` is quasi-compact (quasi-separatedness)
  have hZ : IsCompact ((W₁ ⊓ W₂ : Opens X) : Set X) := by
    rw [Opens.coe_inf]
    exact hW₁.inter_of_isOpen hW₂ W₁.isOpen W₂.isOpen
  have hfg : ∀ (W : Opens X) (z : S.X₁.obj.obj (op W)), S.g.hom.app (op W) (S.f.hom.app (op W) z) = 0 := by
    intro W z
    have h0 : S.f.hom.app (op W) ≫ S.g.hom.app (op W) = 0 := by
      rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, S.zero]; rfl
    have := ConcreteCategory.congr_hom h0 z
    simpa using this
  -- the difference of the two lifts on `Z` comes from `F(Z)`
  set d : S.X₂.obj.obj (op (W₁ ⊓ W₂)) :=
    S.X₂.obj.map (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)).op a -
      S.X₂.obj.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op b with hd_def
  have hd : S.g.hom.app (op (W₁ ⊓ W₂)) d = 0 := by
    rw [hd_def, map_sub, TopCat.Sheaf.app_res, TopCat.Sheaf.app_res, ha, hb, TopCat.Sheaf.res_res,
      TopCat.Sheaf.res_res, sub_self]
  obtain ⟨c₀, hc₀⟩ := TopCat.Sheaf.sections_exact_of_left_exact hS.exact hS.mono_f d hd
  -- extend it to `W₂` using qc-flasqueness of `F`
  obtain ⟨c, hc⟩ := h₁ hZ hW₂ (inf_le_right : W₁ ⊓ W₂ ≤ W₂) c₀
  -- corrected second lift
  set b' : S.X₂.obj.obj (op W₂) := b + S.f.hom.app (op W₂) c with hb'_def
  have hgb' : S.g.hom.app (op W₂) b' = S.X₃.obj.map (homOfLE e₂).op s := by
    rw [hb'_def, map_add, hfg, add_zero, hb]
  -- `a` and `b'` agree on every open contained in both `W₁` and `W₂`
  have hagree : ∀ (T : Opens X) (t₁ : T ≤ W₁) (t₂ : T ≤ W₂),
      S.X₂.obj.map (homOfLE t₁).op a = S.X₂.obj.map (homOfLE t₂).op b' := by
    intro T t₁ t₂
    have hT : T ≤ W₁ ⊓ W₂ := le_inf t₁ t₂
    have key : S.X₂.obj.map (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)).op a =
        S.X₂.obj.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op b' := by
      rw [hb'_def, map_add, ← TopCat.Sheaf.app_res, hc, hc₀, hd_def, add_sub_cancel]
    have := congrArg (S.X₂.obj.map (homOfLE hT).op) key
    rwa [TopCat.Sheaf.res_res, TopCat.Sheaf.res_res] at this
  -- glue
  let W : Fin 2 → Opens X := ![W₁, W₂]
  let sf : ∀ i : Fin 2, S.X₂.obj.obj (op (W i)) := fun i => match i with
    | 0 => a
    | 1 => b'
  have hWle : ∀ i, W i ≤ W₁ ⊔ W₂ := by
    intro i; fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  have hcover : W₁ ⊔ W₂ ≤ iSup W := sup_le (le_iSup W 0) (le_iSup W 1)
  have hcompat : TopCat.Presheaf.IsCompatible S.X₂.obj W sf := by
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact hagree _ _ _
    · exact (hagree _ _ _).symm
    · rfl
  obtain ⟨e, he, -⟩ := TopCat.Sheaf.existsUnique_gluing' S.X₂ W (W₁ ⊔ W₂) (fun i => homOfLE (hWle i))
    hcover sf hcompat
  refine ⟨e, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' S.X₃ W (W₁ ⊔ W₂) (fun i => homOfLE (hWle i)) hcover
  intro i
  rw [← TopCat.Sheaf.app_res, he i, TopCat.Sheaf.res_res]
  fin_cases i
  · exact ha
  · exact hgb'

end TopCat.Sheaf

end
