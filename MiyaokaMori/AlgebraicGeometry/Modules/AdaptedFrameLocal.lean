import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SubbundleFiltration
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesExactIffLocallyLift
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.AdaptedFrameFrameLemmas

/-! # Local frames adapted to a subbundle filtration

Local frames adapted to a subbundle filtration `0 = E_0 ⊂ E_1 ⊂ ⋯ ⊂ E_r = E`
(`SubbundleFiltration`, with `E_i → E_{i+1}` mono and `coker ≅ Q_i` a line bundle).

An adapted frame on an open `U` (`Data F r _ U`) consists of frames `f_i : Fin i → Γ(E_i, U)` for
every `i`, compatible with the inclusions (`f_{i+1} (castSucc l) = incl_i (f_i l)`), such that the
image of the last vector `f_{i+1} (last i)` in `Q_i` is a frame (generator) of `Q_i` on `U`.

Main result: `exists_data` — around every point `x` there is an open `U ∋ x` carrying an adapted
frame. Proof: induction on the stage `n`. Stage `0`: `E_0` has rank `0`, so `exists_frame_fin`
gives the empty frame (all sections of `E_0` near `x` vanish). Stage `n → n+1`: `Q_n` is a line
bundle, so it has a one-element frame `q` near `x` (`exists_frame_fin`, rank `1`); the projection
`π_n : E_{n+1} → Q_n` is an epimorphism, hence locally surjective on sections
(`epi_iff_locally_surjective_sections`), so after shrinking `q = π_n(s)` for a section `s` of
`E_{n+1}`. Then `(incl_n f_n, s)` is a frame of `E_{n+1}` (`isFrameOn_snocFrame`): linear
independence — apply `π_n` to a vanishing combination to kill the last coefficient (`q` is a frame),
then use injectivity of `incl_n` on sections (mono); spanning — for `t`, write `π_n t = c • q`, then
`t - c • s` lies in `ker π_n = im incl_n` on sections (`sections_of_exact_mono` for the short exact
sequence `E_n → E_{n+1} → coker`), and `im incl_n` is spanned by `incl_n f_n`.

References: Stacks 01C6, 01AG.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.AdaptedFrame

variable {k : Type u} [Field k] {C : SmoothProjectiveCurve k} {r : ℕ}
  {E : VectorBundle C.toVariety} (F : SubbundleFiltration E r)

/-! ## The projections `E_{i+1} → Q_i` and section-level exactness -/

/-- The chosen isomorphism `coker(E_i → E_{i+1}) ≅ Q_i`. -/
def quotIso (i : Fin r) : cokernel (F.incl i) ≅ (F.lineQuotient i).toModules :=
  Classical.choice (F.quotient_iso i)

/-- The projection `E_{i+1} → Q_i`. -/
def toQuot (i : Fin r) : (F.sub i.succ).toModules ⟶ (F.lineQuotient i).toModules :=
  cokernel.π (F.incl i) ≫ (quotIso F i).hom

theorem incl_toQuot (i : Fin r) : F.incl i ≫ toQuot F i = 0 := by
  rw [toQuot, ← Category.assoc, cokernel.condition, zero_comp]

theorem epi_toQuot (i : Fin r) : Epi (toQuot F i) := by
  unfold toQuot
  infer_instance

theorem toQuot_app_incl_app (i : Fin r) (W : C.toScheme.Opens)
    (z : Γ((F.sub i.castSucc).toModules, W)) :
    (toQuot F i).app W ((F.incl i).app W z) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, incl_toQuot]
  rfl

/-- The short exact sequence `E_i → E_{i+1} → coker`. -/
def cokerComplex (i : Fin r) : ShortComplex C.toScheme.Modules :=
  ShortComplex.mk (F.incl i) (cokernel.π (F.incl i)) (cokernel.condition _)

theorem cokerComplex_exact (i : Fin r) : (cokerComplex F i).Exact :=
  ShortComplex.exact_cokernel _

/-- `incl_i` is injective on sections (it is a monomorphism of sheaves). -/
theorem incl_app_injective (i : Fin r) (W : C.toScheme.Opens) :
    Function.Injective ((F.incl i).app W) := by
  haveI : Mono (cokerComplex F i).f := F.mono i
  exact (ModulesLocLiftAux.sections_of_exact_mono (cokerComplex F i) (cokerComplex_exact F i) W).1

/-- On sections, `ker π_i ⊆ im incl_i`. -/
theorem exists_incl_app_eq_of_toQuot_app_eq_zero (i : Fin r) (W : C.toScheme.Opens)
    (t : Γ((F.sub i.succ).toModules, W)) (ht : (toQuot F i).app W t = 0) :
    ∃ z : Γ((F.sub i.castSucc).toModules, W), (F.incl i).app W z = t := by
  haveI : Mono (cokerComplex F i).f := F.mono i
  have h0 : (cokernel.π (F.incl i)).app W t = 0 := by
    have hinj : Function.Injective ((quotIso F i).hom.app W) :=
      (ConcreteCategory.bijective_of_isIso _).1
    apply hinj
    rw [map_zero, ← ht, toQuot, Scheme.Modules.Hom.comp_app]
    rfl
  exact (ModulesLocLiftAux.sections_of_exact_mono (cokerComplex F i) (cokerComplex_exact F i) W).2
    t h0

/-! ## The composite inclusions `E_i → E_r → E` -/

/-- The composite `E_i → E_r` of the inclusions. -/
def chain : ∀ i : Fin (r + 1), (F.sub i).toModules ⟶ (F.sub (Fin.last r)).toModules :=
  Fin.reverseInduction (𝟙 _) (fun i ih => F.incl i ≫ ih)

theorem chain_last : chain F (Fin.last r) = 𝟙 _ := Fin.reverseInduction_last

theorem chain_castSucc (i : Fin r) : chain F i.castSucc = F.incl i ≫ chain F i.succ :=
  Fin.reverseInduction_castSucc i

/-- The composite `E_i → E`. -/
def toTop (i : Fin (r + 1)) : (F.sub i).toModules ⟶ E.toModules := chain F i ≫ F.lastIso.hom

theorem toTop_last : toTop F (Fin.last r) = F.lastIso.hom := by
  rw [toTop, chain_last, Category.id_comp]

theorem toTop_castSucc (i : Fin r) : toTop F i.castSucc = F.incl i ≫ toTop F i.succ := by
  rw [toTop, toTop, chain_castSucc, Category.assoc]

/-! ## Adapted frames -/

/-- An adapted frame on `U` for the stages `0, …, n` of the filtration: frames `f i` of `E_i`,
compatible with the inclusions, such that the image of `f (i+1) (last i)` in `Q_i` generates
`Q_i` on `U`. -/
structure Data (n : ℕ) (hn : n ≤ r) (U : C.toScheme.Opens) where
  /-- the frame of `E_i` -/
  f : ∀ i : Fin (n + 1), Fin (i : ℕ) → Γ((F.sub ⟨i, by omega⟩).toModules, U)
  frame : ∀ i : Fin (n + 1), (F.sub ⟨i, by omega⟩).toModules.IsFrameOn U (f i)
  compat : ∀ (i : Fin n) (l : Fin (i : ℕ)),
    (F.incl ⟨i, by omega⟩).app U (f i.castSucc l) = f i.succ l.castSucc
  quot : ∀ i : Fin n, ∃ q0 : Γ((F.lineQuotient ⟨i, by omega⟩).toModules, U),
    (F.lineQuotient ⟨i, by omega⟩).toModules.IsFrameOn U (fun _ : Fin 1 => q0) ∧
    (toQuot F ⟨i, by omega⟩).app U (f i.succ (Fin.last i)) = q0

variable {F}

/-- Restriction of an adapted frame to a smaller open. -/
def Data.restrict {n : ℕ} {hn : n ≤ r} {U : C.toScheme.Opens} (D : Data F n hn U)
    {W : C.toScheme.Opens} (hW : W ≤ U) : Data F n hn W where
  f i l := (F.sub ⟨i, by omega⟩).toModules.presheaf.map (homOfLE hW).op (D.f i l)
  frame i := isFrameOn_restrict (D.frame i) hW
  compat i l := by
    have h1 := app_res (F.incl ⟨i, by omega⟩) hW (D.f i.castSucc l)
    rw [D.compat i l] at h1
    exact h1
  quot i := by
    obtain ⟨q0, hq, heq⟩ := D.quot i
    refine ⟨(F.lineQuotient ⟨i, by omega⟩).toModules.presheaf.map (homOfLE hW).op q0,
      isFrameOn_restrict hq hW, ?_⟩
    have h1 := app_res (toQuot F ⟨i, by omega⟩) hW (D.f i.succ (Fin.last i))
    rw [heq] at h1
    exact h1

variable (F)

/-! ## Extending a frame by one vector -/

/-- The candidate frame `(incl_i fA, s)` of `E_{i+1}`. -/
def snocFrame (i : Fin r) {W : C.toScheme.Opens} {m : ℕ}
    (fA : Fin m → Γ((F.sub i.castSucc).toModules, W)) (s : Γ((F.sub i.succ).toModules, W)) :
    Fin (m + 1) → Γ((F.sub i.succ).toModules, W) :=
  Fin.snoc (fun l => (F.incl i).app W (fA l)) s

theorem snocFrame_castSucc (i : Fin r) {W : C.toScheme.Opens} {m : ℕ}
    (fA : Fin m → Γ((F.sub i.castSucc).toModules, W)) (s : Γ((F.sub i.succ).toModules, W))
    (l : Fin m) : snocFrame F i fA s l.castSucc = (F.incl i).app W (fA l) := by
  unfold snocFrame
  rw [Fin.snoc_castSucc]

theorem snocFrame_last (i : Fin r) {W : C.toScheme.Opens} {m : ℕ}
    (fA : Fin m → Γ((F.sub i.castSucc).toModules, W)) (s : Γ((F.sub i.succ).toModules, W)) :
    snocFrame F i fA s (Fin.last m) = s := by
  unfold snocFrame
  rw [Fin.snoc_last]

/-- If `fA` is a frame of `E_i` on `W`, `q0` generates `Q_i` on `W` and `π_i s = q0`, then
`(incl_i fA, s)` is a frame of `E_{i+1}` on `W`. -/
theorem isFrameOn_snocFrame (i : Fin r) {W : C.toScheme.Opens} {m : ℕ}
    {fA : Fin m → Γ((F.sub i.castSucc).toModules, W)}
    (hA : (F.sub i.castSucc).toModules.IsFrameOn W fA)
    {s : Γ((F.sub i.succ).toModules, W)} {q0 : Γ((F.lineQuotient i).toModules, W)}
    (hq : (F.lineQuotient i).toModules.IsFrameOn W (fun _ : Fin 1 => q0))
    (hs : (toQuot F i).app W s = q0) :
    (F.sub i.succ).toModules.IsFrameOn W (snocFrame F i fA s) := by
  intro W' h
  have hA' := hA W' h
  have hq' := hq W' h
  have hres_cast : ∀ l : Fin m,
      (F.sub i.succ).toModules.presheaf.map (homOfLE h).op (snocFrame F i fA s l.castSucc) =
        (F.incl i).app W' ((F.sub i.castSucc).toModules.presheaf.map (homOfLE h).op (fA l)) := by
    intro l
    rw [snocFrame_castSucc, app_res]
  have hres_last : (F.sub i.succ).toModules.presheaf.map (homOfLE h).op
      (snocFrame F i fA s (Fin.last m)) = (F.sub i.succ).toModules.presheaf.map (homOfLE h).op s := by
    rw [snocFrame_last]
  have hπs : (toQuot F i).app W' ((F.sub i.succ).toModules.presheaf.map (homOfLE h).op s) =
      (F.lineQuotient i).toModules.presheaf.map (homOfLE h).op q0 := by
    rw [app_res, hs]
  have hπ0 : ∀ (c : Γ(C.toScheme, W')) (l : Fin m), (toQuot F i).app W'
      (c • (F.incl i).app W' ((F.sub i.castSucc).toModules.presheaf.map (homOfLE h).op (fA l))) = 0 := by
    intro c l
    rw [Scheme.Modules.Hom.app_smul, toQuot_app_incl_app F i W', smul_zero]
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fin.sum_univ_castSucc] at hc
    simp only [hres_cast, hres_last] at hc
    have hc_last : c (Fin.last m) = 0 := by
      have h1 := congrArg ((toQuot F i).app W') hc
      rw [map_add, map_sum, map_zero, Scheme.Modules.Hom.app_smul, hπs,
        Finset.sum_eq_zero (fun l _ => hπ0 (c l.castSucc) l), zero_add] at h1
      exact (Fintype.linearIndependent_iff.mp hq'.1) (fun _ => c (Fin.last m))
        (by rw [Fin.sum_univ_one]; exact h1) 0
    have hc_cast : ∀ l : Fin m, c l.castSucc = 0 := by
      rw [hc_last, zero_smul, add_zero] at hc
      have h2 : (F.incl i).app W' (∑ l, c l.castSucc •
          (F.sub i.castSucc).toModules.presheaf.map (homOfLE h).op (fA l)) = (F.incl i).app W' 0 := by
        rw [map_sum, map_zero]
        simp only [Scheme.Modules.Hom.app_smul]
        exact hc
      exact Fintype.linearIndependent_iff.mp hA'.1 _ (incl_app_injective F i W' h2)
    intro l
    refine Fin.lastCases ?_ ?_ l
    · exact hc_last
    · exact hc_cast
  · rw [eq_top_iff]
    intro t _
    have hmemq : (toQuot F i).app W' t ∈ Submodule.span Γ(C.toScheme, W')
        (Set.range fun _ : Fin 1 => (F.lineQuotient i).toModules.presheaf.map (homOfLE h).op q0) := by
      rw [hq'.2]; trivial
    obtain ⟨cq, hcq⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmemq
    rw [Fin.sum_univ_one] at hcq
    have hker : (toQuot F i).app W'
        (t - cq 0 • (F.sub i.succ).toModules.presheaf.map (homOfLE h).op s) = 0 := by
      rw [map_sub, Scheme.Modules.Hom.app_smul, hπs, hcq, sub_self]
    obtain ⟨z, hz⟩ := exists_incl_app_eq_of_toQuot_app_eq_zero F i W' _ hker
    have hmemz : z ∈ Submodule.span Γ(C.toScheme, W')
        (Set.range fun l => (F.sub i.castSucc).toModules.presheaf.map (homOfLE h).op (fA l)) := by
      rw [hA'.2]; trivial
    obtain ⟨cz, hcz⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmemz
    have h4 : ∑ l, cz l • (F.incl i).app W'
        ((F.sub i.castSucc).toModules.presheaf.map (homOfLE h).op (fA l)) =
        t - cq 0 • (F.sub i.succ).toModules.presheaf.map (homOfLE h).op s := by
      rw [← hz, ← hcz, map_sum]
      simp only [Scheme.Modules.Hom.app_smul]
    have ht : t = ∑ l, cz l • (F.sub i.succ).toModules.presheaf.map (homOfLE h).op
        (snocFrame F i fA s l.castSucc) +
        cq 0 • (F.sub i.succ).toModules.presheaf.map (homOfLE h).op (snocFrame F i fA s (Fin.last m)) := by
      simp only [hres_cast, hres_last]
      rw [h4, sub_add_cancel]
    rw [ht]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

/-! ## Existence of adapted frames -/

/-- `Fin.snoc` evaluated at `(last n).succ = last (n+1)`. -/
theorem snoc_succ_last {n : ℕ} {α : Fin (n + 2) → Sort*} (p : ∀ i : Fin (n + 1), α i.castSucc)
    (x : α (Fin.last (n + 1))) : Fin.snoc (α := α) p x (Fin.last n).succ = x :=
  Fin.snoc_last x p

/-- `Fin.snoc` evaluated at `(castSucc j).succ = castSucc j.succ`. -/
theorem snoc_succ_castSucc {n : ℕ} {α : Fin (n + 2) → Sort*} (p : ∀ i : Fin (n + 1), α i.castSucc)
    (x : α (Fin.last (n + 1))) (j : Fin n) :
    Fin.snoc (α := α) p x j.castSucc.succ = p j.succ :=
  Fin.snoc_castSucc x p j.succ

variable {F}

/-- One more stage: from an adapted frame up to stage `n` on `W`, a section `s` of `E_{n+1}` on
`W` whose image generates `Q_n` on `W`, build an adapted frame up to stage `n + 1`. -/
def Data.snoc {n : ℕ} (hn : n + 1 ≤ r) {W : C.toScheme.Opens}
    (D : Data F n (Nat.le_of_succ_le hn) W)
    (s : Γ((F.sub (⟨n, hn⟩ : Fin r).succ).toModules, W))
    {q0 : Γ((F.lineQuotient ⟨n, hn⟩).toModules, W)}
    (hq : (F.lineQuotient ⟨n, hn⟩).toModules.IsFrameOn W (fun _ : Fin 1 => q0))
    (hs : (toQuot F ⟨n, hn⟩).app W s = q0) : Data F (n + 1) hn W where
  f := Fin.snoc (α := fun i : Fin (n + 2) => Fin (i : ℕ) → Γ((F.sub ⟨i, by omega⟩).toModules, W))
    (fun i => D.f i) (snocFrame F ⟨n, hn⟩ (D.f (Fin.last n)) s)
  frame i := by
    refine Fin.lastCases ?_ ?_ i
    · rw [Fin.snoc_last]
      exact isFrameOn_snocFrame F ⟨n, hn⟩ (D.frame (Fin.last n)) hq hs
    · intro j
      rw [Fin.snoc_castSucc]
      exact D.frame j
  compat i := by
    refine Fin.lastCases ?_ ?_ i
    · intro l
      rw [Fin.snoc_castSucc, snoc_succ_last, snocFrame_castSucc]
      rfl
    · intro j l
      rw [Fin.snoc_castSucc, snoc_succ_castSucc]
      exact D.compat j l
  quot i := by
    refine Fin.lastCases ?_ ?_ i
    · refine ⟨q0, hq, ?_⟩
      rw [snoc_succ_last]
      have h1 : (toQuot F ⟨n, hn⟩).app W
          (snocFrame F ⟨n, hn⟩ (m := n) (D.f (Fin.last n)) s (Fin.last n)) = q0 := by
        rw [snocFrame_last]
        exact hs
      exact h1
    · intro j
      obtain ⟨q1, hq1, heq⟩ := D.quot j
      refine ⟨q1, hq1, ?_⟩
      rw [snoc_succ_castSucc]
      exact heq

/-- The empty adapted frame at stage `0` on an open where `E_0` has no nonzero sections. -/
def Data.zero {U : C.toScheme.Opens}
    (hU : ∀ (W : C.toScheme.Opens) (_ : W ≤ U) (t : Γ((F.sub ⟨0, Nat.succ_pos r⟩).toModules, W)),
      t = 0) : Data F 0 (Nat.zero_le r) U where
  f i l := Fin.elim0 (Fin.cast (Nat.lt_one_iff.mp i.isLt) l)
  frame i := by
    obtain ⟨i, hi⟩ := i
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    intro W h
    have : IsEmpty (Fin ((⟨0, hi⟩ : Fin 1) : ℕ)) := ⟨fun l => Fin.elim0 l⟩
    refine ⟨linearIndependent_empty_type, ?_⟩
    rw [eq_top_iff]
    intro t _
    rw [hU W h t]
    exact Submodule.zero_mem _
  compat i := i.elim0
  quot i := i.elim0

variable (F)

/-- Around every point there is an adapted frame up to every stage `n ≤ r`. -/
theorem exists_data (x : C.toScheme) :
    ∀ (n : ℕ) (hn : n ≤ r), ∃ U : C.toScheme.Opens, x ∈ U ∧ Nonempty (Data F n hn U) := by
  intro n
  induction n with
  | zero =>
    intro _
    have hrk : Scheme.Modules.rankAtStalk (F.sub ⟨0, Nat.succ_pos r⟩).toModules x = 0 := by
      rw [(F.sub _).rankAtStalk_eq x, F.rank_eq]
    obtain ⟨U, hxU, e, he⟩ := @exists_frame_fin _ (F.sub ⟨0, Nat.succ_pos r⟩).toModules
      (F.sub ⟨0, Nat.succ_pos r⟩).locallyFree (F.sub ⟨0, Nat.succ_pos r⟩).isFiniteType x
    refine ⟨U, hxU, ⟨Data.zero (F := F) fun W h t => ?_⟩⟩
    have hsp := (he W h).2
    have : IsEmpty (Fin (Scheme.Modules.rankAtStalk (F.sub ⟨0, Nat.succ_pos r⟩).toModules x)) := by
      rw [hrk]; infer_instance
    rw [Set.range_eq_empty, Submodule.span_empty] at hsp
    have ht : t ∈ (⊥ : Submodule Γ(C.toScheme, W) Γ((F.sub ⟨0, Nat.succ_pos r⟩).toModules, W)) := by
      rw [hsp]; trivial
    exact (Submodule.mem_bot _).mp ht
  | succ n ih =>
    intro hn
    obtain ⟨U, hxU, ⟨D⟩⟩ := ih (Nat.le_of_succ_le hn)
    have hrkQ : Scheme.Modules.rankAtStalk (F.lineQuotient ⟨n, hn⟩).toModules x = 1 := by
      rw [(F.lineQuotient ⟨n, hn⟩).toVectorBundle.rankAtStalk_eq x,
        (F.lineQuotient ⟨n, hn⟩).rank_eq_one]
    obtain ⟨V, hxV, q, hq⟩ := exists_frame_fin (F.lineQuotient ⟨n, hn⟩).toModules x
    have hq1 : (F.lineQuotient ⟨n, hn⟩).toModules.IsFrameOn V
        (fun _ : Fin 1 => q ((finCongr hrkQ).symm 0)) := by
      have e : (fun _ : Fin 1 => q ((finCongr hrkQ).symm 0)) =
          fun i => q ((finCongr hrkQ).symm i) := by
        funext i
        rw [Fin.fin_one_eq_zero i]
      rw [e]
      exact isFrameOn_reindex hq (finCongr hrkQ).symm
    have := epi_toQuot F ⟨n, hn⟩
    obtain ⟨W, hWUV, hxW, s, hs⟩ :=
      (Scheme.Modules.epi_iff_locally_surjective_sections (toQuot F ⟨n, hn⟩)).mp inferInstance
        (U ⊓ V) ((F.lineQuotient ⟨n, hn⟩).toModules.presheaf.map (homOfLE inf_le_right).op
          (q ((finCongr hrkQ).symm 0))) x ⟨hxU, hxV⟩
    refine ⟨W, hxW, ⟨Data.snoc hn (D.restrict (hWUV.trans inf_le_left)) s
      (q0 := (F.lineQuotient ⟨n, hn⟩).toModules.presheaf.map
        (homOfLE (hWUV.trans inf_le_right)).op (q ((finCongr hrkQ).symm 0))) ?_ ?_⟩⟩
    · exact isFrameOn_restrict hq1 (hWUV.trans inf_le_right)
    · rw [hs, map_map_res]

end MiyaokaMori.AdaptedFrame

end
