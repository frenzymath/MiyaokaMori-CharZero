import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternating
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternatingElementwise
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechAlternatingFlasque
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesExactIffLocallyLift
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks09sx

/-! # Čech acyclicity of injective modules and surjectivity on sections (Stacks 01EP, 01EU)

(a) Stacks 01EP: the (ordered/alternating) Čech complex of an injective `O_X`-module on any finite
family of opens has zero homology in positive degrees. (b) Stacks 01EU: if `0 → F → G → H → 0` is a
short exact sequence of `O_X`-modules, `V` is open, and a family of finite open covers of `V` is
cofinal among the open covers of `V` with `Ȟ¹(𝒰, F) = 0` for each of them, then `G(V) → H(V)` is
surjective.

Source: Stacks 01EP (`cohomology-lemma-injective-trivial-cech`), 01EU (`cohomology-lemma-ses-cech-h1`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- (a) Stacks 01EP: the alternating Čech complex of an injective `O_X`-module `I` on any finite
family of opens `U` has zero homology in positive degrees. The Čech complex is `cechComplexAlt`
(ordered indices `i₀ < ⋯ < i_p`). -/

theorem AlgebraicGeometry.Scheme.Modules.cechComplexAlt_homology_subsingleton_of_injective
    {X : AlgebraicGeometry.Scheme.{u}} (I : X.Modules) [CategoryTheory.Injective I]
    {n : ℕ} (U : Fin n → X.Opens) (p : ℕ) (hp : 0 < p) :
    Subsingleton (((AlgebraicGeometry.Scheme.Modules.cechComplexAlt U I).homology (p : ℤ)) : Type u) := by
  have : TopCat.Sheaf.IsFlasque I.toAddCommGrpSheaf :=
    AlgebraicGeometry.Scheme.Modules.isFlasque_of_injective I
  exact AlgebraicGeometry.Scheme.Modules.cechComplexAlt_homology_subsingleton_of_isFlasque U I p hp

namespace Stacks01euAux

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

variable {n : ℕ}

/-- The one-point index tuple. -/
def singleEmb (i : Fin n) : Fin 1 ↪o Fin n :=
  OrderEmbedding.ofStrictMono (fun _ => i) (fun a b h => absurd h (by
    rw [Subsingleton.elim a b]
    exact lt_irrefl _))

/-- The two-point index tuple `i < k`. -/
def pairEmb (i k : Fin n) (h : i < k) : Fin 2 ↪o Fin n :=
  OrderEmbedding.ofStrictMono ![i, k] (by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all)

theorem face_pair_zero (i k : Fin n) (h : i < k) :
    CechAltAlg.face (pairEmb i k h) 0 = singleEmb k := by
  apply RelEmbedding.ext
  intro m
  fin_cases m
  rfl

theorem face_pair_one (i k : Fin n) (h : i < k) :
    CechAltAlg.face (pairEmb i k h) 1 = singleEmb i := by
  apply RelEmbedding.ext
  intro m
  fin_cases m
  rfl

end Stacks01euAux

theorem AlgebraicGeometry.Scheme.Modules.surjective_sections_of_cech_h1
    {X : AlgebraicGeometry.Scheme.{u}} (S : CategoryTheory.ShortComplex X.Modules) (hS : S.ShortExact)
    (V : X.Opens) (Cov : Set (Σ n : ℕ, Fin n → X.Opens))
    (hcov : ∀ c ∈ Cov, ⨆ i, c.2 i = V)
    (hcof : ∀ (ι : Type u) (W : ι → X.Opens), ⨆ j, W j = V → ∃ c ∈ Cov, ∀ i, ∃ j, c.2 i ≤ W j)
    (hH1 : ∀ c ∈ Cov,
      Subsingleton (((AlgebraicGeometry.Scheme.Modules.cechComplexAlt c.2 S.X₁).homology (1 : ℤ)) : Type u)) :
    Function.Surjective (S.g.val.app (Opposite.op V)).hom := by
  classical
  open Stacks01euAux in
  intro s0
  obtain ⟨s, hs0⟩ : ∃ s : Γ(S.X₃, V), s = s0 := ⟨s0, rfl⟩
  have hepi : Epi S.g := hS.epi_g
  have hmono : Mono S.f := hS.mono_f
  have hloc := (AlgebraicGeometry.Scheme.Modules.epi_iff_locally_surjective_sections S.g).1 hepi V s
  choose Vp hVp hpV y hy using fun p : V => hloc p.1 p.2
  have hcovW : ⨆ p : V, Vp p = V :=
    le_antisymm (iSup_le hVp) (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hpV ⟨x, hx⟩⟩)
  obtain ⟨⟨n, U⟩, hc, href⟩ := hcof V Vp hcovW
  choose jj hjj using href
  have hUV : ⨆ i, U i = V := hcov _ hc
  have hH := hH1 _ hc
  have hle : ∀ {q : ℕ} (σ : Fin (q + 1) ↪o Fin n), (⨅ k, U (σ k)) ≤ V := fun σ =>
    (iInf_le _ 0).trans ((le_iSup U _).trans hUV.le)
  have hfg : ∀ (W : X.Opens) (z : Γ(S.X₁, W)), S.g.app W (S.f.app W z) = 0 := fun W z =>
    congrArg (fun φ : S.X₁ ⟶ S.X₃ => (AlgebraicGeometry.Scheme.Modules.Hom.app φ W) z) S.zero
  -- local lifts
  let t0 : CechFamily U S.X₂ 0 := fun σ =>
    S.X₂.presheaf.map (homOfLE ((iInf_le (fun k => U (σ k)) 0).trans (hjj (σ 0)))).op (y (jj (σ 0)))
  have hgt0 : ∀ σ : Fin 1 ↪o Fin n, S.g.app _ (t0 σ) = S.X₃.presheaf.map (homOfLE (hle σ)).op s := by
    intro σ
    have h1 : (⨅ k, U (σ k)) ≤ Vp (jj (σ 0)) := (iInf_le (fun k => U (σ k)) 0).trans (hjj (σ 0))
    refine (app_map S.g h1 (y (jj (σ 0)))).trans ?_
    refine (congrArg (fun z => S.X₃.presheaf.map (homOfLE h1).op z) (hy (jj (σ 0)))).trans ?_
    exact famRes_comp S.X₃ (hVp _) h1 s
  -- for the constant family `s|`, the alternating sum vanishes
  have hconst : ∀ (H : CechFamily U S.X₃ 0),
      (∀ σ, H σ = S.X₃.presheaf.map (homOfLE (hle σ)).op s) → cechFamilyD U S.X₃ 0 H = 0 := by
    intro H hH'
    funext τ
    show ∑ k : Fin 2, ((-1 : ℤ) ^ (k : ℕ)) • S.X₃.presheaf.map _ (H _) = 0
    rw [Fin.sum_univ_two, hH', hH']
    have e0 := famRes_comp S.X₃ (hle (CechAltAlg.face τ 0)) (cech_face_le U τ 0) s
    have e1 := famRes_comp S.X₃ (hle (CechAltAlg.face τ 1)) (cech_face_le U τ 1) s
    refine (congrArg₂ (fun a b => ((-1 : ℤ) ^ ((0 : Fin 2) : ℕ)) • a + ((-1 : ℤ) ^ ((1 : Fin 2) : ℕ)) • b)
      e0 e1).trans ?_
    simp
  have hgcG : ∀ τ, S.g.app _ (cechFamilyD U S.X₂ 0 t0 τ) = 0 := by
    intro τ
    have h1 := congrFun (cechFamilyD_map U S.g 0 t0) τ
    have h2 := congrFun (hconst (fun σ => S.g.app _ (t0 σ)) hgt0) τ
    exact h1.trans h2
  choose fF hfF using fun τ =>
    (ModulesLocLiftAux.sections_of_exact_mono S hS.exact _).2 (cechFamilyD U S.X₂ 0 t0 τ) (hgcG τ)
  have hcoc : cechFamilyD U S.X₁ 1 fF = 0 := by
    funext τ
    apply (ModulesLocLiftAux.sections_of_exact_mono S hS.exact _).1
    have h1 := congrFun (cechFamilyD_map U S.f 1 fF) τ
    have h2 : (fun σ => S.f.app _ (fF σ)) = cechFamilyD U S.X₂ 0 t0 := funext hfF
    rw [h2, cechFamilyD_comp] at h1
    exact h1.trans (map_zero _).symm
  obtain ⟨e, he⟩ := exists_family_of_homology_subsingleton U S.X₁ 0 hH fF hcoc
  let t1 : CechFamily U S.X₂ 0 := t0 - fun σ => S.f.app _ (e σ)
  have hd1 : cechFamilyD U S.X₂ 0 t1 = 0 := by
    rw [cechFamilyD_sub, ← cechFamilyD_map, he, sub_eq_zero]
    exact (funext hfF).symm
  have hg1 : ∀ σ : Fin 1 ↪o Fin n, S.g.app _ (t1 σ) = S.X₃.presheaf.map (homOfLE (hle σ)).op s := by
    intro σ
    show S.g.app _ (t0 σ - S.f.app _ (e σ)) = _
    rw [map_sub, hfg, sub_zero, hgt0]
  -- gluing
  let W' : Fin n → X.Opens := fun i => ⨅ k, U (singleEmb i k)
  have hW'le : ∀ i, W' i ≤ U i := fun i => iInf_le (fun k => U (singleEmb i k)) 0
  have hW'ge : ∀ i, U i ≤ W' i := fun i => le_iInf fun _ => le_rfl
  let sf : ∀ i, Γ(S.X₂, W' i) := fun i => t1 (singleEmb i)
  have hlt : ∀ (i k : Fin n) (h : i < k) (T : X.Opens) (hi : T ≤ W' i) (hk : T ≤ W' k),
      famRes S.X₂ hi (sf i) = famRes S.X₂ hk (sf k) := by
    intro i k h T hi hk
    have hT : T ≤ ⨅ m, U (pairEmb i k h m) := by
      refine le_iInf fun m => ?_
      fin_cases m
      · exact hi.trans (hW'le i)
      · exact hk.trans (hW'le k)
    have h0 := congrFun hd1 (pairEmb i k h)
    change ∑ m : Fin 2, ((-1 : ℤ) ^ (m : ℕ)) • famRes S.X₂ (cech_face_le U (pairEmb i k h) m)
      (t1 (CechAltAlg.face (pairEmb i k h) m)) = 0 at h0
    rw [Fin.sum_univ_two] at h0
    have hle0 : (⨅ m, U (pairEmb i k h m)) ≤ W' k := le_iInf fun _ => iInf_le (fun m => U (pairEmb i k h m)) 1
    have hle1 : (⨅ m, U (pairEmb i k h m)) ≤ W' i := le_iInf fun _ => iInf_le (fun m => U (pairEmb i k h m)) 0
    rw [CechAltAlg.transport_res (A := ℤ) (fun q (σ : Fin (q + 1) ↪o Fin n) => ⨅ k, U (σ k))
        (fun W : X.Opens => Γ(S.X₂, W)) (fun h => famRes S.X₂ h) t1 (face_pair_zero i k h)
        (cech_face_le U (pairEmb i k h) 0) hle0,
      CechAltAlg.transport_res (A := ℤ) (fun q (σ : Fin (q + 1) ↪o Fin n) => ⨅ k, U (σ k))
        (fun W : X.Opens => Γ(S.X₂, W)) (fun h => famRes S.X₂ h) t1 (face_pair_one i k h)
        (cech_face_le U (pairEmb i k h) 1) hle1] at h0
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul] at h0
    rw [← sub_eq_add_neg, sub_eq_zero] at h0
    have h1 := congrArg (famRes S.X₂ hT) h0
    rw [famRes_comp, famRes_comp] at h1
    exact h1.symm
  have hcompat : TopCat.Presheaf.IsCompatible S.X₂.toAddCommGrpSheaf.obj W' sf := by
    intro i k
    rcases lt_trichotomy i k with h | h | h
    · exact hlt i k h _ inf_le_left inf_le_right
    · subst h
      rfl
    · exact (hlt k i h _ inf_le_right inf_le_left).symm
  have hcover : V ≤ iSup W' := by
    rw [← hUV]
    exact iSup_mono hW'ge
  have hW'V : ∀ i, W' i ≤ V := fun i => (hW'le i).trans ((le_iSup U i).trans hUV.le)
  obtain ⟨u, hu, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := S.X₂.toAddCommGrpSheaf) W' V
    (fun i => homOfLE (hW'V i)) hcover sf hcompat
  refine ⟨u, ?_⟩
  rw [← hs0]
  show S.g.app V u = s
  apply TopCat.Sheaf.eq_of_locally_eq' (F := S.X₃.toAddCommGrpSheaf) W' V
    (fun i => homOfLE (hW'V i)) hcover
  intro i
  refine (app_map S.g (hW'V i) u).symm.trans ?_
  refine (congrArg (fun z => S.g.app (W' i) z) (hu i)).trans ?_
  exact hg1 (singleEmb i)

end
