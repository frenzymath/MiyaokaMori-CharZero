import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternating
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternatingElementwise
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechAlternatingFlasqueAcyclic
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule

/-! # Flasque modules are Čech-acyclic

Let `X` be a scheme and `M` an `O_X`-module whose underlying abelian sheaf is flasque
(`TopCat.Sheaf.IsFlasque M.toAddCommGrpSheaf`). Then for every finite family of opens
`U : Fin n → X.Opens` and every `p > 0`, the alternating Čech complex `cechComplexAlt U M` has zero
homology in degree `p`.

Proof sketch:
1. By the elementwise description of the Čech complex it suffices to check that cocycle families
   are coboundary families.
2. Apply the abstract acyclicity criterion (`CechAlternatingFlasqueAcyclic.lean`, with `A = ℤ`,
   `N(W) = Γ(M, W)`, `V(σ) = ⋂_k U_{σ_k}`); it remains to verify the extension property: given `σ`,
   `j ∉ σ`, `J` (disjoint from `σ`, `j ∉ J`) and `y ∈ Γ(M, U_σ ∩ U_j)` vanishing on every
   `U_σ ∩ U_j ∩ U_i` (`i ∈ J`), extend `y`.
3. Take the opens `W_none = U_{σ∪{j}}`, `W_i = U_{σ∪{i}}` (`i ∈ J`) with sections `y, 0, …, 0`; they
   agree on pairwise intersections (`y` vanishes on `W_none ∩ W_i ⊆ U_{σ∪{j,i}}`), so they glue to
   `g ∈ Γ(M, ⋃ W)` (`TopCat.Sheaf.existsUnique_gluing`); `⋃ W ⊆ U_σ` and flasqueness (restriction is
   surjective, `AddCommGrpCat.epi_iff_surjective`) give `x ∈ Γ(M, U_σ)` with `x|_{⋃W} = g`, hence
   `x|_{W_none} = y` and `x|_{W_i} = 0`.

Source: the standard argument that flasque sheaves are Čech-acyclic for every open cover.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} {n : ℕ} (U : Fin n → X.Opens) (M : X.Modules)

theorem iInf_ins {q : ℕ} (F : Fin n → X.Opens) (σ : Fin (q + 1) ↪o Fin n) (j : Fin n)
    (hj : j ∉ Set.range σ) :
    ⨅ k, F (CechAltAlg.ins σ j hj k) = (⨅ k, F (σ k)) ⊓ F j := by
  apply le_antisymm
  · refine le_inf (le_iInf fun k => ?_) ?_
    · have := iInf_le (fun k => F (CechAltAlg.ins σ j hj k)) ((CechAltAlg.pos σ j hj).succAbove k)
      rwa [CechAltAlg.ins_succAbove] at this
    · have := iInf_le (fun k => F (CechAltAlg.ins σ j hj k)) (CechAltAlg.pos σ j hj)
      rwa [CechAltAlg.ins_pos] at this
  · refine le_iInf fun k => ?_
    have hk : CechAltAlg.ins σ j hj k ∈ Set.range (CechAltAlg.ins σ j hj) := ⟨k, rfl⟩
    rw [CechAltAlg.range_ins] at hk
    rcases hk with hk | ⟨i, hi⟩
    · rw [hk]
      exact inf_le_right
    · rw [← hi]
      exact inf_le_left.trans (iInf_le _ i)

/-- The extension property of a flasque sheaf. -/
theorem flasque_ext [hfl : TopCat.Sheaf.IsFlasque M.toAddCommGrpSheaf] {q : ℕ}
    (σ : Fin (q + 1) ↪o Fin n) (j : Fin n) (hj : j ∉ Set.range σ) (J : Finset (Fin n))
    (hjJ : j ∉ J) (hJσ : ∀ i ∈ J, i ∉ Set.range σ)
    (y : Γ(M, ⨅ k, U (CechAltAlg.ins σ j hj k)))
    (hy : ∀ i ∈ J, ∀ hi : i ∉ Set.range (CechAltAlg.ins σ j hj),
      ∀ hle : (⨅ k, U (CechAltAlg.ins (CechAltAlg.ins σ j hj) i hi k)) ≤
        ⨅ k, U (CechAltAlg.ins σ j hj k), famRes M hle y = 0) :
    ∃ x : Γ(M, ⨅ k, U (σ k)),
      (∀ hle : (⨅ k, U (CechAltAlg.ins σ j hj k)) ≤ ⨅ k, U (σ k), famRes M hle x = y) ∧
      ∀ i ∈ J, ∀ hi : i ∉ Set.range σ,
        ∀ hle : (⨅ k, U (CechAltAlg.ins σ i hi k)) ≤ ⨅ k, U (σ k), famRes M hle x = 0 := by
  classical
  let W : Option {i : Fin n // i ∈ J} → X.Opens := fun a =>
    match a with
    | none => ⨅ k, U (CechAltAlg.ins σ j hj k)
    | some i => ⨅ k, U (CechAltAlg.ins σ i.1 (hJσ i.1 i.2) k)
  let sf : ∀ a, Γ(M, W a) := fun a =>
    match a with
    | none => y
    | some _ => 0
  have hzero : ∀ (i : {i : Fin n // i ∈ J}) (T : X.Opens) (h1 : T ≤ W none) (_ : T ≤ W (some i)),
      famRes M h1 y = 0 := by
    intro i T h1 h2
    have hi : i.1 ∉ Set.range (CechAltAlg.ins σ j hj) := by
      rw [CechAltAlg.range_ins]
      rintro (h | h)
      · exact hjJ (h ▸ i.2)
      · exact hJσ i.1 i.2 h
    have hle : (⨅ k, U (CechAltAlg.ins (CechAltAlg.ins σ j hj) i.1 hi k)) ≤
        ⨅ k, U (CechAltAlg.ins σ j hj k) := by
      rw [iInf_ins]
      exact inf_le_left
    have hT : T ≤ ⨅ k, U (CechAltAlg.ins (CechAltAlg.ins σ j hj) i.1 hi k) := by
      rw [iInf_ins]
      refine le_inf h1 (h2.trans ?_)
      show (⨅ k, U (CechAltAlg.ins σ i.1 (hJσ i.1 i.2) k)) ≤ U i.1
      rw [iInf_ins]
      exact inf_le_right
    rw [← famRes_comp M hle hT, hy i.1 i.2 hi hle, map_zero]
  have hcompat : TopCat.Presheaf.IsCompatible M.toAddCommGrpSheaf.obj W sf := by
    intro a b
    rcases a with _ | a <;> rcases b with _ | b
    · rfl
    · exact (hzero b _ inf_le_left inf_le_right).trans (map_zero _).symm
    · exact (map_zero _).trans (hzero a _ inf_le_right inf_le_left).symm
    · exact (map_zero _).trans (map_zero _).symm
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing (F := M.toAddCommGrpSheaf) W sf hcompat
  have hWle : iSup W ≤ ⨅ k, U (σ k) := by
    refine iSup_le fun a => ?_
    rcases a with _ | a
    · show (⨅ k, U (CechAltAlg.ins σ j hj k)) ≤ _
      rw [iInf_ins]
      exact inf_le_left
    · show (⨅ k, U (CechAltAlg.ins σ a.1 (hJσ a.1 a.2) k)) ≤ _
      rw [iInf_ins]
      exact inf_le_left
  have hepi : Epi (M.toAddCommGrpSheaf.obj.map (homOfLE hWle).op) := hfl.epi _
  obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective _).1 hepi g
  refine ⟨x, ?_, ?_⟩
  · intro hle
    have h1 : famRes M (le_iSup W none) (famRes M hWle x) = y := by
      show M.presheaf.map _ (M.presheaf.map _ x) = y
      rw [show M.presheaf.map (homOfLE hWle).op x = g from hx]
      exact hg none
    exact (famRes_comp M hWle (le_iSup W none) x).symm.trans h1
  · intro i hiJ hi hle
    have h1 : famRes M (le_iSup W (some ⟨i, hiJ⟩)) (famRes M hWle x) = 0 := by
      show M.presheaf.map _ (M.presheaf.map _ x) = 0
      rw [show M.presheaf.map (homOfLE hWle).op x = g from hx]
      exact hg (some ⟨i, hiJ⟩)
    exact (famRes_comp M hWle (le_iSup W (some ⟨i, hiJ⟩)) x).symm.trans h1

/-- Flasque ⇒ the alternating Čech complex of any finite family of opens is acyclic in positive
degrees. -/
theorem cechComplexAlt_homology_subsingleton_of_isFlasque
    [TopCat.Sheaf.IsFlasque M.toAddCommGrpSheaf] (p : ℕ) (hp : 0 < p) :
    Subsingleton (((cechComplexAlt U M).homology (p : ℤ)) : Type u) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  apply cechComplexAlt_homology_subsingleton_of_family
  intro s hs
  have key := CechAltAlg.exists_d_eq_of_ext (A := ℤ)
    (fun q (σ : Fin (q + 1) ↪o Fin n) => ⨅ k, U (σ k))
    (fun W : X.Opens => Γ(M, W)) (fun h => famRes M h) (fun _ τ k => cech_face_le U τ k)
    (fun h h' x => famRes_comp M h h' x)
    (fun q σ j hj J hjJ hJσ y hy => by
      obtain ⟨x, hx1, hx2⟩ := flasque_ext U M σ j hj J hjJ hJσ y (fun i hiJ hi hle => hy i hiJ hi)
      exact ⟨x, hx1 _, fun i hiJ hi => hx2 i hiJ hi _⟩)
    q s (by rw [famD_eq]; exact hs)
  obtain ⟨t, ht⟩ := key
  rw [famD_eq] at ht
  exact ⟨t, ht⟩

end AlgebraicGeometry.Scheme.Modules

end
