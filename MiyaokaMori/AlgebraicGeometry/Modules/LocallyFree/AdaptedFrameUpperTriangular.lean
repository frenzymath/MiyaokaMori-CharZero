import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.MatrixCocycle
import MiyaokaMori.AlgebraicGeometry.Modules.SubbundleFiltration
import MiyaokaMori.AlgebraicGeometry.Modules.AdaptedFrameLocal

/-! # Adapted frames give upper triangular transition matrices

Frames adapted to a subbundle filtration `0 = E_0 ⊂ ⋯ ⊂ E_r = E` give an upper triangular
trivialization cocycle of `E` whose diagonal entries are trivialization cocycles of the line
quotients `Q_i = E_{i+1}/E_i` (the upper triangular transition matrices (2.7) of §2 of
the paper).

Proof. Around every point `x` there is an open `U_x` with an adapted
frame (`AdaptedFrame.exists_data`, `AdaptedFrameLocal.lean`): frames `f_i` of `E_i` on `U_x`,
compatible with the inclusions, such that `q_i := π_i (f_{i+1} (last i))` generates `Q_i`. Take the
cover `U_x` (`x : C`), the frames `e_x := lastIso (f_r)` of `E` and the matrices
`g_{xx'} := ` coordinates of `e_{x'}` in the frame `e_x` on `U_x ⊓ U_{x'}` (`coords`).
* `g` is a trivialization cocycle of `E` by construction.
* Key relation (`Data.exists_overlap_coords`): on `U_x ⊓ U_{x'}`, write `f'_{j+1} (last j)` in the
  frame `f_{j+1}` with coordinates `d`; pushing to `E` gives `e'_j = ∑_{l ≤ j} d_l e_l`, and pushing to
  `Q_j` kills the first `j` vectors (they come from `E_j`), so `q'_j = d_{last} q_j`.
* Upper triangular: by uniqueness of coordinates `g_{ij} = d_i` for `i ≤ j` and `0` for `i > j`.
* Diagonal: `g_{jj} = d_{last}`, so `q'_j = g_{jj} q_j`, a `1 × 1` trivialization cocycle of `Q_j`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped AlgebraicGeometry

namespace MiyaokaMori.AdaptedFrame

open AlgebraicGeometry

/-! ## Extension by zero of a family on `Fin (j+1)` to `Fin r` -/

/-- Extension by zero of `d : Fin (j+1) → R` to `Fin r`. -/
def extendZero {R : Type*} [Zero R] {r : ℕ} (j : Fin r) (d : Fin ((j : ℕ) + 1) → R) (i : Fin r) : R :=
  if h : (i : ℕ) < (j : ℕ) + 1 then d ⟨i, h⟩ else 0

theorem extendZero_castLE {R : Type*} [Zero R] {r : ℕ} (j : Fin r) (d : Fin ((j : ℕ) + 1) → R)
    (l : Fin ((j : ℕ) + 1)) : extendZero j d (Fin.castLE j.isLt l) = d l := by
  unfold extendZero
  exact dif_pos (show ((Fin.castLE j.isLt l : Fin r) : ℕ) < (j : ℕ) + 1 from l.isLt)

theorem extendZero_eq_zero {R : Type*} [Zero R] {r : ℕ} (j : Fin r) (d : Fin ((j : ℕ) + 1) → R)
    (i : Fin r) (h : ¬ (i : ℕ) < (j : ℕ) + 1) : extendZero j d i = 0 := by
  unfold extendZero
  exact dif_neg h

theorem sum_extendZero_smul {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {r : ℕ}
    (j : Fin r) (d : Fin ((j : ℕ) + 1) → R) (v : Fin r → M) :
    ∑ i, extendZero j d i • v i = ∑ l, d l • v (Fin.castLE j.isLt l) := by
  classical
  symm
  calc ∑ l, d l • v (Fin.castLE j.isLt l)
      = ∑ l, extendZero j d (Fin.castLEEmb j.isLt l) • v (Fin.castLEEmb j.isLt l) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        show d l • v (Fin.castLE j.isLt l) = extendZero j d (Fin.castLE j.isLt l) • v (Fin.castLE j.isLt l)
        rw [extendZero_castLE]
    _ = ∑ i ∈ Finset.univ.map (Fin.castLEEmb j.isLt), extendZero j d i • v i :=
        (Finset.sum_map Finset.univ (Fin.castLEEmb j.isLt) (fun i => extendZero j d i • v i)).symm
    _ = ∑ i, extendZero j d i • v i := by
        refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
        have hni : ¬ (i : ℕ) < (j : ℕ) + 1 := fun h =>
          hi (Finset.mem_map.mpr ⟨⟨i, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        rw [extendZero_eq_zero j d i hni, zero_smul]

/-! ## Accessors of a full adapted frame (`n = r`) -/

variable {k : Type u} [Field k] {C : SmoothProjectiveCurve k} {r : ℕ}
  {E : VectorBundle C.toVariety} {F : SubbundleFiltration E r}

section Full

variable {U : C.toScheme.Opens} (D : Data F r le_rfl U)

/-- The frame of `E_{j+1}`, indexed by `Fin (j+1)`. -/
def Data.frS (j : Fin r) : Fin ((j : ℕ) + 1) → Γ((F.sub j.succ).toModules, U) := D.f j.succ

theorem Data.frS_frame (j : Fin r) : (F.sub j.succ).toModules.IsFrameOn U (D.frS j) :=
  D.frame j.succ

/-- The frame of `E` induced by an adapted frame: `lastIso (f_r)`. -/
def Data.top : Fin r → Γ(E.toModules, U) := fun l => F.lastIso.hom.app U (D.f (Fin.last r) l)

theorem Data.top_frame : E.toModules.IsFrameOn U D.top :=
  isFrameOn_map_iso F.lastIso.hom (D.frame (Fin.last r))

theorem Data.compat' (i : Fin r) (l : Fin (i : ℕ)) :
    (F.incl i).app U (D.f i.castSucc l) = D.f i.succ l.castSucc :=
  D.compat i l

theorem Data.toTop_f : ∀ (i : Fin (r + 1)) (l : Fin (i : ℕ)),
    (toTop F i).app U (D.f i l) = D.top (Fin.castLE (Nat.le_of_lt_succ i.isLt) l) := by
  intro i
  induction i using Fin.reverseInduction with
  | last =>
    intro l
    rw [toTop_last]
    rfl
  | cast i ih =>
    intro l
    rw [toTop_castSucc, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, D.compat' i l,
      ih l.castSucc]
    rfl

theorem Data.toTop_frS (j : Fin r) (l : Fin ((j : ℕ) + 1)) :
    (toTop F j.succ).app U (D.frS j l) = D.top (Fin.castLE j.isLt l) :=
  D.toTop_f j.succ l

theorem Data.toQuot_frS_castSucc (j : Fin r) (l : Fin (j : ℕ)) :
    (toQuot F j).app U (D.frS j l.castSucc) = 0 := by
  have h := D.compat' j l
  show (toQuot F j).app U (D.f j.succ l.castSucc) = 0
  rw [← h]
  exact toQuot_app_incl_app F j U _

/-- The generator of `Q_j` induced by an adapted frame: `π_j (f_{j+1} (last j))`. -/
def Data.qsec (j : Fin r) : Γ((F.lineQuotient j).toModules, U) :=
  (toQuot F j).app U (D.frS j (Fin.last j))

theorem Data.qsec_frame (j : Fin r) :
    (F.lineQuotient j).toModules.IsFrameOn U (fun _ : Fin 1 => D.qsec j) := by
  obtain ⟨q0, hq, heq⟩ := D.quot j
  have h : D.qsec j = q0 := heq
  rw [h]
  exact hq

end Full

/-- Key overlap relation between two adapted frames `D` on `U` and `D'` on `U'`: on `U ⊓ U'`,
`e'_j = ∑_{l ≤ j} d_l e_l` and `q'_j = d_{last} q_j` for the coordinates `d` of `f'_{j+1} (last j)`
in the frame `f_{j+1}`. -/
theorem Data.exists_overlap_coords {U U' : C.toScheme.Opens} (D : Data F r le_rfl U)
    (D' : Data F r le_rfl U') (j : Fin r) :
    ∃ d : Fin ((j : ℕ) + 1) → Γ(C.toScheme, U ⊓ U'),
      E.toModules.presheaf.map (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op (D'.top j) =
        ∑ l, d l • E.toModules.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op
          (D.top (Fin.castLE j.isLt l)) ∧
      (F.lineQuotient j).toModules.presheaf.map (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op
          (D'.qsec j) =
        d (Fin.last j) • (F.lineQuotient j).toModules.presheaf.map
          (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op (D.qsec j) := by
  have hfr := isFrameOn_restrict (D.frS_frame j) (inf_le_left : U ⊓ U' ≤ U)
  obtain ⟨d, hd⟩ := exists_coords hfr ((F.sub j.succ).toModules.presheaf.map
    (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op (D'.frS j (Fin.last j)))
  refine ⟨d, ?_, ?_⟩
  · have h1 := congrArg ((toTop F j.succ).app (U ⊓ U')) hd
    rw [map_sum, app_res, D'.toTop_frS] at h1
    simp only [Scheme.Modules.Hom.app_smul, app_res, D.toTop_frS] at h1
    exact h1.symm
  · have h2 := congrArg ((toQuot F j).app (U ⊓ U')) hd
    rw [map_sum, app_res, Fin.sum_univ_castSucc] at h2
    simp only [Scheme.Modules.Hom.app_smul, app_res, D.toQuot_frS_castSucc, map_zero, smul_zero,
      Finset.sum_const_zero, zero_add] at h2
    exact h2.symm

end MiyaokaMori.AdaptedFrame

open MiyaokaMori.AdaptedFrame in
/-- A vector bundle with a subbundle filtration by line quotients has an upper triangular
trivialization cocycle whose diagonal entries are trivialization cocycles of the line quotients. -/
theorem exists_upperTriangular_cocycle {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {r : ℕ} (E : AlgebraicGeometry.VectorBundle C.toVariety)
    (hr : E.rank = r) (F : SubbundleFiltration E r) :
    ∃ (ι : Type u) (U : ι → C.toScheme.Opens) (_ : ⨆ α, U α = ⊤)
      (g : ∀ α α' : ι, Matrix (Fin r) (Fin r) Γ(C.toScheme, U α ⊓ U α')),
      IsTrivializationCocycle E.toModules U g ∧ (∀ α α', (g α α').BlockTriangular id) ∧
      ∀ i : Fin r, IsTrivializationCocycle (F.lineQuotient i).toModules U
        (fun α α' => Matrix.of fun _ _ : Fin 1 => g α α' i i) := by
  classical
  have hex : ∀ x : C.toScheme, ∃ U : C.toScheme.Opens, x ∈ U ∧ Nonempty (Data F r le_rfl U) :=
    fun x => exists_data F x r le_rfl
  choose U hxU hD using hex
  have D : ∀ x, Data F r le_rfl (U x) := fun x => Classical.choice (hD x)
  -- the frames of `E` restricted to overlaps
  have hfr : ∀ α α' : C.toScheme, E.toModules.IsFrameOn (U α ⊓ U α')
      (fun i => E.toModules.presheaf.map (homOfLE (inf_le_left : U α ⊓ U α' ≤ U α)).op
        ((D α).top i)) :=
    fun α α' => isFrameOn_restrict (D α).top_frame inf_le_left
  refine ⟨C.toScheme, U, ?_, fun α α' => Matrix.of fun i j => coords (hfr α α')
    (E.toModules.presheaf.map (homOfLE (inf_le_right : U α ⊓ U α' ≤ U α')).op ((D α').top j)) i,
    ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hxU x⟩
  · refine ⟨fun α => (D α).top, fun α => (D α).top_frame, fun α α' j => ?_⟩
    simp only [Matrix.of_apply]
    exact (sum_coords_smul (hfr α α') _).symm
  · intro α α' i j hij
    have hij' : (j : ℕ) < i := hij
    obtain ⟨d, hd, -⟩ := Data.exists_overlap_coords (D α) (D α') j
    have hc : ∑ i, extendZero j d i • E.toModules.presheaf.map
        (homOfLE (inf_le_left : U α ⊓ U α' ≤ U α)).op ((D α).top i) =
        E.toModules.presheaf.map (homOfLE (inf_le_right : U α ⊓ U α' ≤ U α')).op ((D α').top j) := by
      rw [sum_extendZero_smul]
      exact hd.symm
    simp only [Matrix.of_apply]
    rw [coords_unique (hfr α α') hc i]
    exact extendZero_eq_zero j d i (by omega)
  · intro j
    refine ⟨fun α _ => (D α).qsec j, fun α => (D α).qsec_frame j, fun α α' _ => ?_⟩
    obtain ⟨d, hd, hq⟩ := Data.exists_overlap_coords (D α) (D α') j
    have hc : ∑ i, extendZero j d i • E.toModules.presheaf.map
        (homOfLE (inf_le_left : U α ⊓ U α' ≤ U α)).op ((D α).top i) =
        E.toModules.presheaf.map (homOfLE (inf_le_right : U α ⊓ U α' ≤ U α')).op ((D α').top j) := by
      rw [sum_extendZero_smul]
      exact hd.symm
    have h5 : extendZero j d j = d (Fin.last j) := extendZero_castLE j d (Fin.last j)
    simp only [Fin.sum_univ_one, Matrix.of_apply]
    rw [coords_unique (hfr α α') hc j, h5]
    exact hq

end
