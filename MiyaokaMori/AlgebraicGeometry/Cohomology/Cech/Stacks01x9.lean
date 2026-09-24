import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternating
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternatingElementwise
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechAlternatingLocalizationAcyclic
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcSectionsBasicOpenLocalization

/-! # Čech cohomology of a quasi-coherent sheaf on a standard open cover (Stacks 01X9)

The Čech cohomology of a quasi-coherent sheaf on a standard open cover of an affine open vanishes in
positive degrees.

Source: Stacks 01X9.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace Stacks01x9Aux

open AlgebraicGeometry

variable {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}

/-- The opens contained in `U`. -/
abbrev P (U : X.Opens) : Type u := {W : X.Opens // W ≤ U}

/-- `Γ(M, W)` as a `Γ(X, U)`-module (`W ≤ U`). -/
def NN (W : P U) : Type u := Γ(M, W.1)

instance (W : P U) : AddCommGroup (NN M W) := inferInstanceAs (AddCommGroup Γ(M, W.1))

instance (W : P U) : Module Γ(X, U) (NN M W) :=
  Module.compHom Γ(M, W.1) (X.presheaf.map (homOfLE W.2).op).hom

theorem smul_def (W : P U) (a : Γ(X, U)) (x : NN M W) :
    a • x = (show Γ(M, W.1) from (X.presheaf.map (homOfLE W.2).op a) • (show Γ(M, W.1) from x)) :=
  rfl

/-- The restriction map, `Γ(X, U)`-linear. -/
def res {W W' : P U} (h : W' ≤ W) : NN M W →ₗ[Γ(X, U)] NN M W' where
  toFun := M.presheaf.map (homOfLE (show W'.1 ≤ W.1 from h)).op
  map_add' := map_add _
  map_smul' a x := by
    show M.presheaf.map (homOfLE (show W'.1 ≤ W.1 from h)).op
        ((X.presheaf.map (homOfLE W.2).op a) • (show Γ(M, W.1) from x)) =
      (X.presheaf.map (homOfLE W'.2).op a) •
        M.presheaf.map (homOfLE (show W'.1 ≤ W.1 from h)).op (show Γ(M, W.1) from x)
    rw [Scheme.Modules.map_smul]
    congr 1
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

theorem map_map {W₁ W₂ W₃ : X.Opens} (h : W₂ ≤ W₁) (h' : W₃ ≤ W₂) (x : Γ(M, W₁)) :
    M.presheaf.map (homOfLE h').op (M.presheaf.map (homOfLE h).op x) =
      M.presheaf.map (homOfLE (h'.trans h)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem res_comp {W₁ W₂ W₃ : P U} (h : W₂ ≤ W₁) (h' : W₃ ≤ W₂) (x : NN M W₁) :
    res M h' (res M h x) = res M (h'.trans h) x :=
  map_map M _ _ x

theorem basicOpen_finset_prod {ι : Type} (s : Finset ι) (g : ι → Γ(X, U)) :
    X.basicOpen (∏ k ∈ s, g k) = U ⊓ s.inf fun k => X.basicOpen (g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Scheme.basicOpen_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul, ih, Finset.inf_insert]
    apply le_antisymm
    · exact le_inf (inf_le_right.trans inf_le_left)
        (le_inf inf_le_left (inf_le_right.trans inf_le_right))
    · exact le_inf (inf_le_right.trans inf_le_left)
        (le_inf inf_le_left (inf_le_right.trans inf_le_right))

theorem iInf_basicOpen_eq {q : ℕ} (g : Fin (q + 1) → Γ(X, U)) :
    ⨅ k, X.basicOpen (g k) = X.basicOpen (∏ k, g k) := by
  rw [basicOpen_finset_prod, Finset.inf_univ_eq_iInf]
  exact (inf_eq_right.2 ((iInf_le (fun k => X.basicOpen (g k)) 0).trans (X.basicOpen_le _))).symm

theorem iInf_ins {n q : ℕ} (F : Fin n → X.Opens) (σ : Fin (q + 1) ↪o Fin n) (j : Fin n)
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

theorem loc_of_eq [M.IsQuasicoherent] {W : X.Opens} (hW : IsAffineOpen W) (h : Γ(X, W))
    {W' : X.Opens} (e : W' = X.basicOpen h) (hle : W' ≤ W) :
    (∀ y : Γ(M, W'), ∃ (m : ℕ) (t : Γ(M, W)), M.presheaf.map (homOfLE hle).op t =
      (X.presheaf.map (homOfLE hle).op h) ^ m • y) ∧
    (∀ t : Γ(M, W), M.presheaf.map (homOfLE hle).op t = 0 → ∃ m : ℕ, h ^ m • t = 0) := by
  subst e
  exact ⟨fun y => M.exists_pow_smul_eq_map_basicOpen hW h y,
    fun t ht => M.exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero hW h t ht⟩

end Stacks01x9Aux

theorem cechComplexAlt_standardCover_acyclic {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) {n : ℕ}
    (f : Fin n → Γ(X, U)) (hf : ⨆ i, X.basicOpen (f i) = U) (p : ℕ) (hp : 0 < p) :
    Subsingleton (((AlgebraicGeometry.Scheme.Modules.cechComplexAlt (fun i => X.basicOpen (f i)) M).homology
      (p : ℤ)) : Type u) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  apply AlgebraicGeometry.Scheme.Modules.cechComplexAlt_homology_subsingleton_of_family
  intro s hs
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff, iSup_range' (fun g => X.basicOpen g) f, hf]
  have hVle : ∀ (q : ℕ) (σ : Fin (q + 1) ↪o Fin n), (⨅ k, X.basicOpen (f (σ k))) ≤ U :=
    fun q σ => (iInf_le _ 0).trans (X.basicOpen_le _)
  have hface : ∀ (q : ℕ) (τ : Fin (q + 2) ↪o Fin n) (k : Fin (q + 2)),
      (⟨⨅ i, X.basicOpen (f (τ i)), hVle (q + 1) τ⟩ : Stacks01x9Aux.P U) ≤
        ⟨⨅ i, X.basicOpen (f (CechAltAlg.face τ k i)), hVle q _⟩ :=
    fun q τ k => AlgebraicGeometry.Scheme.Modules.cech_face_le (fun i => X.basicOpen (f i)) τ k
  have key := CechAltAlg.exists_d_eq f
    (V := fun q σ => (⟨⨅ k, X.basicOpen (f (σ k)), hVle q σ⟩ : Stacks01x9Aux.P U))
    (Stacks01x9Aux.NN M) (fun h => Stacks01x9Aux.res M h) hface
    (fun h h' x => Stacks01x9Aux.res_comp M h h' x) ?_ hspan q s ?_
  · obtain ⟨t, ht⟩ := key
    refine ⟨t, ?_⟩
    funext τ
    exact (CechAltAlg.d_apply _ _ _ _ _ t τ).symm.trans (congrFun ht τ)
  · intro q σ j hj h
    have hW : AlgebraicGeometry.IsAffineOpen (⨅ k, X.basicOpen (f (σ k))) := by
      rw [Stacks01x9Aux.iInf_basicOpen_eq]
      exact hU.basicOpen _
    have e : (⨅ k, X.basicOpen (f (CechAltAlg.ins σ j hj k))) =
        X.basicOpen (X.presheaf.map (homOfLE (hVle q σ)).op (f j)) := by
      rw [AlgebraicGeometry.Scheme.basicOpen_res]
      exact Stacks01x9Aux.iInf_ins (fun i => X.basicOpen (f i)) σ j hj
    obtain ⟨h1, h2⟩ := Stacks01x9Aux.loc_of_eq M hW _ e h
    constructor
    · intro y
      obtain ⟨m, t, ht⟩ := h1 y
      refine ⟨m, t, ?_⟩
      rw [Stacks01x9Aux.smul_def]
      refine ht.trans ?_
      rw [map_pow]
      congr 2
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    · intro x hx
      obtain ⟨m, hm⟩ := h2 x hx
      refine ⟨m, ?_⟩
      rw [Stacks01x9Aux.smul_def, map_pow]
      exact hm
  · funext τ
    refine Eq.trans (CechAltAlg.d_apply _ _ _ _ _ _ τ) ?_
    exact congrFun hs τ

end
