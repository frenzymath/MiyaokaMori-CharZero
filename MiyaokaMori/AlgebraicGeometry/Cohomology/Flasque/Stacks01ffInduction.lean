import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks01ffZero
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks01ffInjectiveColimitAcyclic
import MiyaokaMori.CategoryTheory.Stacks01ffInjectiveDiagram

/-! # The induction step of Stacks 01FF

The induction on `q` in the proof of Stacks 01FF (cohomology-lemma-quasi-separated-cohomology-colimit):
`colim_j H^q(X, F_j) → H^q(X, colim F)` is bijective (elementwise form `Stmt F q`) for every filtered diagram
`F` of abelian sheaves on a compact quasi-separated space with a basis of quasi-compact opens.

* `q = 0`: `Stacks01ff.stmt_zero`.
* `stmt_succ`: the step `q → q + 1`. Embed `F ⟶ I` into a diagram of injectives
  (`Functor.exists_mono_injective_diagram`), form `0 → F → I → Q := coker → 0` in `J ⥤ Sh(X)`; it stays
  short exact at every `j` and after `colim` (`Stacks01ffSes.lean`).
  `H^{q+1}(I_j) = 0` (`I_j` injective) and `H^{q+1}(colim I) = 0`
  (`H_colimit_subsingleton_of_injective`), so the connecting maps
  `H^q(Q_j) → H^{q+1}(F_j)` and `H^q(colim Q) → H^{q+1}(colim F)` are surjective; the inductive hypothesis for
  `Q` and `I` and the naturality of the connecting map give the claim by a diagram chase (written out in
  `stmt_succ`).
* `stmt_all`: induction on `q`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace Stacks01ff

variable {X : TopCat.{u}} {J : Type u} [SmallCategory J]

/-- The inductive step `q → q + 1` (Stacks 01FF, proof, "induction on q"): a diagram chase along the long
exact `Ext`-sequences of `0 → F → I → Q → 0` at each stage `j` and at the colimit. -/
theorem stmt_succ [CompactSpace X] [QuasiSeparatedSpace X] [IsFiltered J]
    (hB : Opens.IsBasis {U : Opens X | IsCompact (U : Set X)}) (q : ℕ)
    (ih : ∀ G : J ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}, Stmt G q)
    (F : J ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) : Stmt F (q + 1) := by
  obtain ⟨I, ι, hmono, hinj⟩ := CategoryTheory.Functor.exists_mono_injective_diagram F
  have : ∀ j, Mono (ι.app j) := hmono
  have : Mono ι := NatTrans.mono_of_mono_app ι
  have hC : Subsingleton (Sheaf.H (colimit I) (q + 1)) :=
    TopCat.Sheaf.H_colimit_subsingleton_of_injective hB I hinj q
  have hIj : ∀ j, Subsingleton (Sheaf.H (I.obj j) (q + 1)) := fun j =>
    haveI := hinj j
    Abelian.Ext.subsingleton_of_injective _ (I.obj j) q
  have hSc := sesColim_shortExact ι
  have hSj := sesAt_shortExact ι
  constructor
  · -- surjectivity: lift `x` to `H^q(colim Q)`, then to some `H^q(Q_j)`, and apply the connecting map
    intro x
    have hx : x.comp (Abelian.Ext.mk₀ (colimMap ι)) (add_zero (q + 1)) = 0 :=
      @Subsingleton.elim _ hC _ _
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hSc x hx rfl
    obtain ⟨j, yj, hyj⟩ := (ih (cokernel ι)).1 y
    refine ⟨j, yj.comp (hSj j).extClass rfl, ?_⟩
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero, extClass_toColim ι j,
      ← Abelian.Ext.comp_assoc_of_second_deg_zero, hyj, hy]
  · -- kernel: `e = δ_j y`; `ι_j y` lifts to `H^q(colim I)`, hence to some `H^q(I_k)`; compare at a common
    -- stage `l`, kill the difference at a stage `m`, and use `δ ∘ (I → Q) = 0`
    intro j e he
    have he' : e.comp (Abelian.Ext.mk₀ (ι.app j)) (add_zero (q + 1)) = 0 :=
      @Subsingleton.elim _ (hIj j) _ _
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ _ (hSj j) e he' rfl
    have h1 : (y.comp (Abelian.Ext.mk₀ (colimit.ι (cokernel ι) j)) (add_zero q)).comp
        hSc.extClass rfl = 0 := by
      rw [Abelian.Ext.comp_assoc_of_second_deg_zero, ← extClass_toColim ι j,
        ← Abelian.Ext.comp_assoc_of_third_deg_zero, hy, he]
    obtain ⟨z, hz⟩ := Abelian.Ext.covariant_sequence_exact₃ _ hSc _ rfl h1
    obtain ⟨k, zk, hzk⟩ := (ih I).1 z
    set l := IsFiltered.max j k with hl
    set a : j ⟶ l := IsFiltered.leftToMax j k with ha
    set b : k ⟶ l := IsFiltered.rightToMax j k with hb
    set A : Sheaf.H ((cokernel ι).obj l) q :=
      y.comp (Abelian.Ext.mk₀ ((cokernel ι).map a)) (add_zero q) with hA_def
    set B : Sheaf.H ((cokernel ι).obj l) q :=
      (zk.comp (Abelian.Ext.mk₀ (I.map b)) (add_zero q)).comp
        (Abelian.Ext.mk₀ ((cokernel.π ι).app l)) (add_zero q) with hB_def
    have hA : A.comp (Abelian.Ext.mk₀ (colimit.ι (cokernel ι) l)) (add_zero q) =
        y.comp (Abelian.Ext.mk₀ (colimit.ι (cokernel ι) j)) (add_zero q) := by
      rw [hA_def, Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, colimit.w]
    have hB : B.comp (Abelian.Ext.mk₀ (colimit.ι (cokernel ι) l)) (add_zero q) =
        y.comp (Abelian.Ext.mk₀ (colimit.ι (cokernel ι) j)) (add_zero q) := by
      rw [hB_def, Abelian.Ext.comp_assoc_of_third_deg_zero (zk.comp _ _), Abelian.Ext.mk₀_comp_mk₀,
        ← ι_colimMap, ← Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.comp_assoc_of_second_deg_zero,
        Abelian.Ext.comp_assoc_of_third_deg_zero zk, Abelian.Ext.mk₀_comp_mk₀, colimit.w, hzk, hz]
    have hw : (A - B).comp (Abelian.Ext.mk₀ (colimit.ι (cokernel ι) l)) (add_zero q) = 0 := by
      rw [sub_eq_add_neg, Abelian.Ext.add_comp, Abelian.Ext.neg_comp, hA, hB, add_neg_cancel]
    obtain ⟨m, c, hc⟩ := (ih (cokernel ι)).2 l (A - B) hw
    refine ⟨m, a ≫ c, ?_⟩
    have hAc : A.comp (Abelian.Ext.mk₀ ((cokernel ι).map c)) (add_zero q) =
        B.comp (Abelian.Ext.mk₀ ((cokernel ι).map c)) (add_zero q) := by
      rw [← sub_eq_zero, sub_eq_add_neg, ← Abelian.Ext.neg_comp, ← Abelian.Ext.add_comp,
        ← sub_eq_add_neg]
      exact hc
    rw [← hy, Abelian.Ext.comp_assoc_of_third_deg_zero, extClass_trans ι (a ≫ c),
      ← Abelian.Ext.comp_assoc_of_second_deg_zero, Functor.map_comp, ← Abelian.Ext.mk₀_comp_mk₀,
      ← Abelian.Ext.comp_assoc_of_second_deg_zero, ← hA_def, hAc, hB_def,
      Abelian.Ext.comp_assoc_of_third_deg_zero (zk.comp _ _), Abelian.Ext.mk₀_comp_mk₀,
      ← (cokernel.π ι).naturality, ← Abelian.Ext.mk₀_comp_mk₀,
      ← Abelian.Ext.comp_assoc_of_second_deg_zero,
      Abelian.Ext.comp_assoc_of_second_deg_zero _ _ (hSj m).extClass,
      ShortComplex.ShortExact.comp_extClass (hSj m), Abelian.Ext.comp_zero]

/-- Stacks 01FF in the form `Stmt F q`, for all `q` and all filtered diagrams `F`. -/
theorem stmt_all [CompactSpace X] [QuasiSeparatedSpace X] [IsFiltered J]
    (hB : Opens.IsBasis {U : Opens X | IsCompact (U : Set X)}) (q : ℕ) :
    ∀ F : J ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}, Stmt F q := by
  induction q with
  | zero => exact stmt_zero hB
  | succ q ih => exact stmt_succ hB q ih

end Stacks01ff

end
