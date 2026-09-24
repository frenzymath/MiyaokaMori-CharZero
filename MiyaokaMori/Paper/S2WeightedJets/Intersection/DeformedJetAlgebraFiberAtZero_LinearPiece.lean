import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraSyzygy

/-! # `I^{(1)}_j = S_j` for `j ≥ 1`, and the pieces of `gr_{S_+}(S)` in the extreme degrees

Generic facts about the powers `I^{(p)}_j = (S_+^p)_j` of the irrelevant ideal of a graded quasi-coherent algebra `S`
(`GradedQCAlgebra.irrelevantPow`) and the pieces `coker (stepHom S p j) = I^{(p)}_j / I^{(p+1)}_j` of the associated graded
algebra `gr_{S_+}(S)`, needed by `reesDeformation_restrictToLambda_zero_iso_weightedSym`
(`DeformedJetAlgebraFiberAtZero`) to identify the **linear pieces** `S_{q+1}/I^{(2)}_{q+1}` (which the hypothesis
`φ` there talks about) with the `p = 1` summands `I^{(1)}_{q+1}/I^{(2)}_{q+1}` of the fibre at `λ = 0` given by
`reesDeformation_restrictToLambda_zero_part_iso`.

* `mul_one'`: the right unit law `(S_m ◁ 1) ≫ mul = ρ` of a `GradedQCAlgebra` (from `one_mul` and `mul_comm`).
* `landsIn_id_one`, `epi_irrelevantPow_one_snd`, `isIso_irrelevantPow_one_snd`, `irrelevantPowOneIso`: for `j ≥ 1`,
  `I^{(1)}_j = S_j` — every `S_j` with `j ≥ 1` lies in the irrelevant ideal: `S_j = S_j · S_0 = S_j · 1 ⊆ (S_+ · S)_j`
  (the component `d = j`, `m = 0` of the generating map of `I^{(1)}_j`, `landsIn_whiskerLeft_irrelevantPow_mul_succ`).
* `linearPieceIso`: `coker (stepHom S 1 j) ≅ coker (S.irrelevantPow 2 j).2`, i.e. `I^{(1)}_j/I^{(2)}_j ≅ S_j/I^{(2)}_j`, for
  `j ≥ 1`, with `π_comp_linearPieceIso_hom`.
* `stepHom_self_eq_zero`, `topPieceIso`, `zerothPieceIso`: `I^{(j+1)}_j = 0` (`irrelevantPow_isZero_of_lt`), so
  `coker (stepHom S j j) ≅ I^{(j)}_j`; for `j = 0` this is `coker (stepHom S 0 0) ≅ S_0`.

Source: Stacks 052P (the extended Rees algebra, `R/λR = gr_I(A)`); Lemma 2.3 of the paper. The facts
themselves are elementary properties of the irrelevant ideal `S_+ = ⊕_{j ≥ 1} S_j` (`(S_+)_j = S_j` for `j ≥ 1`,
`(S_+^{p})_j = 0` for `p > j`); cf. Stacks 00JL (graded rings, irrelevant ideal).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- **Right unit law** of a graded QC algebra: `(S_m ◁ one) ≫ mul m 0 = ρ ≫ eqToHom`. Derived from the left unit law
`one_mul` and commutativity `mul_comm` via the braiding (`braiding_naturality_right`, `braiding_leftUnitor`). -/
theorem mul_one' (m : ℕ) :
    (S.part m ◁ S.one) ≫ S.mul m 0 =
      (ρ_ (S.part m)).hom ≫ eqToHom (congrArg S.part (Nat.add_zero m).symm) := by
  have h3 : S.mul m 0 = (β_ (S.part m) (S.part 0)).hom ≫ S.mul 0 m ≫
      eqToHom (congrArg S.part (Nat.add_comm 0 m)) := by
    rw [← Category.assoc, S.mul_comm m 0, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rw [h3, ← Category.assoc, BraidedCategory.braiding_naturality_right, Category.assoc,
    ← Category.assoc (S.one ▷ S.part m), S.one_mul m]
  simp only [Category.assoc]
  rw [← Category.assoc, braiding_leftUnitor, eqToHom_trans]

/-- `S_j ⊆ I^{(1)}_j` for `j ≥ 1`: the identity of `S_j` lands in `I^{(1)}_j`, because `S_j = S_j · S_0` and
`S_d · I^{(0)}_m ⊆ I^{(1)}_{d+m}` for `d ≥ 1` (`landsIn_whiskerLeft_irrelevantPow_mul_succ` with `d = j`, `m = 0`). -/
theorem landsIn_id_one (j : ℕ) (hj : 0 < j) : S.LandsIn (𝟙 (S.part j)) 1 := by
  have h := S.landsIn_whiskerLeft_irrelevantPow_mul_succ 0 j 0 j hj (Nat.add_zero j)
  have h' := S.landsIn_comp ((ρ_ (S.part j)).inv ≫ (S.part j ◁ S.one)) h
  have e : 𝟙 (S.part j) = ((ρ_ (S.part j)).inv ≫ (S.part j ◁ S.one)) ≫
      ((S.part j ◁ (S.irrelevantPow 0 0).2) ≫ S.mul j 0 ≫ eqToHom (congrArg S.part (Nat.add_zero j))) := by
    show 𝟙 (S.part j) = ((ρ_ (S.part j)).inv ≫ (S.part j ◁ S.one)) ≫
      ((S.part j ◁ 𝟙 (S.part 0)) ≫ S.mul j 0 ≫ eqToHom (congrArg S.part (Nat.add_zero j)))
    rw [MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.assoc, ← Category.assoc (S.part j ◁ S.one),
      S.mul_one' j, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, Iso.inv_hom_id]
  rw [e]
  exact h'

/-- `I^{(1)}_j → S_j` is an epimorphism for `j ≥ 1` (`I^{(1)}_j = S_j`). -/
theorem epi_irrelevantPow_one_snd (j : ℕ) (hj : 0 < j) : Epi (S.irrelevantPow 1 j).2 := by
  apply CategoryTheory.Abelian.epi_of_cokernel_π_eq_zero
  have h := S.landsIn_id_one j hj
  unfold LandsIn at h
  rwa [Category.id_comp] at h

/-- `I^{(1)}_j → S_j` is an isomorphism for `j ≥ 1` (mono + epi in an abelian category). -/
theorem isIso_irrelevantPow_one_snd (j : ℕ) (hj : 0 < j) : IsIso (S.irrelevantPow 1 j).2 :=
  haveI := S.mono_irrelevantPow 1 j
  haveI := S.epi_irrelevantPow_one_snd j hj
  isIso_of_mono_of_epi _

/-- `I^{(1)}_j ≅ S_j` for `j ≥ 1` (the inclusion itself). -/
noncomputable def irrelevantPowOneIso (j : ℕ) (hj : 0 < j) : (S.irrelevantPow 1 j).1 ≅ S.part j :=
  haveI := S.isIso_irrelevantPow_one_snd j hj
  asIso (S.irrelevantPow 1 j).2

theorem irrelevantPowOneIso_hom (j : ℕ) (hj : 0 < j) :
    (S.irrelevantPowOneIso j hj).hom = (S.irrelevantPow 1 j).2 := rfl

/-- **The linear piece of `gr_{S_+}(S)` in weight `j ≥ 1`**: `I^{(1)}_j/I^{(2)}_j ≅ S_j/I^{(2)}_j`, i.e.
`coker (stepHom S 1 j) ≅ coker (S.irrelevantPow 2 j).2` (`cokernel.mapIso` along `I^{(1)}_j ≅ S_j`;
`stepHom ≫ (irrelevantPow 1 j).2 = (irrelevantPow 2 j).2` is `stepHom_comp`). -/
noncomputable def linearPieceIso (j : ℕ) (hj : 0 < j) :
    cokernel (irrelevantPow.stepHom S 1 j) ≅ cokernel (S.irrelevantPow 2 j).2 :=
  cokernel.mapIso _ _ (Iso.refl _) (S.irrelevantPowOneIso j hj)
    (by rw [Iso.refl_hom, Category.id_comp, irrelevantPowOneIso_hom]; exact irrelevantPow.stepHom_comp S 1 j)

@[reassoc]
theorem π_comp_linearPieceIso_hom (j : ℕ) (hj : 0 < j) :
    cokernel.π (irrelevantPow.stepHom S 1 j) ≫ (S.linearPieceIso j hj).hom =
      (S.irrelevantPow 1 j).2 ≫ cokernel.π (S.irrelevantPow 2 j).2 := by
  unfold linearPieceIso
  rw [cokernel.mapIso_hom, cokernel.π_desc, irrelevantPowOneIso_hom]

/-- `stepHom S j j : I^{(j+1)}_j → I^{(j)}_j` vanishes (its source is `0`, `irrelevantPow_isZero_of_lt`). -/
theorem stepHom_self_eq_zero (j : ℕ) : irrelevantPow.stepHom S j j = 0 :=
  (S.irrelevantPow_isZero_of_lt (j + 1) j (Nat.lt_succ_self j)).eq_of_src _ _

/-- **The top piece** `coker (stepHom S j j) = I^{(j)}_j / I^{(j+1)}_j ≅ I^{(j)}_j` (`I^{(j+1)}_j = 0`). -/
noncomputable def topPieceIso (j : ℕ) : cokernel (irrelevantPow.stepHom S j j) ≅ (S.irrelevantPow j j).1 :=
  cokernelIsoOfEq (S.stepHom_self_eq_zero j) ≪≫ cokernelZeroIsoTarget

@[reassoc]
theorem π_comp_topPieceIso_hom (j : ℕ) :
    cokernel.π (irrelevantPow.stepHom S j j) ≫ (S.topPieceIso j).hom = 𝟙 _ := by
  unfold topPieceIso
  rw [Iso.trans_hom, π_comp_cokernelIsoOfEq_hom_assoc, cokernelZeroIsoTarget_hom, cokernel.π_desc]

/-- **The zeroth piece** `coker (stepHom S 0 0) = S_0 / I^{(1)}_0 ≅ S_0` (`I^{(1)}_0 = 0`, `I^{(0)}_0 = S_0`). -/
noncomputable def zerothPieceIso : cokernel (irrelevantPow.stepHom S 0 0) ≅ S.part 0 :=
  S.topPieceIso 0

@[reassoc]
theorem π_comp_zerothPieceIso_hom :
    cokernel.π (irrelevantPow.stepHom S 0 0) ≫ S.zerothPieceIso.hom = 𝟙 (S.part 0) :=
  S.π_comp_topPieceIso_hom 0

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
