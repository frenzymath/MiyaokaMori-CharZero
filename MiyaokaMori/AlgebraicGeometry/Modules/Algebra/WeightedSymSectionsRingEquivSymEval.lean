import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymSectionsRingEquivSymPure
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymSectionsRingEquivSymEvalSpan
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymSectionsRingEquivSymEvalLinear

/-! # Evaluation of pure sections and the section ring of the weighted symmetric algebra

Second half of the sheaf-side toolkit for `symLiftHom_bijective` (`WeightedSymSectionsRingEquivSym.lean`); the
first half (pure sections `weightedTensorPure`, their multiplication and the generator inclusion on sections) is
`WeightedSymSectionsRingEquivSymPure.lean`. Notation as there: `S := weightedSymAlgebra V`, `F q := V_q^∨`,
`T_d := weightedSymTensor r F d`, `R := Γ(X, U)`.

* `weightedTensorPure_eq_prod`: any unital, multiplicative evaluation `Φ` of the graded layer `(T_d)_d` into a
  commutative monoid sends a pure section to the product of its one-factor pure sections (induction on `r`).
* `weightedSymAlgebra.pieceOf`, `ofPiece_ι_weightedTensorPure`: the evaluation into the section ring `⨁_m Γ(U, S_m)`;
  in it `ι_d (pure d w) = ∏_q ∏_i genIncl_q (w q i)`.
* Two statements that use the affine hypothesis (Stacks 01I8 / 01CG through
  `tensorSectionsHom_app_bijective_of_isAffineOpen` and the coequalizer description of `Sym^e` on
  affine opens): `span_range_weightedTensorPure_eq_top` and
  `exists_linearMap_weightedTensorPure`. Both are assembled by induction on `r` from the helper
  modules `WeightedSymSectionsRingEquivSymEvalSpan.lean` (pure tensors span `Γ(U, F^{⊗e})` and `Γ(U, Sym^e F)`) and
  `WeightedSymSectionsRingEquivSymEvalLinear.lean` (linear maps prescribed on pure tensors); their remaining
  dependencies are `tensorSectionsHom_app_bijective_of_isAffineOpen` and `symPowπ_app_eq_zero_iff_of_isAffineOpen`.
* Consequences for the section ring: `weightedSymAlgebra.closure_sectionsUnitHom_genIncl_eq_top` and
  `weightedSymAlgebra.exists_addMonoidHom_sectionsRing`.

Sources: Stacks 01CG, 01I8; Bourbaki Algebra III §6; §2 of the paper (the weighted symmetric algebra).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}} (U : X.Opens)

/-! ## Evaluation of pure sections in a commutative monoid -/

/-- **Evaluation of pure sections.** Let `Φ_d : Γ(U, T_d) → C` (`C` a commutative monoid) be unital and multiplicative
on pure sections (`Φ_{a+b} (mulTerm a b (pure a ⊗ pure b)) = Φ_a (pure a) * Φ_b (pure b)`). Then the value of `Φ` on a
pure section is the product of its values on the one-factor pure sections: for any family `e j` of one-factor
multidegrees (`e j q = δ_{jq}`) with one-factor families `fam j x` (`fam j x j i = x`),
`Φ_d (pure d w) = ∏_q ∏_i Φ_{e q} (pure (e q) (fam q (w q i)))`.

Proof by induction on `r` along `weightedSymTensor`: the first block `Sym^{d 0}(F 0)` is peeled off with
`weightedSymTensorMul_app_weightedTensorPure` (multidegrees `Fin.cons (d 0) 0` and `Fin.cons 0 (Fin.tail d)`), the
first block is expanded by induction on `d 0` (one factor at a time, again with `mulTerm`), and the tail is handled by
the induction hypothesis applied to `Φ' d' y := Φ (Fin.cons 0 d') (1 ⊗ y)`, which is again unital and multiplicative on
pure sections. All multidegree bookkeeping is done with `weightedTensorCast_weightedTensorPure`. -/
theorem weightedTensorPure_eq_prod {C : Type*} [CommMonoid C] (r : ℕ) :
    ∀ (F : Fin r → X.Modules)
      (Φ : ∀ d : Fin r → ℕ, Γ(AlgebraicGeometry.Scheme.weightedSymTensor r F d, U) → C),
      Φ 0 ((AlgebraicGeometry.Scheme.weightedSymTensorOne r F).app U (AlgebraicGeometry.Scheme.Modules.unitSec U)) = 1 →
      (∀ (a b : Fin r → ℕ) (wa : ∀ q, Fin (a q) → Γ(F q, U)) (wb : ∀ q, Fin (b q) → Γ(F q, U)),
        Φ (a + b) ((AlgebraicGeometry.Scheme.weightedSymTensorMul r F a b).app U
          (AlgebraicGeometry.Scheme.Modules.tsec _ _ U (weightedTensorPure U r F a wa)
            (weightedTensorPure U r F b wb))) =
          Φ a (weightedTensorPure U r F a wa) * Φ b (weightedTensorPure U r F b wb)) →
      ∀ (e : Fin r → Fin r → ℕ), (∀ j q, e j q = if q = j then 1 else 0) →
      ∀ (fam : ∀ j, Γ(F j, U) → ∀ q, Fin (e j q) → Γ(F q, U)), (∀ j x i, fam j x j i = x) →
      ∀ (d : Fin r → ℕ) (w : ∀ q, Fin (d q) → Γ(F q, U)),
        Φ d (weightedTensorPure U r F d w) =
          ∏ q, ∏ i, Φ (e q) (weightedTensorPure U r F (e q) (fam q (w q i))) := by
  induction r with
  | zero =>
    intro F Φ hone _ e _ fam _ d w
    have hd : d = 0 := Subsingleton.elim _ _
    subst hd
    rw [← weightedSymTensorOne_app_one U 0 F w, hone, Fin.prod_univ_zero]
  | succ r ih =>
    intro F Φ hone hmul e he fam hfam d w
    -- transport along equalities of multidegrees
    have hΦcast : ∀ {d d' : Fin (r + 1) → ℕ} (h : d = d')
        (x : Γ(AlgebraicGeometry.Scheme.weightedSymTensor (r + 1) F d, U)),
        Φ d' (weightedTensorCast U (r + 1) F h x) = Φ d x := by
      intro d d' h x
      subst h
      rw [weightedTensorCast_rfl]
    let Z : Fin (r + 1) → ℕ := Fin.cons (0 : ℕ) (0 : Fin r → ℕ)
    have h00 : Z = 0 := by
      funext q
      exact Fin.cases rfl (fun _ => rfl) q
    -- the layer-`r` evaluation `Φ' d' y := Φ (cons 0 d') (1 ⊗ y)`
    let one₀ : Γ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (F 0)).part 0, U) :=
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (F 0)).one.app U (AlgebraicGeometry.Scheme.Modules.unitSec U)
    let Φ' : ∀ d' : Fin r → ℕ, Γ(AlgebraicGeometry.Scheme.weightedSymTensor r (Fin.tail F) d', U) → C :=
      fun d' y => Φ (Fin.cons (0 : ℕ) d') (weightedTensorUp₀ U r F d' (AlgebraicGeometry.Scheme.Modules.tsec _ _ U one₀ y))
    have hΦ' : ∀ (d' : Fin r → ℕ) (W : ∀ q, Fin (d' q) → Γ(Fin.tail F q, U)),
        Φ' d' (weightedTensorPure U r (Fin.tail F) d' W) =
          Φ (Fin.cons (0 : ℕ) d') (weightedTensorPure U (r + 1) F (Fin.cons (0 : ℕ) d')
            (Fin.cons (α := fun q => Fin ((Fin.cons (0 : ℕ) d' : Fin (r + 1) → ℕ) q) → Γ(F q, U)) Fin.elim0 W)) :=
      fun d' W => rfl
    have hzero : ∀ W : ∀ q, Fin (Z q) → Γ(F q, U), Φ Z (weightedTensorPure U (r + 1) F Z W) = 1 := by
      intro W
      calc Φ Z (weightedTensorPure U (r + 1) F Z W)
          = Φ 0 (weightedTensorCast U (r + 1) F h00 (weightedTensorPure U (r + 1) F Z W)) := (hΦcast h00 _).symm
        _ = Φ 0 (weightedTensorPure U (r + 1) F 0 (fun _ => Fin.elim0)) :=
            congrArg (Φ 0) (weightedTensorCast_weightedTensorPure U (r + 1) F h00 _ _
              (fun q i => (show Fin 0 from Fin.cast (congrFun h00 q) i).elim0))
        _ = Φ 0 ((AlgebraicGeometry.Scheme.weightedSymTensorOne (r + 1) F).app U
              (AlgebraicGeometry.Scheme.Modules.unitSec U)) :=
            congrArg (Φ 0) (weightedSymTensorOne_app_one U (r + 1) F (fun _ => Fin.elim0)).symm
        _ = 1 := hone
    have hone' : Φ' 0 ((AlgebraicGeometry.Scheme.weightedSymTensorOne r (Fin.tail F)).app U
        (AlgebraicGeometry.Scheme.Modules.unitSec U)) = 1 :=
      (congrArg (Φ' 0) (weightedSymTensorOne_app_one U r (Fin.tail F) (fun _ => Fin.elim0))).trans
        ((hΦ' 0 _).trans (hzero _))
    have hmul' : ∀ (a b : Fin r → ℕ) (wa : ∀ q, Fin (a q) → Γ(Fin.tail F q, U))
        (wb : ∀ q, Fin (b q) → Γ(Fin.tail F q, U)),
        Φ' (a + b) ((AlgebraicGeometry.Scheme.weightedSymTensorMul r (Fin.tail F) a b).app U
          (AlgebraicGeometry.Scheme.Modules.tsec _ _ U (weightedTensorPure U r (Fin.tail F) a wa)
            (weightedTensorPure U r (Fin.tail F) b wb))) =
          Φ' a (weightedTensorPure U r (Fin.tail F) a wa) * Φ' b (weightedTensorPure U r (Fin.tail F) b wb) := by
      intro a b wa wb
      let A : Fin (r + 1) → ℕ := Fin.cons (0 : ℕ) a
      let B : Fin (r + 1) → ℕ := Fin.cons (0 : ℕ) b
      let WA : ∀ q, Fin (A q) → Γ(F q, U) := Fin.cons Fin.elim0 wa
      let WB : ∀ q, Fin (B q) → Γ(F q, U) := Fin.cons Fin.elim0 wb
      have hab : A + B = Fin.cons (0 : ℕ) (a + b) := by
        funext q
        exact Fin.cases rfl (fun _ => rfl) q
      calc Φ' (a + b) ((AlgebraicGeometry.Scheme.weightedSymTensorMul r (Fin.tail F) a b).app U
            (AlgebraicGeometry.Scheme.Modules.tsec _ _ U (weightedTensorPure U r (Fin.tail F) a wa)
              (weightedTensorPure U r (Fin.tail F) b wb)))
          = Φ' (a + b) (weightedTensorPure U r (Fin.tail F) (a + b) (fun q => Fin.append (wa q) (wb q))) :=
            congrArg (Φ' (a + b)) (weightedSymTensorMul_app_weightedTensorPure U r (Fin.tail F) a b wa wb)
        _ = Φ (Fin.cons (0 : ℕ) (a + b)) (weightedTensorPure U (r + 1) F (Fin.cons (0 : ℕ) (a + b))
              (Fin.cons (α := fun q => Fin ((Fin.cons (0 : ℕ) (a + b) : Fin (r + 1) → ℕ) q) → Γ(F q, U))
                Fin.elim0 (fun q => Fin.append (wa q) (wb q)))) := hΦ' (a + b) _
        _ = Φ (A + B) (weightedTensorCast U (r + 1) F hab.symm (weightedTensorPure U (r + 1) F
              (Fin.cons (0 : ℕ) (a + b))
              (Fin.cons (α := fun q => Fin ((Fin.cons (0 : ℕ) (a + b) : Fin (r + 1) → ℕ) q) → Γ(F q, U))
                Fin.elim0 (fun q => Fin.append (wa q) (wb q))))) := (hΦcast hab.symm _).symm
        _ = Φ (A + B) (weightedTensorPure U (r + 1) F (A + B) (fun q => Fin.append (WA q) (WB q))) := by
            refine congrArg (Φ (A + B)) (weightedTensorCast_weightedTensorPure U (r + 1) F hab.symm _ _ fun q => ?_)
            refine Fin.cases ?_ (fun q₁ => ?_) q
            · intro i
              exact (show Fin 0 from i).elim0
            · intro i
              show Fin.append (wa q₁) (wb q₁) i = Fin.append (wa q₁) (wb q₁) (Fin.cast _ i)
              exact congrArg _ (Fin.ext rfl)
        _ = Φ (A + B) ((AlgebraicGeometry.Scheme.weightedSymTensorMul (r + 1) F A B).app U
              (AlgebraicGeometry.Scheme.Modules.tsec _ _ U (weightedTensorPure U (r + 1) F A WA)
                (weightedTensorPure U (r + 1) F B WB))) :=
            congrArg (Φ (A + B)) (weightedSymTensorMul_app_weightedTensorPure U (r + 1) F A B WA WB).symm
        _ = Φ A (weightedTensorPure U (r + 1) F A WA) * Φ B (weightedTensorPure U (r + 1) F B WB) := hmul A B WA WB
        _ = Φ' a (weightedTensorPure U r (Fin.tail F) a wa) * Φ' b (weightedTensorPure U r (Fin.tail F) b wb) :=
            congrArg₂ (· * ·) (hΦ' a wa).symm (hΦ' b wb).symm
    -- one-factor data for the tail
    have he' : ∀ (j q : Fin r), e j.succ q.succ = if q = j then 1 else 0 := fun j q => by
      rw [he j.succ q.succ]
      simp [Fin.succ_inj]
    have hfam' : ∀ (j : Fin r) (x : Γ(Fin.tail F j, U)) (i : Fin (e j.succ j.succ)),
        fam j.succ x j.succ i = x := fun j x i => hfam j.succ x i
    have hih := ih (Fin.tail F) Φ' hone' hmul' (fun j q => e j.succ q.succ) he'
      (fun j x q i => fam j.succ x q.succ i) hfam' (Fin.tail d) (fun q => w q.succ)
    -- the first block, one factor at a time
    have hblock : ∀ (n : ℕ) (v : Fin n → Γ(F 0, U)),
        Φ (Fin.cons n (0 : Fin r → ℕ)) (weightedTensorPure U (r + 1) F (Fin.cons n (0 : Fin r → ℕ))
          (Fin.cons (α := fun q => Fin ((Fin.cons n (0 : Fin r → ℕ) : Fin (r + 1) → ℕ) q) → Γ(F q, U))
            v (fun _ => Fin.elim0))) =
          ∏ i, Φ (e 0) (weightedTensorPure U (r + 1) F (e 0) (fam 0 (v i))) := by
      intro n
      induction n with
      | zero =>
        intro v
        rw [Fin.prod_univ_zero]
        exact hzero _
      | succ n ihn =>
        intro v
        let A : Fin (r + 1) → ℕ := Fin.cons n (0 : Fin r → ℕ)
        let A' : Fin (r + 1) → ℕ := Fin.cons (n + 1) (0 : Fin r → ℕ)
        let WA : ∀ q, Fin (A q) → Γ(F q, U) := Fin.cons (Fin.init v) (fun _ => Fin.elim0)
        let WA' : ∀ q, Fin (A' q) → Γ(F q, U) := Fin.cons v (fun _ => Fin.elim0)
        have hne : A + e 0 = A' := by
          funext q
          refine Fin.cases ?_ (fun q₁ => ?_) q
          · show n + e 0 0 = n + 1
            rw [he 0 0, if_pos rfl]
          · show 0 + e 0 q₁.succ = 0
            rw [he 0 q₁.succ, if_neg (Fin.succ_ne_zero q₁)]
        have hw : ∀ (q : Fin (r + 1)) (i : Fin (A' q)),
            WA' q i = Fin.append (WA q) (fam 0 (v (Fin.last n)) q) (Fin.cast (congrFun hne.symm q) i) := by
          intro q
          refine Fin.cases ?_ (fun q₁ => ?_) q
          · intro i
            obtain ⟨j, rfl⟩ : ∃ j : Fin (n + e 0 0), Fin.cast (congrFun hne 0) j = i :=
              ⟨Fin.cast (congrFun hne 0).symm i, Fin.ext rfl⟩
            have hj : Fin.cast (congrFun hne.symm 0) (Fin.cast (congrFun hne 0) j) = j := Fin.ext rfl
            show v (Fin.cast (congrFun hne 0) j) =
              Fin.append (Fin.init v) (fam 0 (v (Fin.last n)) 0) (Fin.cast (congrFun hne.symm 0) (Fin.cast _ j))
            refine Eq.trans ?_ (congrArg (Fin.append (Fin.init v) (fam 0 (v (Fin.last n)) 0)) hj).symm
            induction j using Fin.addCases with
            | left j => rw [Fin.append_left]; exact congrArg v (Fin.ext rfl)
            | right j =>
              rw [Fin.append_right, hfam 0 (v (Fin.last n)) j]
              refine congrArg v (Fin.ext ?_)
              have h1 : e 0 0 = 1 := by rw [he 0 0, if_pos rfl]
              have hj1 : (j : ℕ) < 1 := lt_of_lt_of_eq j.isLt h1
              show n + (j : ℕ) = n
              omega
          · intro i
            exact (show Fin 0 from i).elim0
        calc Φ A' (weightedTensorPure U (r + 1) F A' WA')
            = Φ (A + e 0) (weightedTensorCast U (r + 1) F hne.symm (weightedTensorPure U (r + 1) F A' WA')) :=
              (hΦcast hne.symm _).symm
          _ = Φ (A + e 0) (weightedTensorPure U (r + 1) F (A + e 0)
                (fun q => Fin.append (WA q) (fam 0 (v (Fin.last n)) q))) :=
              congrArg (Φ (A + e 0)) (weightedTensorCast_weightedTensorPure U (r + 1) F hne.symm _ _ hw)
          _ = Φ (A + e 0) ((AlgebraicGeometry.Scheme.weightedSymTensorMul (r + 1) F A (e 0)).app U
                (AlgebraicGeometry.Scheme.Modules.tsec _ _ U (weightedTensorPure U (r + 1) F A WA)
                  (weightedTensorPure U (r + 1) F (e 0) (fam 0 (v (Fin.last n)))))) :=
              congrArg (Φ (A + e 0))
                (weightedSymTensorMul_app_weightedTensorPure U (r + 1) F A (e 0) WA (fam 0 (v (Fin.last n)))).symm
          _ = Φ A (weightedTensorPure U (r + 1) F A WA) *
                Φ (e 0) (weightedTensorPure U (r + 1) F (e 0) (fam 0 (v (Fin.last n)))) := hmul _ _ _ _
          _ = (∏ i : Fin n, Φ (e 0) (weightedTensorPure U (r + 1) F (e 0) (fam 0 (Fin.init v i)))) *
                Φ (e 0) (weightedTensorPure U (r + 1) F (e 0) (fam 0 (v (Fin.last n)))) :=
              congrArg₂ (· * ·) (ihn (Fin.init v)) rfl
          _ = ∏ i, Φ (e 0) (weightedTensorPure U (r + 1) F (e 0) (fam 0 (v i))) :=
              (Fin.prod_univ_castSucc (fun i => Φ (e 0) (weightedTensorPure U (r + 1) F (e 0) (fam 0 (v i))))).symm
    -- assembly: `d = cons (d 0) 0 + cons 0 (tail d)`
    let A : Fin (r + 1) → ℕ := Fin.cons (d 0) (0 : Fin r → ℕ)
    let B : Fin (r + 1) → ℕ := Fin.cons (0 : ℕ) (Fin.tail d)
    let WA : ∀ q, Fin (A q) → Γ(F q, U) := Fin.cons (w 0) (fun _ => Fin.elim0)
    let WB : ∀ q, Fin (B q) → Γ(F q, U) := Fin.cons Fin.elim0 (fun q => w q.succ)
    have hd : A + B = d := by
      funext q
      refine Fin.cases ?_ (fun q₁ => ?_) q
      · show d 0 + 0 = d 0
        exact Nat.add_zero _
      · show 0 + d q₁.succ = d q₁.succ
        exact Nat.zero_add _
    have hstep : ∀ (q : Fin r) (x : Γ(F q.succ, U)),
        Φ' (fun q₁ => e q.succ q₁.succ) (weightedTensorPure U r (Fin.tail F) (fun q₁ => e q.succ q₁.succ)
          (fun q₁ i => fam q.succ x q₁.succ i)) =
          Φ (e q.succ) (weightedTensorPure U (r + 1) F (e q.succ) (fam q.succ x)) := by
      intro q x
      let E : Fin (r + 1) → ℕ := Fin.cons (0 : ℕ) (fun q₁ => e q.succ q₁.succ)
      have hq : E = e q.succ := by
        funext q₂
        refine Fin.cases ?_ (fun _ => rfl) q₂
        show 0 = e q.succ 0
        rw [he q.succ 0, if_neg (Fin.succ_ne_zero q).symm]
      refine (hΦ' _ _).trans ?_
      refine ((hΦcast hq _).symm.trans ?_)
      refine congrArg (Φ (e q.succ)) (weightedTensorCast_weightedTensorPure U (r + 1) F hq _ _ fun q₂ => ?_)
      refine Fin.cases ?_ (fun q₃ => ?_) q₂
      · intro i
        exact (show Fin 0 from i).elim0
      · intro i
        show fam q.succ x q₃.succ i = fam q.succ x q₃.succ (Fin.cast _ i)
        exact congrArg _ (Fin.ext rfl)
    calc Φ d (weightedTensorPure U (r + 1) F d w)
        = Φ (A + B) (weightedTensorCast U (r + 1) F hd.symm (weightedTensorPure U (r + 1) F d w)) :=
          (hΦcast hd.symm _).symm
      _ = Φ (A + B) (weightedTensorPure U (r + 1) F (A + B) (fun q => Fin.append (WA q) (WB q))) := by
          refine congrArg (Φ (A + B)) (weightedTensorCast_weightedTensorPure U (r + 1) F hd.symm _ _ fun q => ?_)
          refine Fin.cases ?_ (fun q₁ => ?_) q
          · intro i
            show w 0 i = Fin.append (w 0) (Fin.elim0 : Fin 0 → Γ(F 0, U)) (Fin.cast _ i)
            rw [Fin.append_elim0]
            exact congrArg _ (Fin.ext rfl)
          · intro i
            show w q₁.succ i = Fin.append (Fin.elim0 : Fin 0 → Γ(F q₁.succ, U)) (w q₁.succ) (Fin.cast _ i)
            rw [Fin.append_left_nil _ _ rfl]
            exact congrArg _ (Fin.ext rfl)
      _ = Φ (A + B) ((AlgebraicGeometry.Scheme.weightedSymTensorMul (r + 1) F A B).app U
            (AlgebraicGeometry.Scheme.Modules.tsec _ _ U (weightedTensorPure U (r + 1) F A WA)
              (weightedTensorPure U (r + 1) F B WB))) :=
          congrArg (Φ (A + B)) (weightedSymTensorMul_app_weightedTensorPure U (r + 1) F A B WA WB).symm
      _ = Φ A (weightedTensorPure U (r + 1) F A WA) * Φ B (weightedTensorPure U (r + 1) F B WB) := hmul A B WA WB
      _ = (∏ i, Φ (e 0) (weightedTensorPure U (r + 1) F (e 0) (fam 0 (w 0 i)))) *
            ∏ q : Fin r, ∏ i, Φ (e q.succ) (weightedTensorPure U (r + 1) F (e q.succ) (fam q.succ (w q.succ i))) :=
          congrArg₂ (· * ·) (hblock (d 0) (w 0))
            ((hΦ' (Fin.tail d) (fun q => w q.succ)).symm.trans
              (hih.trans (Fintype.prod_congr _ _ fun q => Fintype.prod_congr _ _ fun i => hstep q (w q.succ i))))
      _ = ∏ q, ∏ i, Φ (e q) (weightedTensorPure U (r + 1) F (e q) (fam q (w q i))) :=
          (Fin.prod_univ_succ (fun q => ∏ i, Φ (e q) (weightedTensorPure U (r + 1) F (e q) (fam q (w q i))))).symm

/-! ## The section ring of the weighted symmetric algebra as an evaluation -/

namespace weightedSymAlgebra

variable {r : ℕ} (V : Fin r → X.Modules) [∀ q, (V q).IsLocallyFree] [∀ q, (V q).IsFiniteType]

/-- The weight `Σ_q (q + 1) d q` of a multidegree (the `m` with `d ∈ weightedSymIndex r m`). -/
def wdeg (d : Fin r → ℕ) : ℕ := ∑ q : Fin r, ((q : ℕ) + 1) * d q

theorem le_wdeg (d : Fin r → ℕ) (q : Fin r) : d q ≤ wdeg d :=
  calc d q = 1 * d q := (Nat.one_mul _).symm
    _ ≤ ((q : ℕ) + 1) * d q := Nat.mul_le_mul_right _ (by omega)
    _ ≤ ∑ q' : Fin r, ((q' : ℕ) + 1) * d q' :=
      Finset.single_le_sum (f := fun q' : Fin r => ((q' : ℕ) + 1) * d q') (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ q)

/-- A multidegree as an element of `weightedSymIndex r (wdeg d)`. -/
def mkIndex (d : Fin r → ℕ) : AlgebraicGeometry.Scheme.weightedSymIndex r (wdeg d) :=
  ⟨fun q => ⟨d q, Nat.lt_succ_of_le (le_wdeg d q)⟩, rfl⟩

theorem dv_mkIndex (d : Fin r → ℕ) : dv (mkIndex d) = d := rfl

theorem dv_single (j q : Fin r) :
    dv (AlgebraicGeometry.Scheme.weightedSymIndex.single j) q = if q = j then 1 else 0 := by
  simp only [dv, AlgebraicGeometry.Scheme.weightedSymIndex.single]
  split_ifs <;> rfl

/-- **The evaluation of the recursive layer in the section ring**: a section of `T_d` is put into the `wdeg d`-th
piece of `⨁_m Γ(U, S_m)` through the biproduct inclusion `ι_d`. -/
def pieceOf (d : Fin r → ℕ)
    (x : Γ(AlgebraicGeometry.Scheme.weightedSymTensor r (gen V) d, U)) :
    (AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsRing U :=
  (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U (wdeg d)
    ((biproduct.ι (fun d => term V d) (mkIndex d)).app U x)

/-- `ofPiece m (ι_d x) = pieceOf (dv d) x` for any index `d` of weight `m`. -/
theorem ofPiece_ι_eq_pieceOf {m : ℕ} (d : AlgebraicGeometry.Scheme.weightedSymIndex r m) (x : Γ(term V d, U)) :
    (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U m
        ((biproduct.ι (fun d => term V d) d).app U x) = pieceOf U V (dv d) x := by
  have h : m = wdeg (dv d) := d.2.symm
  have h1 := congrArg (fun k => k.app U x) (eqToHom_comp_ι V h (d := d) (d' := mkIndex (dv d)) (fun q => rfl))
  simp only at h1
  have hι : (biproduct.ι (fun d => term V d) (mkIndex (dv d))).app U x =
      (eqToHom (congrArg (AlgebraicGeometry.Scheme.weightedSymAlgebra.part V) h)).app U
        ((biproduct.ι (fun d => term V d) d).app U x) :=
    ((congrArg (fun y => (biproduct.ι (fun d => term V d) (mkIndex (dv d))).app U y)
      (Modules.eqToHom_app_self U _ x)).symm.trans (Modules.comp_app_apply_sec U _ _ x).symm).trans
      (h1.trans (Modules.comp_app_apply_sec U _ _ x))
  exact ((congrArg ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U (wdeg (dv d))) hι).trans
    (GradedQCAlgebra.ofPiece_eqToHom_app U (AlgebraicGeometry.Scheme.weightedSymAlgebra V) h _)).symm

/-- `pieceOf` is multiplicative on `mulTerm` (`ι_tensor_ι_comp_mulHom` on sections). -/
theorem pieceOf_mul (a b : Fin r → ℕ) (x : Γ(AlgebraicGeometry.Scheme.weightedSymTensor r (gen V) a, U))
    (y : Γ(AlgebraicGeometry.Scheme.weightedSymTensor r (gen V) b, U)) :
    pieceOf U V (a + b) ((AlgebraicGeometry.Scheme.weightedSymTensorMul r (gen V) a b).app U
        (AlgebraicGeometry.Scheme.Modules.tsec _ _ U x y)) =
      pieceOf U V a x * pieceOf U V b y := by
  have h := congrArg (fun k => k.app U (AlgebraicGeometry.Scheme.Modules.tsec _ _ U x y))
    (ι_tensor_ι_comp_mulHom V (mkIndex a) (mkIndex b))
  simp only at h
  have h' : (mulHom V (wdeg a) (wdeg b)).app U (AlgebraicGeometry.Scheme.Modules.tsec _ _ U
      ((biproduct.ι (fun d => term V d) (mkIndex a)).app U x) ((biproduct.ι (fun d => term V d) (mkIndex b)).app U y)) =
      (biproduct.ι (fun d => term V d) ((mkIndex a).add (mkIndex b))).app U
        ((mulTerm V (mkIndex a) (mkIndex b)).app U (AlgebraicGeometry.Scheme.Modules.tsec _ _ U x y)) :=
    ((congrArg _ (Modules.tensorHom_app_tsec U _ _ x y)).symm.trans (Modules.comp_app_apply_sec U _ _ _).symm).trans
      (h.trans (Modules.comp_app_apply_sec U _ _ _))
  calc pieceOf U V (a + b) ((AlgebraicGeometry.Scheme.weightedSymTensorMul r (gen V) a b).app U
        (AlgebraicGeometry.Scheme.Modules.tsec _ _ U x y))
      = (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U (wdeg a + wdeg b)
          ((biproduct.ι (fun d => term V d) ((mkIndex a).add (mkIndex b))).app U
            ((mulTerm V (mkIndex a) (mkIndex b)).app U (AlgebraicGeometry.Scheme.Modules.tsec _ _ U x y))) :=
        (ofPiece_ι_eq_pieceOf U V ((mkIndex a).add (mkIndex b)) _).symm
    _ = (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U (wdeg a + wdeg b)
          (((AlgebraicGeometry.Scheme.weightedSymAlgebra V).mul (wdeg a) (wdeg b)).app U
            (AlgebraicGeometry.Scheme.Modules.tsec _ _ U ((biproduct.ι (fun d => term V d) (mkIndex a)).app U x)
              ((biproduct.ι (fun d => term V d) (mkIndex b)).app U y))) := congrArg _ h'.symm
    _ = (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U (wdeg a)
          ((biproduct.ι (fun d => term V d) (mkIndex a)).app U x) *
        (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U (wdeg b)
          ((biproduct.ι (fun d => term V d) (mkIndex b)).app U y) :=
        GradedQCAlgebra.ofPiece_mul_app_tsec U (AlgebraicGeometry.Scheme.weightedSymAlgebra V) _ _
    _ = pieceOf U V a x * pieceOf U V b y := rfl

/-- `pieceOf` is unital. -/
theorem pieceOf_one :
    pieceOf U V 0 ((AlgebraicGeometry.Scheme.weightedSymTensorOne r (gen V)).app U
      (AlgebraicGeometry.Scheme.Modules.unitSec U)) = 1 :=
  calc pieceOf U V 0 ((AlgebraicGeometry.Scheme.weightedSymTensorOne r (gen V)).app U
        (AlgebraicGeometry.Scheme.Modules.unitSec U))
      = (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U 0
          ((biproduct.ι (fun d => term V d) (⟨0, by simp⟩ : AlgebraicGeometry.Scheme.weightedSymIndex r 0)).app U
            ((AlgebraicGeometry.Scheme.weightedSymTensorOne r (gen V)).app U
              (AlgebraicGeometry.Scheme.Modules.unitSec U))) :=
        (ofPiece_ι_eq_pieceOf U V (⟨0, by simp⟩ : AlgebraicGeometry.Scheme.weightedSymIndex r 0) _).symm
    _ = (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U 0
          ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).one.app U (AlgebraicGeometry.Scheme.Modules.unitSec U)) :=
        congrArg _ (Modules.comp_app_apply_sec U _ _ _).symm
    _ = 1 := GradedQCAlgebra.ofPiece_one_app_one U (AlgebraicGeometry.Scheme.weightedSymAlgebra V)

/-- The one-factor family of the generator index `δ_j` with factor `x`. -/
def genFam (j : Fin r) (x : Γ(AlgebraicGeometry.Scheme.Modules.dual (V j), U)) :
    ∀ q, Fin (dv (AlgebraicGeometry.Scheme.weightedSymIndex.single j) q) →
      Γ(AlgebraicGeometry.Scheme.Modules.dual (V q), U) :=
  fun q i => if h : q = j then
      cast (congrArg (fun q => (Γ(AlgebraicGeometry.Scheme.Modules.dual (V q), U) : Type u)) h.symm) x
    else (Fin.cast ((dv_single j q).trans (if_neg h)) i).elim0

omit [∀ q, (V q).IsLocallyFree] [∀ q, (V q).IsFiniteType] in
theorem genFam_self (j : Fin r) (x : Γ(AlgebraicGeometry.Scheme.Modules.dual (V j), U))
    (i : Fin (dv (AlgebraicGeometry.Scheme.weightedSymIndex.single j) j)) : genFam U V j x j i = x := by
  show (if h : j = j then _ else _) = x
  rw [dif_pos rfl]
  exact cast_eq _ x

/-- **Pure sections in the section ring**: `ι_d (pure d w) = ∏_q ∏_i genIncl_q (w q i)` in `⨁_m Γ(U, S_m)`. -/
theorem ofPiece_ι_weightedTensorPure {m : ℕ} (d : AlgebraicGeometry.Scheme.weightedSymIndex r m)
    (w : ∀ q, Fin (dv d q) → Γ(AlgebraicGeometry.Scheme.Modules.dual (V q), U)) :
    (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U m ((biproduct.ι (fun d => term V d) d).app U
        (weightedTensorPure U r (gen V) (dv d) w)) =
      ∏ q : Fin r, ∏ i, (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U ((q : ℕ) + 1)
        ((genIncl V q).app U (w q i)) := by
  refine (ofPiece_ι_eq_pieceOf U V d _).trans ?_
  refine (weightedTensorPure_eq_prod U r (gen V) (pieceOf U V) (pieceOf_one U V)
    (fun a b _ _ => pieceOf_mul U V a b _ _)
    (fun j => dv (AlgebraicGeometry.Scheme.weightedSymIndex.single j)) dv_single (genFam U V) (genFam_self U V)
    (dv d) w).trans ?_
  refine Fintype.prod_congr _ _ fun q => Fintype.prod_congr _ _ fun i => ?_
  refine (ofPiece_ι_eq_pieceOf U V (AlgebraicGeometry.Scheme.weightedSymIndex.single q) _).symm.trans ?_
  refine congrArg _ ?_
  refine (congrArg _ (weightedSymTensorGen_app U r (gen V) q _ (dv_single q) (w q i) (genFam U V q (w q i))
    (genFam_self U V q (w q i))).symm).trans ?_
  exact (Modules.comp_app_apply_sec U _ _ _).symm

end weightedSymAlgebra

/-! ## The two leaves that use the affine hypothesis -/

/-- **Pure sections span the sections of `T_d` over an affine open** (Stacks 01I8 + 01CG on sections).

Natural-language proof, by induction on `r` along `weightedSymTensor`. `r = 0`: `T_d = 𝟙_ = O_X`, `Γ(U, O_X) = R` is
spanned by the pure section `1`. `r + 1`: `T_d = Sym^{d 0}(F 0) ⊗ T'`, with `T' := weightedSymTensor r (tail F) (tail d)`
quasi-coherent (`weightedSymTensor_isQuasicoherent`) and `Sym^{d 0}(F 0) = (symGradedAlgebra (F 0)).part (d 0)` quasi-coherent
(`GradedQCAlgebra.quasicoherent`).
1. `Γ(U, Sym^{d 0}(F 0) ⊗ T')` is spanned by the `tsec a b` (`a ∈ Γ(U, Sym^{d 0}(F 0))`, `b ∈ Γ(U, T')`): this is the
   surjectivity half of `tensorSectionsHom_app_bijective_of_isAffineOpen` (Stacks 01I8;
   `tensorSectionsHom_app` says the map sends `a ⊗ₜ b` to `tensorSections a b`, and `Γ(U, A) ⊗_R Γ(U, B)` is spanned by the
   `a ⊗ₜ b`, `TensorProduct.span_tmul_eq_top`). `tsec` is bilinear (`tsec_add_left/right`, `tsec_smul_left/right`), so it
   suffices that `a` runs through a spanning set of `Γ(U, Sym^{d 0}(F 0))` and `b` through one of `Γ(U, T')`.
2. `Γ(U, T')` is spanned by the pure sections of `T'` (induction hypothesis).
3. `Γ(U, (symGradedAlgebra (F 0)).part e)` is spanned by the `gradedPure e v`, `v : Fin e → Γ(U, F 0)`. Indeed
   `symGradedAlgebra (F 0) = symGradedAlgebraOfQC (F 0) _` (`symGradedAlgebra_of_isQuasicoherent`), so `part e = symPow (F 0) e`
   and `(symPowπ (F 0) e).app U : Γ(U, (F 0)^{⊗e}) → Γ(U, Sym^e (F 0))` is surjective
   (`symPowπ_app_surjective_of_isAffineOpen`); `Γ(U, (F 0)^{⊗e})` is
   spanned by the iterated `tsec` of sections of `F 0` (step 1 applied `e` times along `monoidalPow`, with `monoidalPow`
   quasi-coherent), and the image under `symPowπ` of such an iterated pure tensor `v_0 ⊗ ⋯ ⊗ v_{e-1}` is `gradedPure e v`:
   `symGen (F 0) = (λ_ _).inv ≫ symPowπ (F 0) 1 ≫ eqToHom _` (`symGen_eq_of_isQuasicoherent`,
   `TotalSpaceSectionConstructions.lean`) and `(symPowπ e ⊗ₘ symPowπ 1) ≫ symPowMul e 1 = (monoidalPowCat e 1).hom ≫ symPowπ (e+1)`
   (`tensorHom_symPowπ_symPowMul`), with `(monoidalPowCat e 1).hom = (α_ _ _ _).inv ≫ (ρ_ _).hom ▷ _` on sections
   `tsec x (tsec 1 v) ↦ tsec x v` (`associator_inv_app_tsec`, `rightUnitor_app_tsec_unitSec`), so by induction on `e`
   `symPowπ (e+1) (x ⊗ v) = S.mul e 1 (symPowπ e x ⊗ symGen v) = gradedPure (e+1) (snoc v' v)`.
4. Hence `Γ(U, T_d)` is spanned by the `tsec (gradedPure (d 0) (w 0)) (pure (tail d) (tail w)) = pure d w`.

Uses the bijectivity of `tensorSectionsHom` on affine opens (surjectivity only) and the surjectivity of
`symPowπ` on affine opens. Edge cases: `U = ⊥` (all modules zero); `d = 0` (the pure section is the
unit `1`, spanning `Γ(U, O_X) = R`).

Formalized along these lines: steps 1–3 are `Modules.mem_span_image2_tsec`,
`Modules.span_range_monoidalPowPure_eq_top`, `GradedQCAlgebra.span_range_gradedPure_eq_top`
(`WeightedSymSectionsRingEquivSymEvalSpan.lean`); step 4 is the induction below. -/
theorem span_range_weightedTensorPure_eq_top (r : ℕ) (F : Fin r → X.Modules) [∀ q, (F q).IsQuasicoherent]
    (d : Fin r → ℕ) {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) :
    Submodule.span Γ(X, U) (Set.range (weightedTensorPure U r F d)) = ⊤ := by
  induction r with
  | zero =>
    rw [eq_top_iff]
    intro x _
    have hx : x = (show Γ(X, U) from x) • weightedTensorPure U 0 F d (fun q => q.elim0) :=
      (mul_one (show Γ(X, U) from x)).symm
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  | succ r ih =>
    have hq : ∀ q, (Fin.tail F q).IsQuasicoherent := fun q => inferInstanceAs ((F q.succ).IsQuasicoherent)
    have hT : (AlgebraicGeometry.Scheme.weightedSymTensor r (Fin.tail F) (Fin.tail d)).IsQuasicoherent :=
      weightedSymTensor_isQuasicoherent r _ _
    have hP : ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (F 0)).part (d 0)).IsQuasicoherent :=
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (F 0)).quasicoherent (d 0)
    have hA : Submodule.span Γ(X, U) (Set.range ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (F 0)).gradedPure U
        (AlgebraicGeometry.Scheme.Modules.symGen (F 0)) (d 0))) = ⊤ :=
      GradedQCAlgebra.span_range_gradedPure_eq_top (F 0) inferInstance
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_of_isQuasicoherent (F 0) inferInstance)
        (AlgebraicGeometry.Scheme.Modules.symGen_heq (F 0) inferInstance) (d 0) hU
    have hB := ih (Fin.tail F) (Fin.tail d)
    rw [eq_top_iff]
    intro x _
    have hx : (x : Γ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (F 0)).part (d 0) ⊗
        AlgebraicGeometry.Scheme.weightedSymTensor r (Fin.tail F) (Fin.tail d), U)) ∈ Submodule.span Γ(X, U)
        (Set.image2 (Modules.tsec _ _ U) (Set.range ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (F 0)).gradedPure U
          (AlgebraicGeometry.Scheme.Modules.symGen (F 0)) (d 0)))
          (Set.range (weightedTensorPure U r (Fin.tail F) (Fin.tail d)))) :=
      Modules.mem_span_image2_tsec _ _ hU hA hB x
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨_, ⟨v, rfl⟩, _, ⟨w', rfl⟩, rfl⟩
    exact ⟨Fin.cons (α := fun q => Fin (d q) → Γ(F q, U)) v w', rfl⟩

/-- **Linear maps out of `Γ(U, T_d)` may be prescribed on pure sections** by a multilinear expression, for affine `U`
(Stacks 01I8 + 01CG on sections: `Γ(U, T_d) = ⊗_q Sym^{d q}_R Γ(U, F q)` and the universal properties of `⊗` and `Sym`).

Natural-language proof. Write `R := Γ(U)`, `W q := Γ(U, F q)`. Induction on `r` along `weightedSymTensor`.
`r = 0`: `Γ(U, 𝟙_) = R`, take `ψ := c ↦ c • 1` (`algebraMap`); the pure section is `1`, the empty product is `1`.
`r + 1`: `T_d = Sym^{d 0}(F 0) ⊗ T'`. By `tensorSectionsHom_app_bijective_of_isAffineOpen` (both `Sym^{d 0}(F 0)` and `T'` quasi-coherent) the `R`-linear map
`(tensorSectionsHom _ _).app (op U) : Γ(U, Sym^{d 0}(F 0)) ⊗_R Γ(U, T') → Γ(U, Sym^{d 0}(F 0) ⊗ T')`, `a ⊗ₜ b ↦ tsec a b`,
is bijective (`LinearEquiv.ofBijective`). So an `R`-linear map out of `Γ(U, T_d)` is the same as an `R`-bilinear map
`Γ(U, Sym^{d 0}(F 0)) × Γ(U, T') → C` (`TensorProduct.lift`). Take `(a, b) ↦ ψ₀ a * ψ' b` where `ψ'` comes from the induction
hypothesis for `T'` (with the tail of `g`) and `ψ₀ : Γ(U, Sym^{d 0}(F 0)) →ₗ[R] C` satisfies
`ψ₀ (gradedPure (d 0) v) = ∏_i g 0 (v i)`. Construction of `ψ₀` for `e := d 0`:
1. `Γ(U, (F 0)^{⊗e}) → C`, `v_0 ⊗ ⋯ ⊗ v_{e-1} ↦ ∏_i g 0 (v_i)`: by induction on `e` with `monoidalPow (F 0) (e+1) = monoidalPow e ⊗ F 0`
   and the tensor-sections bijection again (`TensorProduct.lift` of `(x, v) ↦ ψ_e x * g 0 v`); `e = 0`: `algebraMap`.
2. This map kills `transp_i x - x` for every adjacent transposition `monoidalPowTransp (F 0) e i` (the braiding on sections swaps
   the two factors of `tsec`, `braiding_app_tsec`, and `C` is commutative), so it vanishes on the kernel of
   `(symPowπ (F 0) e).app U`, which is the `R`-span of these elements (`symPowπ_app_eq_zero_iff_of_isAffineOpen`);
   `(symPowπ (F 0) e).app U` is surjective (`symPowπ_app_surjective_of_isAffineOpen`),
   so the map descends to `ψ₀ : Γ(U, symPow (F 0) e) →ₗ[R] C` (`Submodule.liftQ` + `LinearMap.quotKerEquivOfSurjective`), and
   `symGradedAlgebra (F 0) = symGradedAlgebraOfQC (F 0) _` identifies `part e` with `symPow (F 0) e`
   (`symGradedAlgebra_part_eq_symPow`).
3. `ψ₀ (gradedPure e v) = ∏_i g 0 (v i)`: `gradedPure e v` is the image under `symPowπ e` of the pure tensor `v_0 ⊗ ⋯ ⊗ v_{e-1}`
   (step 3 of the proof of `span_range_weightedTensorPure_eq_top`).
Finally `ψ (pure d w) = ψ (tsec (gradedPure (d 0) (w 0)) (pure (tail d) (tail w))) = ψ₀ (gradedPure (d 0) (w 0)) * ψ' (pure (tail d) (tail w))
= (∏_i g 0 (w 0 i)) * ∏_{q} ∏_i g q.succ (w q.succ i) = ∏_q ∏_i g q (w q i)` (`Fin.prod_univ_succ`).

Uses the bijectivity of `tensorSectionsHom` on affine opens and the kernel description of `symPowπ` on affine opens.
Edge cases: `U = ⊥` (`R = 0`, `C` is the zero ring, any map works); `d q = 0` for all `q` (`ψ = algebraMap`, matching the
empty products).

Formalized along these lines: the tensor step is `Modules.exists_linearMap_tsec`, the construction of
`ψ₀` (steps 1–3) is `GradedQCAlgebra.exists_linearMap_gradedPure` (`WeightedSymSectionsRingEquivSymEvalLinear.lean`);
the induction on `r` is below. -/
theorem exists_linearMap_weightedTensorPure (r : ℕ) (F : Fin r → X.Modules) [∀ q, (F q).IsQuasicoherent]
    (d : Fin r → ℕ) {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) {C : Type u} [CommRing C]
    [Algebra Γ(X, U) C] (g : ∀ q, Γ(F q, U) →ₗ[Γ(X, U)] C) :
    ∃ ψ : Γ(AlgebraicGeometry.Scheme.weightedSymTensor r F d, U) →ₗ[Γ(X, U)] C,
      ∀ w, ψ (weightedTensorPure U r F d w) = ∏ q, ∏ i, g q (w q i) := by
  induction r with
  | zero =>
    refine ⟨(Algebra.linearMap Γ(X, U) C).comp (Modules.unitSecLin U), fun w => ?_⟩
    rw [Fin.prod_univ_zero]
    exact map_one (algebraMap Γ(X, U) C)
  | succ r ih =>
    have hq : ∀ q, (Fin.tail F q).IsQuasicoherent := fun q => inferInstanceAs ((F q.succ).IsQuasicoherent)
    have hT : (AlgebraicGeometry.Scheme.weightedSymTensor r (Fin.tail F) (Fin.tail d)).IsQuasicoherent :=
      weightedSymTensor_isQuasicoherent r _ _
    have hP : ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (F 0)).part (d 0)).IsQuasicoherent :=
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (F 0)).quasicoherent (d 0)
    obtain ⟨ψ', hψ'⟩ := ih (Fin.tail F) (Fin.tail d) (fun q => g q.succ)
    obtain ⟨ψ₀, hψ₀⟩ := GradedQCAlgebra.exists_linearMap_gradedPure (F 0) inferInstance
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_of_isQuasicoherent (F 0) inferInstance)
      (AlgebraicGeometry.Scheme.Modules.symGen_heq (F 0) inferInstance) (d 0) hU (g 0)
    obtain ⟨Ψ, hΨ⟩ := Modules.exists_linearMap_tsec ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (F 0)).part (d 0))
      (AlgebraicGeometry.Scheme.weightedSymTensor r (Fin.tail F) (Fin.tail d)) hU
      ((LinearMap.mul Γ(X, U) C).compl₁₂ ψ₀ ψ')
    refine ⟨Ψ, fun w => ?_⟩
    refine (hΨ ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (F 0)).gradedPure U
      (AlgebraicGeometry.Scheme.Modules.symGen (F 0)) (d 0) (w 0))
      (weightedTensorPure U r (Fin.tail F) (Fin.tail d) (fun q => w q.succ))).trans ?_
    rw [LinearMap.compl₁₂_apply, LinearMap.mul_apply', hψ₀]
    exact (congrArg ((∏ i, g 0 (w 0 i)) * ·) (hψ' (fun q => w q.succ))).trans
      (Fin.prod_univ_succ (fun q => ∏ i, g q (w q i))).symm

/-! ## Consequences for the section ring of `weightedSymAlgebra V` -/

namespace weightedSymAlgebra

variable {r : ℕ} (V : Fin r → X.Modules) [∀ q, (V q).IsLocallyFree] [∀ q, (V q).IsFiniteType]

theorem ofPiece_sum (S : X.GradedQCAlgebra) (m : ℕ) {ι : Type*} (s : Finset ι) (f : ι → S.sectionsPiece U m) :
    S.ofPiece U m (∑ i ∈ s, f i) = ∑ i ∈ s, S.ofPiece U m (f i) :=
  map_sum (DirectSum.of (S.sectionsPiece U) m) f s

theorem ofPiece_add (S : X.GradedQCAlgebra) (m : ℕ) (a b : S.sectionsPiece U m) :
    S.ofPiece U m (a + b) = S.ofPiece U m a + S.ofPiece U m b :=
  map_add (DirectSum.of (S.sectionsPiece U) m) a b

theorem ofPiece_zero (S : X.GradedQCAlgebra) (m : ℕ) : S.ofPiece U m 0 = 0 :=
  map_zero (DirectSum.of (S.sectionsPiece U) m)

/-- **The section ring is generated by `Γ(U)` and the generators** on an affine open: the subring of
`⨁_m Γ(U, S_m)` generated by the image of `sectionsUnitHom` and the sections `genIncl_q x` (`x ∈ Γ(U, V_q^∨)`) is everything.
Proof: decompose `z = Σ_m ofPiece m z_m` (`sum_supp`), `z_m = Σ_d ι_d (π_d z_m)` (`biproduct_sections_total`), each
`π_d z_m ∈ Γ(U, T_d)` is an `R`-combination of pure sections (`span_range_weightedTensorPure_eq_top`), and
`ofPiece m (ι_d (c • pure d w)) = sectionsUnitHom c * ∏_q ∏_i genIncl_q (w q i)` (`ofPiece_ι_weightedTensorPure`,
`sectionsUnitHom_mul_ofPiece`). -/
theorem closure_sectionsUnitHom_genIncl_eq_top {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) :
    Subring.closure (Set.range ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsUnitHom U) ∪
      ⋃ q : Fin r, Set.range (fun x : Γ(AlgebraicGeometry.Scheme.Modules.dual (V q), U) =>
        (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U ((q : ℕ) + 1) ((genIncl V q).app U x))) = ⊤ := by
  have : ∀ q, (gen V q).IsQuasicoherent := fun q =>
    AlgebraicGeometry.Scheme.Modules.dual_isQuasicoherent_of_locallyFree (V q)
  set S := AlgebraicGeometry.Scheme.weightedSymAlgebra V with hS
  set K := Subring.closure (Set.range (S.sectionsUnitHom U) ∪
    ⋃ q : Fin r, Set.range (fun x : Γ(AlgebraicGeometry.Scheme.Modules.dual (V q), U) =>
      S.ofPiece U ((q : ℕ) + 1) ((genIncl V q).app U x))) with hK
  refine (Subring.eq_top_iff' K).mpr fun z => ?_
  rw [← (AlgebraicGeometry.Scheme.weightedSymAlgebra V).sum_supp U z]
  refine Subring.sum_mem K fun m _ => ?_
  generalize (AlgebraicGeometry.Scheme.weightedSymAlgebra V).component U m z = a
  have ha : (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U m a =
      ∑ d, (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U m
        ((biproduct.ι (fun d => term V d) d).app U ((biproduct.π (fun d => term V d) d).app U a)) :=
    (congrArg _ (Modules.biproduct_sections_total (fun d => term V d) U a)).trans
      (ofPiece_sum U (AlgebraicGeometry.Scheme.weightedSymAlgebra V) m _ _)
  rw [ha]
  refine Subring.sum_mem K fun d _ => ?_
  generalize (biproduct.π (fun d => term V d) d).app U a = x
  have hx : x ∈ Submodule.span Γ(X, U) (Set.range (weightedTensorPure U r (gen V) (dv d))) := by
    rw [span_range_weightedTensorPure_eq_top r (gen V) (dv d) hU]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨w, rfl⟩
    rw [ofPiece_ι_weightedTensorPure]
    refine Subring.prod_mem K fun q _ => Subring.prod_mem K fun i _ => Subring.subset_closure ?_
    exact Or.inr (Set.mem_iUnion.mpr ⟨q, ⟨w q i, rfl⟩⟩)
  · have h0 : (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U m
        ((biproduct.ι (fun d => term V d) d).app U 0) = 0 :=
      (congrArg _ (map_zero (ConcreteCategory.hom ((biproduct.ι (fun d => term V d) d).app U)))).trans
        (ofPiece_zero U (AlgebraicGeometry.Scheme.weightedSymAlgebra V) m)
    exact (congrArg (· ∈ K) h0).mpr (zero_mem K)
  · intro x y _ _ hx hy
    have h1 : (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U m
        ((biproduct.ι (fun d => term V d) d).app U (x + y)) =
        (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U m ((biproduct.ι (fun d => term V d) d).app U x) +
        (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U m ((biproduct.ι (fun d => term V d) d).app U y) :=
      (congrArg _ (map_add (ConcreteCategory.hom ((biproduct.ι (fun d => term V d) d).app U)) x y)).trans
        (ofPiece_add U (AlgebraicGeometry.Scheme.weightedSymAlgebra V) m _ _)
    exact (congrArg (· ∈ K) h1).mpr (add_mem hx hy)
  · intro c x _ hx
    have h1 : (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U m
        ((biproduct.ι (fun d => term V d) d).app U (c • x)) =
        (AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsUnitHom U c *
          (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U m ((biproduct.ι (fun d => term V d) d).app U x) :=
      (congrArg _ (Modules.Hom.app_smul (biproduct.ι (fun d => term V d) d) c x)).trans
        ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsUnitHom_mul_ofPiece U c _).symm
    exact (congrArg (· ∈ K) h1).mpr (mul_mem (Subring.subset_closure (Or.inl ⟨c, rfl⟩)) hx)

/-- **Additive evaluations of the section ring prescribed on monomials**: for affine `U`, a commutative `R`-algebra `C`
and `R`-linear `g q : Γ(U, V_q^∨) → C`, there is an additive `ψ : ⨁_m Γ(U, S_m) → C`, `R`-linear for the action through
`sectionsUnitHom`, with `ψ (∏_q ∏_i genIncl_q (w q i)) = ∏_q ∏_i g q (w q i)`.
Proof: `ψ := DirectSum.toAddMonoid (m ↦ Σ_{d ∈ D_m} ψ_{dv d} ∘ π_d)` with `ψ_d` from `exists_linearMap_weightedTensorPure`;
the monomial is `ofPiece (wdeg d) (ι_{mkIndex d} (pure d w))` (`ofPiece_ι_weightedTensorPure`), on which `ψ` is
`ψ_d (pure d w)` (`biproduct_π_ι_self/ne_app_apply`). -/
theorem exists_addMonoidHom_sectionsRing {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) {C : Type u}
    [CommRing C] [Algebra Γ(X, U) C]
    (g : ∀ q, Γ(AlgebraicGeometry.Scheme.Modules.dual (V q), U) →ₗ[Γ(X, U)] C) :
    ∃ ψ : (AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsRing U →+ C,
      (∀ (c : Γ(X, U)) (z : (AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsRing U),
        ψ ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsUnitHom U c * z) = c • ψ z) ∧
      ∀ (d : Fin r → ℕ) (w : ∀ q, Fin (d q) → Γ(AlgebraicGeometry.Scheme.Modules.dual (V q), U)),
        ψ (∏ q : Fin r, ∏ i, (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U ((q : ℕ) + 1)
          ((genIncl V q).app U (w q i))) = ∏ q : Fin r, ∏ i, g q (w q i) := by
  have : ∀ q, (gen V q).IsQuasicoherent := fun q =>
    AlgebraicGeometry.Scheme.Modules.dual_isQuasicoherent_of_locallyFree (V q)
  set S := AlgebraicGeometry.Scheme.weightedSymAlgebra V with hS
  choose ψd hψd using fun d : Fin r → ℕ => exists_linearMap_weightedTensorPure r (gen V) d hU g
  let Ψ : ∀ m : ℕ, Γ(⨁ (fun d : AlgebraicGeometry.Scheme.weightedSymIndex r m => term V d), U) →+ C := fun m =>
    { toFun := fun a => ∑ d : AlgebraicGeometry.Scheme.weightedSymIndex r m,
        ψd (dv d) ((biproduct.π (fun d => term V d) d).app U a)
      map_zero' := Finset.sum_eq_zero fun d _ => by
        rw [map_zero (ConcreteCategory.hom ((biproduct.π (fun d => term V d) d).app U)), map_zero]
      map_add' := fun a b => by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun d _ => by
          rw [map_add (ConcreteCategory.hom ((biproduct.π (fun d => term V d) d).app U)), map_add] }
  let ψ : (AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsRing U →+ C :=
    DirectSum.toAddMonoid (fun m => (Ψ m : (AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsPiece U m →+ C))
  have hΨ : ∀ (m : ℕ) (a : (AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsPiece U m),
      ψ ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U m a) =
        ∑ d : AlgebraicGeometry.Scheme.weightedSymIndex r m, ψd (dv d) ((biproduct.π (fun d => term V d) d).app U a) :=
    fun m a => DirectSum.toAddMonoid_of _ m a
  refine ⟨ψ, fun c z => ?_, fun d w => ?_⟩
  · induction z using DirectSum.induction_on with
    | zero =>
      show ψ ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsUnitHom U c *
        (0 : (AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsRing U)) =
        c • ψ (0 : (AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsRing U)
      rw [mul_zero, map_zero, smul_zero]
    | of m a =>
      calc ψ ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsUnitHom U c *
            (AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U m a)
          = ψ ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U m
              (@HSMul.hSMul Γ(X, U) Γ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).part m, U) Γ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).part m, U) _ c a)) :=
            congrArg ψ ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsUnitHom_mul_ofPiece U c a)
        _ = ∑ d : AlgebraicGeometry.Scheme.weightedSymIndex r m,
              ψd (dv d) ((biproduct.π (fun d => term V d) d).app U
                (@HSMul.hSMul Γ(X, U) Γ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).part m, U) Γ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).part m, U) _ c a)) := hΨ m _
        _ = ∑ d : AlgebraicGeometry.Scheme.weightedSymIndex r m,
              c • ψd (dv d) ((biproduct.π (fun d => term V d) d).app U a) :=
            Finset.sum_congr rfl fun d _ =>
              (congrArg _ (Modules.Hom.app_smul (biproduct.π (fun d => term V d) d) c a)).trans (map_smul _ c _)
        _ = c • ∑ d : AlgebraicGeometry.Scheme.weightedSymIndex r m,
              ψd (dv d) ((biproduct.π (fun d => term V d) d).app U a) := (Finset.smul_sum).symm
        _ = c • ψ ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).ofPiece U m a) := congrArg _ (hΨ m a).symm
    | add x y hx hy =>
      obtain ⟨x, rfl⟩ : ∃ x' : (AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsRing U, x' = x := ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ : ∃ y' : (AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsRing U, y' = y := ⟨y, rfl⟩
      have h1 : ψ ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsUnitHom U c * (x + y)) =
          ψ ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsUnitHom U c * x) +
            ψ ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsUnitHom U c * y) :=
        (congrArg ψ (mul_add _ x y)).trans (map_add ψ _ _)
      have h2 : c • ψ (x + y) = c • ψ x + c • ψ y := (congrArg _ (map_add ψ x y)).trans (smul_add c _ _)
      exact h1.trans ((congrArg₂ (· + ·) hx hy).trans h2.symm)
  · have h := ofPiece_ι_weightedTensorPure U V (mkIndex d) w
    refine (congrArg ψ h.symm).trans ((hΨ (wdeg d) _).trans ?_)
    rw [Finset.sum_eq_single (mkIndex d)]
    · rw [Modules.biproduct_π_ι_self_app_apply]
      exact hψd d w
    · intro d' _ hd'
      rw [Modules.biproduct_π_ι_ne_app_apply _ _ (Ne.symm hd'), map_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

end weightedSymAlgebra

end AlgebraicGeometry.Scheme

end
