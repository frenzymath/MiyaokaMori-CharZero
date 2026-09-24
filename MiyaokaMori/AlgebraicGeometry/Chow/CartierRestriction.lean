import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.ChowGroupRatCongr
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforwardScheme
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Chow.CapCommutes
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupRational
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.ProjectionFormula
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveDivisor
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02r5
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02t9
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.Stacks02or
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOpSpanCommute
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.CapListPerm
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suClosedImmersion

/-! # Repeated Cartier restriction

Repeated Cartier restriction (Fulton, Intersection Theory, Chapter 2): the successive caps with a
finite family of effective Cartier divisors are independent of the order (commutativity gives
associativity), and the product vanishes when the intersection of the supports of all the zero
schemes is empty (proof of Proposition 2.4 of the paper). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- `capProd_comm` is assembled from two purely algebraic/combinatorial lemmas; the only geometric input
   is the commutativity of caps (`firstChernClass_comm`). -/

/-- Composition of two index transports. -/
theorem AlgebraicGeometry.ChowGroupRat.congr_comp_congr (X : AlgebraicGeometry.Scheme.{u}) {p q r : ℕ}
    (h : p = q) (h' : q = r) :
    (AlgebraicGeometry.ChowGroupRat.congr X h').comp (AlgebraicGeometry.ChowGroupRat.congr X h)
      = AlgebraicGeometry.ChowGroupRat.congr X (h.trans h') := by
  subst h; subst h'; rfl

theorem AlgebraicGeometry.RatDivisorOp.capProd_comm {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ι → AlgebraicGeometry.RatDivisorOp X)
    (hD : ∀ j, D j ∈ Submodule.span ℚ {D' : AlgebraicGeometry.RatDivisorOp X |
        ∃ (L : X.Modules) (_ : L.IsLineBundle), D' = AlgebraicGeometry.ratDivisorOpOfLineBundle L})
    (e : Equiv.Perm ι) (d : ℕ) :
    AlgebraicGeometry.RatDivisorOp.capProd (D ∘ e) d
      = (AlgebraicGeometry.RatDivisorOp.capProd D d).comp
          (AlgebraicGeometry.ChowGroupRat.congr X (by simp)) := by
  have hperm : ((Finset.univ : Finset ι).toList.map (D ∘ e)).Perm
      ((Finset.univ : Finset ι).toList.map D) := by
    rw [← List.map_map]
    refine List.Perm.map D ?_
    refine (List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).map e.injective)
      (Finset.nodup_toList _)).mpr fun a => ?_
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, iff_true]
    exact ⟨e.symm a, e.apply_symm_apply a⟩
  have hc : ∀ A ∈ (Finset.univ : Finset ι).toList.map (D ∘ e),
      ∀ B ∈ (Finset.univ : Finset ι).toList.map (D ∘ e), ∀ d : ℕ,
        (A d).comp (B (d + 1)) = (B d).comp (A (d + 1)) := by
    intro A hA B hB d
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hA
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hB
    exact AlgebraicGeometry.RatDivisorOp.comp_comm_of_mem_span (k := k) _ _ (hD _) (hD _) d
  unfold AlgebraicGeometry.RatDivisorOp.capProd
  rw [AlgebraicGeometry.RatDivisorOp.capList_perm hperm hc d, LinearMap.comp_assoc,
    LinearMap.comp_assoc, AlgebraicGeometry.ChowGroupRat.congr_comp_congr,
    AlgebraicGeometry.ChowGroupRat.congr_comp_congr]

theorem AlgebraicGeometry.RatDivisorOp.capProd_eq_zero_of_iInter_support_empty
    {X : AlgebraicGeometry.Scheme.{u}} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (L : ι → X.Modules) [∀ j, (L j).IsLineBundle]
    (σ : ∀ j, ((L j).val.obj (Opposite.op ⊤) : Type u))
    (h : (⋂ j, (AlgebraicGeometry.Scheme.idealSheafOfSection (L j) (σ j)).support)
        = (∅ : Set X))
    (d : ℕ) :
    AlgebraicGeometry.RatDivisorOp.capProd
        (fun j => AlgebraicGeometry.ratDivisorOpOfLineBundle (L j)) d = 0 := by
  classical
  have chowPushforward_comp_aux {k : Type u} [Field k]
      {X Y Z : AlgebraicGeometry.Scheme.{u}}
      [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [AlgebraicGeometry.LocallyOfFiniteType
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
      [AlgebraicGeometry.LocallyOfFiniteType
        (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
      [AlgebraicGeometry.LocallyOfFiniteType
        (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [AlgebraicGeometry.IsProper f] [AlgebraicGeometry.IsProper g]
      [AlgebraicGeometry.IsClosedImmersion f] [AlgebraicGeometry.IsClosedImmersion g] (d : ℕ) :
      (AlgebraicGeometry.chowPushforward g d).comp
          (AlgebraicGeometry.chowPushforward f d) =
        AlgebraicGeometry.chowPushforward (f ≫ g) d := by
    -- the closed-immersion case of Stacks 02S2
    have hf : AlgebraicGeometry.PushforwardDescends f d :=
      AlgebraicGeometry.pushforwardDescends_of_isClosedImmersion f d
    have hg : AlgebraicGeometry.PushforwardDescends g d :=
      AlgebraicGeometry.pushforwardDescends_of_isClosedImmersion g d
    have hfg : AlgebraicGeometry.PushforwardDescends (f ≫ g) d :=
      AlgebraicGeometry.pushforwardDescends_of_isClosedImmersion (f ≫ g) d
    ext α
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective α
    have hpush_f :
        AlgebraicGeometry.chowPushforward f d (AlgebraicGeometry.ChowGroup.mk a) =
          AlgebraicGeometry.ChowGroup.mk
            ⟨AlgebraicGeometry.AlgebraicCycle.properPushforward f a,
              AlgebraicGeometry.properPushforward_mem_cycleSubgroup f d hf a⟩ := by
      have hp : AlgebraicGeometry.chowPushforward f d =
          QuotientAddGroup.map _ _
            (AlgebraicGeometry.cyclePushforwardHom f d hf)
            (AlgebraicGeometry.cyclePushforwardHom_rel f d hf) := by
        unfold AlgebraicGeometry.chowPushforward
        exact dif_pos hf
      rw [hp]
      rfl
    have hpush_g : ∀ b,
        AlgebraicGeometry.chowPushforward g d (AlgebraicGeometry.ChowGroup.mk b) =
          AlgebraicGeometry.ChowGroup.mk
            ⟨AlgebraicGeometry.AlgebraicCycle.properPushforward g b,
              AlgebraicGeometry.properPushforward_mem_cycleSubgroup g d hg b⟩ := by
      intro b
      have hp : AlgebraicGeometry.chowPushforward g d =
          QuotientAddGroup.map _ _
            (AlgebraicGeometry.cyclePushforwardHom g d hg)
            (AlgebraicGeometry.cyclePushforwardHom_rel g d hg) := by
        unfold AlgebraicGeometry.chowPushforward
        exact dif_pos hg
      rw [hp]
      rfl
    have hpush_fg :
        AlgebraicGeometry.chowPushforward (f ≫ g) d (AlgebraicGeometry.ChowGroup.mk a) =
          AlgebraicGeometry.ChowGroup.mk
            ⟨AlgebraicGeometry.AlgebraicCycle.properPushforward (f ≫ g) a,
              AlgebraicGeometry.properPushforward_mem_cycleSubgroup (f ≫ g) d hfg a⟩ := by
      have hp : AlgebraicGeometry.chowPushforward (f ≫ g) d =
          QuotientAddGroup.map _ _
            (AlgebraicGeometry.cyclePushforwardHom (f ≫ g) d hfg)
            (AlgebraicGeometry.cyclePushforwardHom_rel (f ≫ g) d hfg) := by
        unfold AlgebraicGeometry.chowPushforward
        exact dif_pos hfg
      rw [hp]
      rfl
    change AlgebraicGeometry.chowPushforward g d
        (AlgebraicGeometry.chowPushforward f d (AlgebraicGeometry.ChowGroup.mk a)) =
      AlgebraicGeometry.chowPushforward (f ≫ g) d (AlgebraicGeometry.ChowGroup.mk a)
    rw [hpush_f, hpush_g, hpush_fg]
    congr 1
    apply Subtype.ext
    exact AlgebraicGeometry.AlgebraicCycle.properPushforward_comp f g a

  have chowPushforwardRat_comp_aux {k : Type u} [Field k]
      {X Y Z : AlgebraicGeometry.Scheme.{u}}
      [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [AlgebraicGeometry.LocallyOfFiniteType
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
      [AlgebraicGeometry.LocallyOfFiniteType
        (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
      [AlgebraicGeometry.LocallyOfFiniteType
        (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [AlgebraicGeometry.IsProper f] [AlgebraicGeometry.IsProper g]
      [AlgebraicGeometry.IsClosedImmersion f] [AlgebraicGeometry.IsClosedImmersion g] (d : ℕ) :
      (AlgebraicGeometry.chowPushforwardRat g d).comp
          (AlgebraicGeometry.chowPushforwardRat f d) =
        AlgebraicGeometry.chowPushforwardRat (f ≫ g) d := by
    apply LinearMap.ext
    intro α
    change (AlgebraicGeometry.chowPushforward g d).ratExtend
        ((AlgebraicGeometry.chowPushforward f d).ratExtend α) =
      (AlgebraicGeometry.chowPushforward (f ≫ g) d).ratExtend α
    induction α using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul q a =>
        unfold AddMonoidHom.ratExtend
        rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
          LinearMap.baseChange_tmul]
        congr 1
        change AlgebraicGeometry.chowPushforward g d
            (AlgebraicGeometry.chowPushforward f d a) =
          AlgebraicGeometry.chowPushforward (f ≫ g) d a
        exact DFunLike.congr_fun (chowPushforward_comp_aux (k := k) f g d) a
    | add α β hα hβ => rw [map_add, map_add, map_add, hα, hβ]

  have chowPushforwardRat_firstChernClass_pullback {k : Type u} [Field k]
      {X Y : AlgebraicGeometry.Scheme.{u}}
      [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [AlgebraicGeometry.LocallyOfFiniteType
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
      [AlgebraicGeometry.LocallyOfFiniteType
        (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
      (p : X ⟶ Y) [p.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [AlgebraicGeometry.IsProper p] [AlgebraicGeometry.IsClosedImmersion p]
      (L : Y.Modules) [L.IsLineBundle] (d : ℕ) :
      (AlgebraicGeometry.chowPushforwardRat p d).comp
          (AlgebraicGeometry.firstChernClass
            ((AlgebraicGeometry.Scheme.Modules.pullback p).obj L) (d + 1)).ratExtend =
        (AlgebraicGeometry.firstChernClass L (d + 1)).ratExtend.comp
          (AlgebraicGeometry.chowPushforwardRat p (d + 1)) := by
    have hproj :
        (AlgebraicGeometry.chowPushforward p d).comp
            (AlgebraicGeometry.firstChernClass
              ((AlgebraicGeometry.Scheme.Modules.pullback p).obj L) (d + 1)) =
          (AlgebraicGeometry.firstChernClass L (d + 1)).comp
            (AlgebraicGeometry.chowPushforward p (d + 1)) := by
      ext α
      exact AlgebraicGeometry.chowPushforward_firstChernClass_pullback_of_isClosedImmersion
        (k := k) p L d α
    apply LinearMap.ext
    intro α
    change (AlgebraicGeometry.chowPushforward p d).ratExtend
        ((AlgebraicGeometry.firstChernClass
          ((AlgebraicGeometry.Scheme.Modules.pullback p).obj L) (d + 1)).ratExtend α) =
      (AlgebraicGeometry.firstChernClass L (d + 1)).ratExtend
        ((AlgebraicGeometry.chowPushforward p (d + 1)).ratExtend α)
    induction α using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | tmul q a =>
        unfold AddMonoidHom.ratExtend
        rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
          LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
        congr 1
        change AlgebraicGeometry.chowPushforward p d
            (AlgebraicGeometry.firstChernClass
              ((AlgebraicGeometry.Scheme.Modules.pullback p).obj L) (d + 1) a) =
          AlgebraicGeometry.firstChernClass L (d + 1)
            (AlgebraicGeometry.chowPushforward p (d + 1) a)
        exact DFunLike.congr_fun hproj a
    | add α β hα hβ => rw [map_add, map_add, map_add, map_add, hα, hβ]

  have firstChernClassRat_mem_range_zeroScheme {k : Type u} [Field k]
      {X : AlgebraicGeometry.Scheme.{u}}
      [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [AlgebraicGeometry.LocallyOfFiniteType
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
      (L : X.Modules) [L.IsLineBundle]
      (s : (L.val.obj (Opposite.op ⊤) : Type u)) (d : ℕ)
      (α : AlgebraicGeometry.ChowGroupRat X (d + 1)) :
      ∃ γ : AlgebraicGeometry.ChowGroupRat
          (AlgebraicGeometry.Scheme.idealSheafOfSection L s).subscheme d,
        AlgebraicGeometry.chowPushforwardRat
            (AlgebraicGeometry.Scheme.idealSheafOfSection L s).subschemeι d γ =
          (AlgebraicGeometry.firstChernClass L (d + 1)).ratExtend α := by
    induction α using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero]; rfl⟩
    | tmul q a =>
        obtain ⟨γ, hγ⟩ :=
          AlgebraicGeometry.firstChernClass_mem_range_zeroScheme (k := k) L s d a
        refine ⟨q ⊗ₜ[ℤ] γ, ?_⟩
        change (AlgebraicGeometry.chowPushforward
            (AlgebraicGeometry.Scheme.idealSheafOfSection L s).subschemeι d).ratExtend
              (q ⊗ₜ[ℤ] γ) =
          (AlgebraicGeometry.firstChernClass L (d + 1)).ratExtend (q ⊗ₜ[ℤ] a)
        unfold AddMonoidHom.ratExtend
        rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
        congr 1
    | add α β hα hβ =>
        obtain ⟨γ, hγ⟩ := hα
        obtain ⟨δ, hδ⟩ := hβ
        refine ⟨γ + δ, ?_⟩
        rw [map_add, map_add, hγ, hδ]
        rfl

  have chowGroupRat_eq_zero_of_isEmpty {Y : AlgebraicGeometry.Scheme.{u}}
      [IsEmpty Y] (d : ℕ) (α : AlgebraicGeometry.ChowGroupRat Y d) : α = 0 := by
    induction α using TensorProduct.induction_on with
    | zero => rfl
    | tmul q a =>
        have ha : a = 0 := by
          induction a using QuotientAddGroup.induction_on with
          | _ a =>
              rw [show a = 0 from Subtype.ext (by ext y; exact isEmptyElim y)]
              rfl
        rw [ha, TensorProduct.tmul_zero]
        rfl
    | add α β hα hβ => rw [hα, hβ]; rfl

  have capList_chowPushforwardRat_eq_zero {k : Type u} [Field k]
      {Y : AlgebraicGeometry.Scheme.{u}}
      [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [AlgebraicGeometry.LocallyOfFiniteType
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
      [AlgebraicGeometry.LocallyOfFiniteType
        (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
      (p : Y ⟶ X) [p.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [AlgebraicGeometry.IsProper p] [AlgebraicGeometry.IsClosedImmersion p]
      (l : List ι)
      (h : p.base ⁻¹' (⋂ j ∈ (l.toFinset : Set ι),
          (AlgebraicGeometry.Scheme.idealSheafOfSection (L j) (σ j)).support) = ∅)
      (d : ℕ) :
        (AlgebraicGeometry.RatDivisorOp.capList
          (l.map (fun j ↦ AlgebraicGeometry.ratDivisorOpOfLineBundle (L j))) d).comp
        (AlgebraicGeometry.chowPushforwardRat p
          (d + (l.map (fun j ↦ AlgebraicGeometry.ratDivisorOpOfLineBundle (L j))).length)) = 0 := by
    induction l generalizing Y d with
    | nil =>
        have hempty : IsEmpty Y := ⟨fun y ↦ by
          have hy : y ∈ p.base ⁻¹' (⋂ j ∈ (([] : List ι).toFinset : Set ι),
              (AlgebraicGeometry.Scheme.idealSheafOfSection (L j) (σ j)).support) := by
            simp
          rw [h] at hy
          exact hy⟩
        let _ := hempty
        apply LinearMap.ext
        intro α
        change AlgebraicGeometry.chowPushforwardRat p d α = 0
        rw [chowGroupRat_eq_zero_of_isEmpty d α, map_zero]
    | cons j l ih =>
        let M := (AlgebraicGeometry.Scheme.Modules.pullback p).obj (L j)
        let s := sectionPullbackAlong p (σ j)
        let I := AlgebraicGeometry.Scheme.idealSheafOfSection M s
        let _ : I.subscheme.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
          ⟨I.subschemeι ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
        let _ : I.subschemeι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
        have : AlgebraicGeometry.LocallyOfFiniteType
            (I.subscheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
          inferInstanceAs (AlgebraicGeometry.LocallyOfFiniteType
            (I.subschemeι ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
        have hi :
            (I.subschemeι ≫ p).base ⁻¹' (⋂ a ∈ (l.toFinset : Set ι),
                (AlgebraicGeometry.Scheme.idealSheafOfSection (L a) (σ a)).support) = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro z hz
          have hzhead : p.base (I.subschemeι.base z) ∈
              (AlgebraicGeometry.Scheme.idealSheafOfSection (L j) (σ j)).support := by
            have hzrange : I.subschemeι.base z ∈ Set.range I.subschemeι.base := ⟨z, rfl⟩
            rw [I.range_subschemeι] at hzrange
            have hI : I =
                (AlgebraicGeometry.Scheme.idealSheafOfSection (L j) (σ j)).comap p := by
              dsimp [I, M, s]
              exact AlgebraicGeometry.Scheme.zeroScheme_pullback p (L j) (σ j)
            have hsupport : I.support =
                (AlgebraicGeometry.Scheme.idealSheafOfSection
                  (L j) (σ j)).support.preimage p.continuous := by
              rw [hI, AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
            rw [hsupport] at hzrange
            exact hzrange
          have hztail : ∀ a, a ∈ l → p.base (I.subschemeι.base z) ∈
              (AlgebraicGeometry.Scheme.idealSheafOfSection (L a) (σ a)).support := by
            intro a ha
            have hz' : (I.subschemeι ≫ p).base z ∈
                (AlgebraicGeometry.Scheme.idealSheafOfSection (L a) (σ a)).support :=
              Set.mem_iInter₂.mp hz a (by simpa using ha)
            exact hz'
          have hzall : I.subschemeι.base z ∈ p.base ⁻¹'
              (⋂ a ∈ ((j :: l).toFinset : Set ι),
                (AlgebraicGeometry.Scheme.idealSheafOfSection (L a) (σ a)).support) := by
            rw [Set.mem_preimage]
            refine Set.mem_iInter₂.mpr fun a ha ↦ ?_
            have ha' : a = j ∨ a ∈ l := by simpa using ha
            rcases ha' with (rfl | ha)
            · exact hzhead
            · exact hztail a ha
          rw [h] at hzall
          exact hzall
        have hrec := ih (Y := I.subscheme) (p := I.subschemeι ≫ p) hi d
        apply LinearMap.ext
        intro α
        change AlgebraicGeometry.RatDivisorOp.capList
            (l.map (fun a ↦ AlgebraicGeometry.ratDivisorOpOfLineBundle (L a))) d
            ((AlgebraicGeometry.firstChernClass
                (L j) (d + (l.map (fun a ↦
                  AlgebraicGeometry.ratDivisorOpOfLineBundle (L a))).length + 1)).ratExtend
              (AlgebraicGeometry.chowPushforwardRat p
                (d + (l.map (fun a ↦
                  AlgebraicGeometry.ratDivisorOpOfLineBundle (L a))).length + 1) α)) = 0
        have hproj := DFunLike.congr_fun
          (chowPushforwardRat_firstChernClass_pullback (k := k) p (L j)
            (d + (l.map (fun a ↦
              AlgebraicGeometry.ratDivisorOpOfLineBundle (L a))).length)) α
        change AlgebraicGeometry.chowPushforwardRat p
            (d + (l.map (fun a ↦
              AlgebraicGeometry.ratDivisorOpOfLineBundle (L a))).length)
            ((AlgebraicGeometry.firstChernClass
              ((AlgebraicGeometry.Scheme.Modules.pullback p).obj (L j))
                (d + (l.map (fun a ↦
                  AlgebraicGeometry.ratDivisorOpOfLineBundle (L a))).length + 1)).ratExtend α) =
          (AlgebraicGeometry.firstChernClass (L j)
              (d + (l.map (fun a ↦
                AlgebraicGeometry.ratDivisorOpOfLineBundle (L a))).length + 1)).ratExtend
            (AlgebraicGeometry.chowPushforwardRat p
              (d + (l.map (fun a ↦
                AlgebraicGeometry.ratDivisorOpOfLineBundle (L a))).length + 1) α) at hproj
        rw [← hproj]
        obtain ⟨γ, hγ⟩ := firstChernClassRat_mem_range_zeroScheme
          (k := k) M s
            (d + (l.map (fun a ↦
              AlgebraicGeometry.ratDivisorOpOfLineBundle (L a))).length) α
        rw [← hγ]
        have hcomp := DFunLike.congr_fun
          (chowPushforwardRat_comp_aux (k := k) I.subschemeι p
            (d + (l.map (fun a ↦
              AlgebraicGeometry.ratDivisorOpOfLineBundle (L a))).length)) γ
        change AlgebraicGeometry.chowPushforwardRat p
            (d + (l.map (fun a ↦
              AlgebraicGeometry.ratDivisorOpOfLineBundle (L a))).length)
            (AlgebraicGeometry.chowPushforwardRat I.subschemeι
              (d + (l.map (fun a ↦
                AlgebraicGeometry.ratDivisorOpOfLineBundle (L a))).length) γ) =
          AlgebraicGeometry.chowPushforwardRat (I.subschemeι ≫ p)
            (d + (l.map (fun a ↦
              AlgebraicGeometry.ratDivisorOpOfLineBundle (L a))).length) γ at hcomp
        rw [hcomp]
        exact DFunLike.congr_fun hrec γ

  have ratExtend_zero_aux {M N : Type u} [AddCommGroup M] [AddCommGroup N] :
      (0 : M →+ N).ratExtend = 0 := by
    unfold AddMonoidHom.ratExtend
    rw [show (0 : M →+ N).toIntLinearMap = 0 by rfl, LinearMap.baseChange_zero]

  have chowPushforward_id_aux {k : Type u} [Field k]
      {X : AlgebraicGeometry.Scheme.{u}}
      [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [AlgebraicGeometry.LocallyOfFiniteType
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))] (d : ℕ) :
      AlgebraicGeometry.chowPushforward (𝟙 X) d = AddMonoidHom.id _ := by
    have hid : AlgebraicGeometry.PushforwardDescends (𝟙 X) d :=
      AlgebraicGeometry.pushforwardDescends_of_isClosedImmersion (𝟙 X) d
    ext α
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective α
    have hpush : AlgebraicGeometry.chowPushforward (𝟙 X) d
        (AlgebraicGeometry.ChowGroup.mk a) =
        AlgebraicGeometry.ChowGroup.mk
          ⟨AlgebraicGeometry.AlgebraicCycle.properPushforward (𝟙 X) a,
            AlgebraicGeometry.properPushforward_mem_cycleSubgroup (𝟙 X) d hid a⟩ := by
      have hp : AlgebraicGeometry.chowPushforward (𝟙 X) d =
          QuotientAddGroup.map _ _
            (AlgebraicGeometry.cyclePushforwardHom (𝟙 X) d hid)
            (AlgebraicGeometry.cyclePushforwardHom_rel (𝟙 X) d hid) := by
        unfold AlgebraicGeometry.chowPushforward
        exact dif_pos hid
      rw [hp]
      rfl
    change AlgebraicGeometry.chowPushforward (𝟙 X) d
        (AlgebraicGeometry.ChowGroup.mk a) =
      AddMonoidHom.id (AlgebraicGeometry.ChowGroup X d) (AlgebraicGeometry.ChowGroup.mk a)
    rw [hpush]
    change AlgebraicGeometry.ChowGroup.mk _ = AlgebraicGeometry.ChowGroup.mk a
    congr 1
    apply Subtype.ext
    exact AlgebraicGeometry.AlgebraicCycle.map_id Order.height a.1

  have chowPushforwardRat_id_aux {k : Type u} [Field k]
      {X : AlgebraicGeometry.Scheme.{u}}
      [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
      [AlgebraicGeometry.LocallyOfFiniteType
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))] (d : ℕ) :
      AlgebraicGeometry.chowPushforwardRat (𝟙 X) d = LinearMap.id := by
    unfold AlgebraicGeometry.chowPushforwardRat
    rw [chowPushforward_id_aux (k := k)]
    apply LinearMap.ext
    intro α
    change (AddMonoidHom.id (AlgebraicGeometry.ChowGroup X d)).ratExtend α = α
    induction α using TensorProduct.induction_on with
    | zero => rw [map_zero]
    | tmul q a =>
        unfold AddMonoidHom.ratExtend
        rw [LinearMap.baseChange_tmul]
        rfl
    | add α β hα hβ => rw [map_add, hα, hβ]

  by_cases hX : ∃ (_ : AlgebraicGeometry.IsLocallyNoetherian X),
      X.IsLocallyOfFiniteTypeOverField
  · obtain ⟨hLN, hfield⟩ := hX
    obtain ⟨k, hk, π, hπ⟩ := hfield
    let _ : Field k := hk
    let _ : AlgebraicGeometry.IsLocallyNoetherian X := hLN
    let _ : X.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨π⟩
    have : AlgebraicGeometry.LocallyOfFiniteType
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hπ
    let l := (Finset.univ : Finset ι).toList
    have hl : (𝟙 X : X ⟶ X).base ⁻¹' (⋂ j ∈ (l.toFinset : Set ι),
        (AlgebraicGeometry.Scheme.idealSheafOfSection (L j) (σ j)).support) = ∅ := by
      simpa [l] using h
    have hrec := capList_chowPushforwardRat_eq_zero (k := k) (p := 𝟙 X) l hl d
    rw [chowPushforwardRat_id_aux (k := k), LinearMap.comp_id] at hrec
    unfold AlgebraicGeometry.RatDivisorOp.capProd
    change (AlgebraicGeometry.RatDivisorOp.capList
      (l.map (fun j ↦ AlgebraicGeometry.ratDivisorOpOfLineBundle (L j))) d).comp
        (AlgebraicGeometry.ChowGroupRat.congr X _) = 0
    rw [hrec, LinearMap.zero_comp]
  · have hz : ∀ j n, AlgebraicGeometry.ratDivisorOpOfLineBundle (L j) n = 0 := by
      intro j n
      unfold AlgebraicGeometry.ratDivisorOpOfLineBundle
      rw [AlgebraicGeometry.firstChernClass_eq_zero_of_not (L j) (n + 1) hX]
      exact ratExtend_zero_aux
    let j₀ : ι := Classical.choice (inferInstance : Nonempty ι)
    have hj₀ : j₀ ∈ (Finset.univ : Finset ι).toList := by simp
    have hne : (Finset.univ : Finset ι).toList ≠ [] := by
      intro he
      rw [he] at hj₀
      simp at hj₀
    have hcapList : ∀ (l : List ι), l ≠ [] →
        AlgebraicGeometry.RatDivisorOp.capList
          (l.map (fun j ↦ AlgebraicGeometry.ratDivisorOpOfLineBundle (L j))) d = 0 := by
      intro l hl
      cases l with
      | nil => exact (hl rfl).elim
      | cons j l =>
          change (AlgebraicGeometry.RatDivisorOp.capList
            (l.map (fun a ↦ AlgebraicGeometry.ratDivisorOpOfLineBundle (L a))) d).comp
              (AlgebraicGeometry.ratDivisorOpOfLineBundle (L j)
                (d + (l.map (fun a ↦
                  AlgebraicGeometry.ratDivisorOpOfLineBundle (L a))).length)) = 0
          rw [hz j, LinearMap.comp_zero]
    have hcap := hcapList (Finset.univ : Finset ι).toList hne
    unfold AlgebraicGeometry.RatDivisorOp.capProd
    rw [hcap, LinearMap.zero_comp]

end
