import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetWeightComponentEqCoefficient
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.JetProjectivizeSymCoeffAux
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.TruncationXiCoefficientCompat

/-! # All positive `ξ`-coefficients of `J^♯` vanish at `y` ⇒ all positive weight components vanish at `y`
(used for `BasedJet.normalizedTupleNowhereZero_of_unit_coefficient`; proof of Lemma 3.1 of
the paper).

Main theorem: `BasedJet.weightComponent_germ_mem_of_forall_pieceSection`. Route: the predicate `XiCoeffsVanishAt` ("all positive
`ξ`-coefficients vanish at `y`") is closed under `+` (linearity) and `*` (transfer to the truncated ring `𝒜(U')` on a frame
neighbourhood, module `…_WeightComponentVanish_TruncationCompat` + `…_NowhereZero_TruncatedVanishing`), contains
`p^♯ρ^♯ a` and `frameHom_{q+1}(t)` for `t` vanishing at `y`; the ring homomorphism `Φ = φ_J^♯ ∘ χ_U` from the chart ring
`J_κ(B_U, ε_U)` is evaluated on the generators (`chartEquiv_unitHom`, `jetPoint_appLE_jetCoordinate`) and `MvPolynomial.induction_on`
does the rest.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
  {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
  {L : LineBundle ρ.source.toVariety} {κ : ℕ}

/-- Membership transport along an equality (`rw` is unusable on these goals: the sheaf-of-modules section types are
not type-correct at reducible transparency). -/
private theorem mem_of_eq_of_mem {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {S : Submodule R M}
    {a b : M} (e : a = b) (hb : b ∈ S) : a ∈ S := e ▸ hb

/-- **All positive `ξ`-coefficients of `g ∈ Γ(Tot(L), p⁻¹V)` vanish at `y ∈ V`**: for every `1 ≤ m ≤ κ` the germ at
`y` of `symCoeffHom_m g` lies in `𝔪_y • ⊤`. The predicate `I` of step (4) of
`weightComponent_germ_mem_of_forall_pieceSection`. -/
def BasedJet.XiCoeffsVanishAt (L : LineBundle ρ.source.toVariety) (κ : ℕ) (V : ρ.source.toScheme.Opens)
    (y : ρ.source.toScheme) (hy : y ∈ V)
    (g : Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ κ →
    (AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.germ
        V y hy (((BasedJet.symCoeffHom L m).val.app (Opposite.op V)).hom g) ∈
      (IsLocalRing.maximalIdeal (ρ.source.toScheme.presheaf.stalk y)) •
        (⊤ : Submodule (ρ.source.toScheme.presheaf.stalk y)
          ((AlgebraicGeometry.Scheme.Modules.monoidalPow
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.stalk y))

/-- The vanishing criterion is the truncated-ring criterion `PositivePiecesVanishAt` of `trunc(g)|_{U'}`
(`positivePiecesVanishAt_sectionsRestrict_truncHom_iff`, module `…_TruncationCompat`). -/
theorem BasedJet.xiCoeffsVanishAt_iff_positivePiecesVanishAt (L : LineBundle ρ.source.toVariety) (κ : ℕ)
    {V U' : ρ.source.toScheme.Opens} (h : U' ≤ V) {y : ρ.source.toScheme} (hy : y ∈ U')
    (g : Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)) :
    BasedJet.XiCoeffsVanishAt L κ V y (h hy) g ↔
      truncatedJetAlgebra.PositivePiecesVanishAt L κ hy
        ((truncatedJetAlgebra L κ).sectionsRestrict h
          (show (truncatedJetAlgebra L κ).sectionsRing V from (truncatedJetAlgebra.truncHom L κ).app V g)) :=
  (truncatedJetAlgebra.positivePiecesVanishAt_sectionsRestrict_truncHom_iff L κ h hy g).symm

theorem BasedJet.XiCoeffsVanishAt.add {L : LineBundle ρ.source.toVariety} {κ : ℕ} {V : ρ.source.toScheme.Opens}
    {y : ρ.source.toScheme} {hy : y ∈ V}
    {g g' : Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)}
    (H : BasedJet.XiCoeffsVanishAt L κ V y hy g) (H' : BasedJet.XiCoeffsVanishAt L κ V y hy g') :
    BasedJet.XiCoeffsVanishAt L κ V y hy (g + g') := by
  intro m h1 hm
  exact mem_of_eq_of_mem
    ((congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.monoidalPow
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.germ V y hy z)
      (map_add ((BasedJet.symCoeffHom L m).val.app (Opposite.op V)).hom g g')).trans
      (map_add (CategoryTheory.ConcreteCategory.hom ((AlgebraicGeometry.Scheme.Modules.monoidalPow
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.germ V y hy)) _ _))
    (Submodule.add_mem _ (H m h1 hm) (H' m h1 hm))

/-- Products: transfer to the truncated ring on a frame neighbourhood `U' ∋ y` of `L^{-1}`
(`exists_frame_le`), where `PositivePiecesVanishAt` is multiplicative (`PositivePiecesVanishAt.mul`);
`trunc` and the restriction are ring homomorphisms (`truncHom_app_mul`, `sectionsRestrict`). -/
theorem BasedJet.XiCoeffsVanishAt.mul {L : LineBundle ρ.source.toVariety} {κ : ℕ} {V : ρ.source.toScheme.Opens}
    {y : ρ.source.toScheme} {hy : y ∈ V}
    {g g' : Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)}
    (H : BasedJet.XiCoeffsVanishAt L κ V y hy g) (H' : BasedJet.XiCoeffsVanishAt L κ V y hy g') :
    BasedJet.XiCoeffsVanishAt L κ V y hy (g * g') := by
  obtain ⟨U', hU'V, hyU', μ, hμ⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_frame_le (L.zpow (-1)).toModules hy
  have hH := (BasedJet.xiCoeffsVanishAt_iff_positivePiecesVanishAt L κ hU'V hyU' g).mp H
  have hH' := (BasedJet.xiCoeffsVanishAt_iff_positivePiecesVanishAt L κ hU'V hyU' g').mp H'
  refine (BasedJet.xiCoeffsVanishAt_iff_positivePiecesVanishAt L κ hU'V hyU' (g * g')).mpr ?_
  rw [truncatedJetAlgebra.truncHom_app_mul, map_mul]
  exact truncatedJetAlgebra.PositivePiecesVanishAt.mul L κ hyU' μ hμ hH hH'

/-- `frameHom_n t = t·ξ^n` has all positive `ξ`-coefficients vanishing at `y` as soon as `t` does
(`frameHom_symCoeffHom`: the `n`-th coefficient is `t`; `symCoeffHom_frameHom_app_of_ne`: the others are `0`). -/
theorem BasedJet.xiCoeffsVanishAt_frameHom_app (L : LineBundle ρ.source.toVariety) (κ : ℕ)
    (V : ρ.source.toScheme.Opens) (y : ρ.source.toScheme) (hy : y ∈ V) (n : ℕ)
    (t : ((AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
      n).val.obj (Opposite.op V) : Type u))
    (ht : (AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
        n).presheaf.germ V y hy t ∈
      (IsLocalRing.maximalIdeal (ρ.source.toScheme.presheaf.stalk y)) •
        (⊤ : Submodule (ρ.source.toScheme.presheaf.stalk y)
          ((AlgebraicGeometry.Scheme.Modules.monoidalPow
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules) n).presheaf.stalk y))) :
    BasedJet.XiCoeffsVanishAt L κ V y hy (((BasedJet.frameHom L n).val.app (Opposite.op V)).hom t) := by
  intro m h1 hm
  by_cases hmn : m = n
  · subst hmn
    have h3 : ((BasedJet.symCoeffHom L m).val.app (Opposite.op V)).hom
        (((BasedJet.frameHom L m).val.app (Opposite.op V)).hom t) = t :=
      congrArg (fun g : AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
          m ⟶ AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m =>
        (g.val.app (Opposite.op V)).hom t) (BasedJet.frameHom_symCoeffHom L m)
    exact mem_of_eq_of_mem (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.monoidalPow
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.germ V y hy z) h3) ht
  · exact mem_of_eq_of_mem
      ((congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.monoidalPow
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.germ V y hy z)
        (BasedJet.symCoeffHom_frameHom_app_of_ne L V hmn t)).trans (map_zero _))
      (Submodule.zero_mem _)

/-- Functions pulled back from `C̃` have no positive `ξ`-coefficients (`symCoeffHom_app_totalSpace_app_of_ne`). -/
theorem BasedJet.xiCoeffsVanishAt_totalSpace_hom_app (L : LineBundle ρ.source.toVariety) (κ : ℕ)
    (V : ρ.source.toScheme.Opens) (y : ρ.source.toScheme) (hy : y ∈ V) (a : Γ(ρ.source.toScheme, V)) :
    BasedJet.XiCoeffsVanishAt L κ V y hy (((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.app V).hom a) := by
  intro m h1 hm
  exact mem_of_eq_of_mem
    ((congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.monoidalPow
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.germ V y hy z)
      (BasedJet.symCoeffHom_app_totalSpace_app_of_ne L V a (Nat.pos_iff_ne_zero.mp h1))).trans (map_zero _))
    (Submodule.zero_mem _)

/-- `Φ := φ_J^♯ ∘ χ_U : J_κ(B_U, ε_U) → Γ(Tot(L), p⁻¹ρ⁻¹U)`, the ring homomorphism "pull back a function on the chart
`J_U = π_J⁻¹U` along the jet point `φ_J = J.jetPoint`" (`relativeJetScheme.chartEquiv` is the chart identification
`χ_U : J_κ(B_U, ε_U) ≃+* Γ(J_κ, π_J⁻¹U)`). -/
noncomputable def BasedJet.chartToTot (J : BasedJet f ρ L κ) (U : C.toScheme.AffineZariskiSite)
    (hle : (BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1 ≤ J.jetPoint.left ⁻¹ᵁ
      ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1)) :
    (jetGradedAffineAlgebra (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).toAffineAlgebra.sections U →+*
      Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U.1)) :=
  (J.jetPoint.left.appLE
      ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1)
      ((BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1) hle).hom.comp
    (relativeJetScheme.chartEquiv (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ U).toRingHom

/-- **Induction over the chart ring.** Under the hypothesis of `weightComponent_germ_mem_of_forall_pieceSection`
(all `J.pieceSection U n _ c`, `1 ≤ n ≤ κ`, vanish at `y`), every `z ∈ J_κ(B_U, ε_U)` has `Φ(z)` with all positive
`ξ`-coefficients vanishing at `y`: write `z = [P]` with `P ∈ Γ(U)[d_q b]` (`Ideal.Quotient.mk_surjective`) and induct
(`MvPolynomial.induction_on`): constants `C a ↦ p^♯ρ^♯a` (`chartEquiv_unitHom`, `symCoeffHom_jetPoint_app_of_ne`);
sums (`XiCoeffsVanishAt.add`); `P · X (q, b)` (`XiCoeffsVanishAt.mul`) with
`Φ(d_q b) = frameHom_{q+1} (J.pieceSection U (q+1) b)` (`coeffClass_succ`, `chartEquiv_eq_chartSections`,
`jetPoint_appLE_jetCoordinate`) whose only positive coefficient is the hypothesis (`xiCoeffsVanishAt_frameHom_app`). -/
theorem BasedJet.xiCoeffsVanishAt_chartToTot (J : BasedJet f ρ L κ) (y : ρ.source.toScheme)
    (U : C.toScheme.AffineZariskiSite) (hy : y ∈ ρ.hom ⁻¹ᵁ U.1)
    (h : ∀ (n : ℕ) (hn : n ≤ κ), 1 ≤ n → ∀ c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U.1),
      (AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) n).presheaf.germ
          (ρ.hom ⁻¹ᵁ U.1) y hy (J.pieceSection U.1 n hn c) ∈
        (IsLocalRing.maximalIdeal (ρ.source.toScheme.presheaf.stalk y)) •
          (⊤ : Submodule (ρ.source.toScheme.presheaf.stalk y)
            ((AlgebraicGeometry.Scheme.Modules.monoidalPow
              (AlgebraicGeometry.Scheme.Modules.dual L.toModules) n).presheaf.stalk y)))
    (hle : (BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1 ≤ J.jetPoint.left ⁻¹ᵁ
      ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1))
    (z : (jetGradedAffineAlgebra (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).toAffineAlgebra.sections U) :
    BasedJet.XiCoeffsVanishAt L κ (ρ.hom ⁻¹ᵁ U.1) y hy (J.chartToTot U hle z) := by
  let _ := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) U.1
  have hU := relativeJetScheme.preimage_eq_chartOpen (k := k) (MMSetup.cone f) (MMSetup.seed f).1
    (MMSetup.seed f).2 κ U
  obtain ⟨P, hP⟩ : ∃ P : MvPolynomial (Fin κ × Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U.1))
      Γ(C.toScheme, U.1),
      (Ideal.Quotient.mk (BasedJetAlgebra.relations
        (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ) P :
        BasedJetAlgebra (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ)
        = z :=
    Ideal.Quotient.mk_surjective z
  subst hP
  induction P using MvPolynomial.induction_on with
  | C a =>
    have e : (Ideal.Quotient.mk (BasedJetAlgebra.relations
        (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ)
        (MvPolynomial.C a) :
        BasedJetAlgebra (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ) =
        (jetGradedAffineAlgebra (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).toAffineAlgebra.unitHom U a :=
      rfl
    rw [e]
    intro m h1 hm
    have h0 := relativeJetScheme.chartEquiv_unitHom (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ U a
    have h2 := J.symCoeffHom_jetPoint_app_of_ne U.1 a hle (Nat.pos_iff_ne_zero.mp h1)
    show (AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.germ
        (ρ.hom ⁻¹ᵁ U.1) y hy (((BasedJet.symCoeffHom L m).val.app (Opposite.op (ρ.hom ⁻¹ᵁ U.1))).hom
          ((J.jetPoint.left.appLE
              ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1)
              ((BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1) hle).hom
            (relativeJetScheme.chartEquiv (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ U
              ((jetGradedAffineAlgebra (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).toAffineAlgebra.unitHom
                U a)))) ∈ _
    rw [h0, h2]
    exact mem_of_eq_of_mem (map_zero _) (Submodule.zero_mem _)
  | add p q hp hq =>
    have e : J.chartToTot U hle (Ideal.Quotient.mk _ (p + q)) =
        J.chartToTot U hle (Ideal.Quotient.mk _ p) + J.chartToTot U hle (Ideal.Quotient.mk _ q) :=
      (congrArg (J.chartToTot U hle) (map_add (Ideal.Quotient.mk _) p q)).trans (map_add (J.chartToTot U hle) _ _)
    exact (congrArg (BasedJet.XiCoeffsVanishAt L κ (ρ.hom ⁻¹ᵁ U.1) y hy) e).mpr (hp.add hq)
  | mul_X p n hp =>
    obtain ⟨q, b⟩ := n
    have e : J.chartToTot U hle (Ideal.Quotient.mk _ (p * MvPolynomial.X (q, b))) =
        J.chartToTot U hle (Ideal.Quotient.mk _ p) * J.chartToTot U hle (Ideal.Quotient.mk _ (MvPolynomial.X (q, b))) :=
      (congrArg (J.chartToTot U hle) (map_mul (Ideal.Quotient.mk _) p _)).trans (map_mul (J.chartToTot U hle) _ _)
    refine (congrArg (BasedJet.XiCoeffsVanishAt L κ (ρ.hom ⁻¹ᵁ U.1) y hy) e).mpr (hp.mul ?_)
    have h0 : (Ideal.Quotient.mk (BasedJetAlgebra.relations
        (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ)
        (MvPolynomial.X (q, b)) :
        BasedJetAlgebra (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ) =
        BasedJetAlgebra.coeffClass
          (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ ((q : ℕ) + 1) b :=
      (BasedJetAlgebra.coeffClass_succ _ κ (q : ℕ) q.2 b).symm
    have h1 := relativeJetScheme.chartEquiv_eq_chartSections (k := k) (MMSetup.cone f) (MMSetup.seed f).1
      (MMSetup.seed f).2 κ U hU
      (BasedJetAlgebra.coeffClass
        (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ ((q : ℕ) + 1) b)
    have h2 := J.jetPoint_appLE_jetCoordinate U q b hU hle
    have hΦ : J.chartToTot U hle (Ideal.Quotient.mk (BasedJetAlgebra.relations
        (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 U.1) κ)
        (MvPolynomial.X (q, b))) =
        ((BasedJet.frameHom L ((q : ℕ) + 1)).val.app (Opposite.op (ρ.hom ⁻¹ᵁ U.1))).hom
          (J.pieceSection U.1 ((q : ℕ) + 1) (Nat.succ_le_of_lt q.2) b) :=
      (congrArg (J.chartToTot U hle) h0).trans
        ((congrArg (fun w => (J.jetPoint.left.appLE
          ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1)
          ((BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1) hle).hom w) h1).trans h2)
    exact (congrArg (BasedJet.XiCoeffsVanishAt L κ (ρ.hom ⁻¹ᵁ U.1) y hy) hΦ).mpr
      (BasedJet.xiCoeffsVanishAt_frameHom_app L κ (ρ.hom ⁻¹ᵁ U.1) y hy ((q : ℕ) + 1) _
        (h ((q : ℕ) + 1) (Nat.succ_le_of_lt q.2) (Nat.succ_pos _) b))

/-- **All positive `ξ`-coefficients of `J^♯` vanish at `y` ⇒ all positive weight components vanish at `y`**
(proof of Lemma 3.1 of the paper). Let `U ⊆ C` be an affine open,
`y ∈ ρ⁻¹U`, and suppose that for every `c ∈ B_U = Γ(𝒵, π⁻¹U)` and every `1 ≤ n ≤ κ` the germ at `y` of
`J.pieceSection U n _ c` lies in `𝔪_y • ⊤`. Then for every `1 ≤ m ≤ κ` and every `x ∈ S_m(U)`
(`((jetAlgebra f κ).part m).val.obj (op U)`), the germ at `y` of `Ψ_m(x)` lies in `𝔪_y • ⊤`, where
`Ψ_m := (pullbackPushforwardAdjunction ρ.hom).homEquiv _ _ (J.weightComponent m) : S_m ⟶ ρ_*(L^∨)^{⊗m}`.

Natural-language proof.
(1) *Formula for `Ψ_m`.* `BasedJet.weightComponent_adj_app`: `Ψ_m(x) = symCoeffHom_m (φ^♯ (partι x))`,
where `φ = J.jetPoint : Tot(L) → J_κ` is the jet point of the universal frame (a morphism over `C`),
`φ^♯ = φ.left.appLE (π_J⁻¹U) (p⁻¹ρ⁻¹U) _ : Γ(J_κ, π_J⁻¹U) → Γ(Tot(L), p⁻¹ρ⁻¹U)` is a ring homomorphism,
and `symCoeffHom_m = structureIso⁻¹ ≫ totalProj m ≫ symPartToMonoidalPow` extracts the `ξ^m`-coefficient
(`Tot(L) = relativeSpec (Sym L^∨)`).
(2) *Generation of `Γ(J_κ, π_J⁻¹U)`.* The chart identification `χ_U = relativeJetScheme.chartEquiv U :
J_κ(B_U, ε_U) ≃+* Γ(J_κ, π_J⁻¹U)` is a ring isomorphism (it is `chartSections` transported along
`relativeJetScheme.preimage_eq_chartOpen`, `chartEquiv_eq_chartSections`), where
`J_κ(B_U, ε_U) = BasedJetAlgebra ε_U κ = MvPolynomial (Fin κ × B_U) Γ(U) ⧸ relations`. Hence every
`z ∈ Γ(J_κ, π_J⁻¹U)` is `χ_U (Ideal.Quotient.mk _ P)` for a polynomial `P` (`Ideal.Quotient.mk_surjective`), and
by `MvPolynomial.induction_on` it suffices to treat `P = C r`, `P + Q`, `P * X (q, b)`. Under `χ_U ∘ mk`, `C r` goes
to the structure map of `r ∈ Γ(U)` (`chartEquiv_unitHom`; `π_J^♯ r`), and `X (q, b)` to `χ_U (coeffClass ε_U κ (q+1) b)`
(`BasedJetAlgebra.coeffClass_succ`).
(3) *Values on generators.* `BasedJet.jetPoint_appLE_jetCoordinate`:
`φ^♯ (chartSections (coeffClass (q+1) b)) = frameHom_{q+1} (J.pieceSection U (q+1) _ b)` (the jet
coordinate `d_q b` pulls back to "`(q+1)`-st `ξ`-coefficient of `J^♯ b`" times `ξ^{q+1}`). Constants:
`φ^♯ (π_J^♯ r) = p^♯ ρ^♯ r` (`Over.w φ`; packaged as `symCoeffHom_jetPoint_app_of_ne`, `JetProjectivizeSymCoeffAux`).
(4) *The vanishing set is a subring.* Let
`I := {g ∈ Γ(Tot(L), p⁻¹ρ⁻¹U) | ∀ 1 ≤ m ≤ κ, germ_y (symCoeffHom_m g) ∈ 𝔪_y • ⊤}`.
  - Generators: `frameHom_n ≫ symCoeffHom_m` is the identity for `n = m` (`frameHom_symCoeffHom`) and `0`
    for `n ≠ m` (`frameHom_symCoeffHom_of_ne`); so `frameHom_{q+1}(t) ∈ I` whenever `germ_y t ∈ 𝔪_y • ⊤`
    (the germ of `0` lies in every submodule). With the hypothesis and (3), `φ^♯` of every jet coordinate
    lies in `I`.
  - Constants: `symCoeffHom_m (p^♯ s) = 0` for `m ≥ 1` (`symCoeffHom_app_totalSpace_app_of_ne`: `p^♯ s = s • 1` and
    `symCoeffHom_m 1 = 0`): constants lie in `I`.
  - Sums: `symCoeffHom_m` is additive.
  - Products: transfer to the truncated ring. `trunc := structureIso⁻¹` followed by
    `truncatedJetAlgebra.truncation L κ` (module `JetNeighborhoodToTotalSpace`) is a ring homomorphism
    `Γ(Tot(L), p⁻¹V) → (truncatedJetAlgebra L κ).sectionsRing V` (`structureIso_inv_app_mul`,
    `jetNeighborhood.truncation_structureHom_isAlgebraMap`, `totalMul_comp_truncation`), and for `m ≤ κ`
    `π_m ∘ trunc = pieceIso_m⁻¹ ∘ symCoeffHom_m` (`ι_truncation`: on the `m`-th summand the truncation is
    `symPartToMonoidalPow ≫ pieceIso⁻¹ ≫ biproduct.ι m`; `totalIncl_totalProj`, `biproduct.ι_π`,
    `total_sections_exists_finset_sum`; formalized as `truncatedJetAlgebra.truncHom_comp_π` in
    `…_WeightComponentVanish_TruncationCompat`, together with `truncHom_app_add/mul`). Hence `I` is the preimage under `trunc` of
    `T_V := {h ∈ sectionsRing V | ∀ 1 ≤ m ≤ κ, germ_y (π_m h) ∈ 𝔪_y • ⊤}` (the criterion is invariant under
    the isomorphism `pieceIso_m`, `germ_hom_app_mem_maximalIdeal_smul_iff_of_iso`), and `T_V` is a subring
    by the frame/polynomial argument of step (3) of `pieceSection_germ_mem_of_forall_isZeroAt`:
    restrict to `U' ∋ y` with a frame `μ` of `L^{-1}` (`germ_res_mem_maximalIdeal_smul_iff`), where
    `sectionsRing U' = O(U')[t]/(t^{κ+1})` (`polyToSections_surjective`, `π_polyToSections`,
    `framePow_isFrame`) and `Polynomial.coeff_mul` shows that the coefficient condition is multiplicative.
(5) By (2)–(4) and induction on `P`, `φ^♯ z ∈ I` for every `z ∈ Γ(J_κ, π_J⁻¹U)`; take `z = partι x` and
use (1) with `1 ≤ m ≤ κ`. ∎

Formalization: `I` is `BasedJet.XiCoeffsVanishAt`; step (4) is `XiCoeffsVanishAt.add/.mul`, `xiCoeffsVanishAt_frameHom_app`,
`xiCoeffsVanishAt_totalSpace_hom_app`, the transfer being `xiCoeffsVanishAt_iff_positivePiecesVanishAt`
(`positivePiecesVanishAt_sectionsRestrict_truncHom_iff`, module `…_TruncationCompat`; the subring property of `T_V` is
`PositivePiecesVanishAt.add/.mul` of `…_NowhereZero_TruncatedVanishing`); steps (2)–(3) and (5) are
`BasedJet.chartToTot` (`Φ = φ^♯ ∘ χ_U`) and `BasedJet.xiCoeffsVanishAt_chartToTot` (the induction, using the ring
equivalence `relativeJetScheme.chartEquiv` and the constants/off-degree lemmas `symCoeffHom_jetPoint_app_of_ne`,
`symCoeffHom_frameHom_app_of_ne`).

Edge cases: `m ≤ κ` is needed by the truncation route (for `m > κ` the statement is still true but needs the
polynomial model of `Γ(Tot(L), p⁻¹U')`); `m ≥ 1` is necessary (`Ψ_0` of a constant is a unit); `κ = 0`
is vacuous; `U = ⊥` is excluded by `y ∈ ρ⁻¹U`. -/
theorem BasedJet.weightComponent_germ_mem_of_forall_pieceSection (J : BasedJet f ρ L κ) (y : ρ.source.toScheme)
    (U : C.toScheme.AffineZariskiSite) (hy : y ∈ ρ.hom ⁻¹ᵁ U.1)
    (h : ∀ (n : ℕ) (hn : n ≤ κ), 1 ≤ n → ∀ c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U.1),
      (AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) n).presheaf.germ
          (ρ.hom ⁻¹ᵁ U.1) y hy (J.pieceSection U.1 n hn c) ∈
        (IsLocalRing.maximalIdeal (ρ.source.toScheme.presheaf.stalk y)) •
          (⊤ : Submodule (ρ.source.toScheme.presheaf.stalk y)
            ((AlgebraicGeometry.Scheme.Modules.monoidalPow
              (AlgebraicGeometry.Scheme.Modules.dual L.toModules) n).presheaf.stalk y)))
    (m : ℕ) (h1 : 1 ≤ m) (hm : m ≤ κ)
    (x : (((jetAlgebra f κ).part m).val.obj (Opposite.op U.1) : Type u)) :
    (AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.germ
        (ρ.hom ⁻¹ᵁ U.1) y hy
        (show ((AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
            m).val.obj (Opposite.op (ρ.hom ⁻¹ᵁ U.1)) : Type u) from
          ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).homEquiv _ _)
            (J.weightComponent m)).val.app (Opposite.op U.1)).hom x) ∈
      (IsLocalRing.maximalIdeal (ρ.source.toScheme.presheaf.stalk y)) •
        (⊤ : Submodule (ρ.source.toScheme.presheaf.stalk y)
          ((AlgebraicGeometry.Scheme.Modules.monoidalPow
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.stalk y)) := by
  have hle : (BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1 ≤ J.jetPoint.left ⁻¹ᵁ
      ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1) := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, CategoryTheory.Over.w]
  rw [J.weightComponent_adj_app m U.1 x hle]
  obtain ⟨z, hz⟩ := (relativeJetScheme.chartEquiv (k := k) (MMSetup.cone f) (MMSetup.seed f).1
    (MMSetup.seed f).2 κ U).surjective
    (show Γ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left,
        (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1) from
      ((BasedJet.partι f κ m).val.app (Opposite.op U.1)).hom x)
  have H := J.xiCoeffsVanishAt_chartToTot y U hy h hle z m h1 hm
  show (AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.germ
      (ρ.hom ⁻¹ᵁ U.1) y hy (((BasedJet.symCoeffHom L m).val.app (Opposite.op (ρ.hom ⁻¹ᵁ U.1))).hom
        ((J.jetPoint.left.appLE
            ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1)
            ((BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1) hle).hom
          (((BasedJet.partι f κ m).val.app (Opposite.op U.1)).hom x))) ∈ _
  exact mem_of_eq_of_mem (congrArg (fun w => (AlgebraicGeometry.Scheme.Modules.monoidalPow
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.germ (ρ.hom ⁻¹ᵁ U.1) y hy
      (((BasedJet.symCoeffHom L m).val.app (Opposite.op (ρ.hom ⁻¹ᵁ U.1))).hom
        ((J.jetPoint.left.appLE
            ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ U.1)
            ((BasedJet.totOver ρ L).hom ⁻¹ᵁ U.1) hle).hom w))) hz.symm) H

end
