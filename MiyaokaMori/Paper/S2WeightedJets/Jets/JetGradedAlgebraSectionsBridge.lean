import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetRescalingChart
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.OfGradedQCAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetAlgebraSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecSections
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetSpecIso
import MiyaokaMori.AlgebraicGeometry.Morphisms.GmLaurentIndependence

/-! # The two gradings of the jet algebra agree on affine charts

**Statement.** On every affine open `U ⊆ C`, the sections ring of the *geometric* jet graded algebra
(`jetGradedAlgebra Z s hs r`, i.e. `⨁_m Γ(U, ker φ_m)` where `φ_m` is the weight-`m`
defect of the rescaling action `t ↦ λt`, `GroupSchemeAction.gradedAlgebra (jetRescalingAction …)`)
is isomorphic, as a ring, to the sections ring of the *algebraic* jet graded algebra
`jetGradedAffineAlgebra Z s hs r` (`J_r(B_U, ε_U)`, the based jet algebra of `B_U = Γ(Z, π⁻¹U)`),
the isomorphism matching the `m`-th grading pieces and the structure maps `Γ(C, U) → S(U)`.

**Source.** §2 of the paper (`𝒮 = (p_J)_*𝒪_J = ⊕ 𝒮_m`, `𝒮_m` = functions homogeneous of weight `m` under parameter
rescaling; replacing `t` by `λt` gives the coordinate algebra a nonnegative grading); Stacks 0EKK
(`𝔾_m`-action ⟺ grading; the ring-level counterpart is `BasedJetAlgebra.mem_grading_iff_coaction`).

**Route.**
Write `α := jetRescalingAction Z s hs r`, `S := GroupSchemeAction.gradedAlgebra α`
(so `(jetGradedAlgebra Z s hs r).1 = S` by `rfl`), `J := relativeJetScheme Z s hs r`, `π := J.hom`,
`A := jetGradedAffineAlgebra Z s hs r`, so `A(U) = J_r(B_U, ε_U)` and `A.grading U m` is the
`m`-th piece `BasedJetAlgebra.grading` (as an `AddSubgroup`).
1. `ι_m : Γ(U, ker φ_m) → Γ(J, π⁻¹U)` is the section map of `kernel.ι φ_m` (`weightPartιApp`);
   it is injective (`weightPartιApp_injective`: `kernel.ι` is mono, the forgetful functor
   to presheaves of modules preserves limits hence monos, monos of presheaves of modules are
   pointwise injective).
2. `χ_U : A(U) ≃+* Γ(J, π⁻¹U)` is the chart identification (`relativeJetScheme.chartEquiv`, a
   composite of `AffineAlgebra.sectionsPreimageEquiv` with `Opens.topIso`; it uses
   `relativeJetScheme = A.toAffineAlgebra.relativeSpec`, which is `rfl`).
3. The piece maps `p_m := χ_U⁻¹ ∘ ι_m : Γ(U, ker φ_m) →+ A(U)` are multiplicative for the graded
   multiplication of `⨁_m Γ(U, ker φ_m)` (`weightPartιApp_sectionsGMul`: `kernel.lift_ι`
   + `Modules.tensorHom_tensorSections` + the multiplication of `π_*𝒪_J` on sections is the
   multiplication of `Γ(J, π⁻¹U)`) and send the unit to the unit (`weightPartιApp_one_app`:
   `kernel.lift_ι` and `unitToPushforwardObjUnit_val_app_apply`), so `DirectSum.toSemiring`
   assembles them into a ring homomorphism `f : ⨁_m Γ(U, ker φ_m) →+* A(U)`.
4. `p_m` lands in the `m`-th grading piece, and every element of the `m`-th grading piece comes from
   `Γ(U, ker φ_m)`: this is the **weight-defect kernel = grading piece** statement
   `relativeJetScheme.weightDefect_app_chartEquiv_eq_zero_iff` (`φ_m(χ_U y) = 0 ⟺ y ∈ A(U)_m`),
   combined with `kernel_ι_app_apply` and `exists_kernel_section` (`JetRescalingChart`).
5. Because `A(U) = ⨁_m A(U)_m` (`DirectSum.Decomposition` from the `GradedRing` instance),
   `decompose (f x) i = p_i (x i)` for every `x`; hence `f` is injective (each `p_i` is), surjective
   (each grading piece is hit), and `x ∈ range (of m) ⟺ f x ∈ A(U)_m`.
6. Structure maps: the geometric unit is `of 0 (S.one.app U a)`, and `ι_0 (S.one.app U a) = π^♯ a`
   (`weightPartιApp_one_app`), while `χ_U (algebraMap a) = π^♯ a` (`relativeJetScheme.chartEquiv_unitHom`:
   the chart `Spec A(U) → Spec_C A` lies over `U`, `AffineAlgebra.chart_hom`).

**Helper lemmas.** For a general `A : X.AffineAlgebra`: `AffineAlgebra.preimageIsoSpec_hom_chart`,
`AffineAlgebra.preimageIsoSpec_hom_chartToOpen`, `AffineAlgebra.morphismRestrict_appTop_topIso_inv`,
`AffineAlgebra.sectionsPreimageEquiv_symm_unitHom`. For the jet scheme: `relativeJetScheme.chartEquiv_eq_chartSections`
(`χ_U` = `chartSections U` transported along `preimage_eq_chartOpen`), `relativeJetScheme.act_appLE_chartEquiv`
(`act^♯ ∘ χ_U = Θ ∘ coaction`), `relativeJetScheme.eval₂RingHom_chartEquiv_lambdaOn_injective` (`Θ` injective).

**Proof-engineering note.** Goals mentioning `U.1` for `U : C.AffineZariskiSite` are "not type-correct under
implicit transparency" (the coercion `↑U` needs the `def AffineZariskiSite` unfolded), and `rw`/`simp` then fail
to find even syntactically present patterns. The proofs in `section Jet` are therefore written in term style
(`congrArg`, `Eq.trans`, `congrArg₂`) instead of `rw`.

**Consumers.** `JetGradedAlgebraLocalWeightedChart` composes this bridge with the algebraic chart
`jetLocalGradedRingEquiv`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry DirectSum CategoryTheory.MonoidalCategory

noncomputable section

namespace GroupSchemeAction

variable {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
  [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}
  [AlgebraicGeometry.IsAffineHom T.hom] (α : GmActionOver k T)

/-- The section map `ι_m : Γ(U, ker φ_m) → Γ(T, π⁻¹U)` of the kernel inclusion of the weight-`m`
defect `φ_m = weightDefect α m`, as an additive map. Its source is the `m`-th piece
`(GroupSchemeAction.gradedAlgebra α).sectionsPiece U m = Γ(U, weightPart α m)` of the old encoding;
its target `Γ(T, π⁻¹U)` is (definitionally) `Γ(U, π_*𝒪_T)`. -/
def weightPartιApp (m : ℕ) (U : S.Opens) :
    (GroupSchemeAction.gradedAlgebra α).sectionsPiece U m →+ Γ(T.left, T.hom ⁻¹ᵁ U) where
  toFun a :=
    show Γ(T.left, T.hom ⁻¹ᵁ U) from
      ((CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m)).val.app (Opposite.op U)).hom a
  map_zero' := map_zero _
  map_add' a b := map_add _ a b

/-- `ι_m` is injective on sections: `kernel.ι` is a monomorphism of sheaves of modules
(`equalizer.ι_mono`), the forgetful functor to presheaves of modules preserves limits
(`SheafOfModules.forgetPreservesLimitsOfShape`) hence monomorphisms, and a monomorphism of
presheaves of modules is injective on every object (`PresheafOfModules.injective_of_mono`). -/
theorem weightPartιApp_injective (m : ℕ) (U : S.Opens) :
    Function.Injective (GroupSchemeAction.weightPartιApp α m U) := by
  intro a b hab
  have hmono : CategoryTheory.Mono
      (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m)) :=
    CategoryTheory.Limits.equalizer.ι_mono
  have : CategoryTheory.Mono
      (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m)).val :=
    @CategoryTheory.Functor.map_mono _ _ _ _ (SheafOfModules.forget _) inferInstance _ _
      (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m)) hmono
  exact PresheafOfModules.injective_of_mono
    (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m)).val (Opposite.op U) hab

/-- `ι` is multiplicative for the graded multiplication of the geometric sections ring:
`ι_{m+n}(a ⋆ b) = ι_m a · ι_n b` in `Γ(T, π⁻¹U)`.

Source: Stacks 0EKK (the multiplication of `⊕ ker φ_m` is the one of `π_*𝒪_T`); §2 of the paper.

Proof: the first two steps below are the general lemma `GradedQCAlgebra.sectionsGMul_app_of_mul_comp`,
applied with `ι_m := kernel.ι φ_m` and `kernel.lift_ι`; the last step is
`pushforwardStructureSheaf.sectionsRing_mul` (`JetSpecIso`).
* By definition (`GradedQCAlgebra.sectionsGMul`), `a ⋆ b = (S.mul m n).app U (tensorSections a b)`
  with `S.mul m n = weightMul α m n = kernel.lift φ_{m+n} ((ι_m ⊗ₘ ι_n) ≫ μ) _`, where
  `μ = pushforwardStructureSheaf.mul T.hom` is the multiplication of `π_*𝒪_T`.
* `kernel.lift_ι` gives `weightMul α m n ≫ kernel.ι φ_{m+n} = (ι_m ⊗ₘ ι_n) ≫ μ`; apply `.val.app (op U)`
  to `tensorSections a b` (composition of morphisms of sheaves of modules is pointwise, `rfl`):
  the left side is `ι_{m+n}(a ⋆ b)`, the right side is `μ.app U ((ι_m ⊗ₘ ι_n).app U (tensorSections a b))`.
* `Modules.tensorHom_tensorSections`: `(ι_m ⊗ₘ ι_n).app U (tensorSections a b) = tensorSections (ι_m a) (ι_n b)`.
* `μ.app U (tensorSections x y) = x * y` in `Γ(T, π⁻¹U)`: by `QCAlgebra.sectionsMul_eq_mul_tensorSections`
  (`rfl`) the left side is the product `x * y` in `(pushforwardStructureSheaf T.hom).sectionsRing U`, and
  `pushforwardStructureSheaf.sectionsRing_mul` (via `pushforwardStructureSheaf.qcPresheafMul_eq`: the
  sheafification comparison isomorphisms cancel and the multiplication is the pointwise `mulFun`) identifies that
  product with the product of `Γ(T, π⁻¹U)`. -/
theorem weightPartιApp_sectionsGMul (m n : ℕ) (U : S.Opens)
    (a : (GroupSchemeAction.gradedAlgebra α).sectionsPiece U m)
    (b : (GroupSchemeAction.gradedAlgebra α).sectionsPiece U n) :
    GroupSchemeAction.weightPartιApp α (m + n) U
        ((GroupSchemeAction.gradedAlgebra α).sectionsGMul U a b) =
      GroupSchemeAction.weightPartιApp α m U a * GroupSchemeAction.weightPartιApp α n U b := by
  have hmul : ∀ m n : ℕ, (GroupSchemeAction.gradedAlgebra α).mul m n ≫
      CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α (m + n)) =
      (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m) ⊗ₘ
          CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α n)) ≫
        (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf T.hom).mul :=
    fun m n => CategoryTheory.Limits.kernel.lift_ι _ _ _
  have h := (GroupSchemeAction.gradedAlgebra α).sectionsGMul_app_of_mul_comp
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf T.hom)
    (fun m => CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m)) hmul U a b
  exact h.trans
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.sectionsRing_mul T.hom U _ _)

/-- `ι_0 (S.one.app U x) = π^♯ x`: the old unit `S.one = weightOne α = kernel.lift _ (π_*𝒪_T).one _`,
`kernel.lift_ι`, and `(π_*𝒪_T).one = unitToPushforwardObjUnit π` is `π^♯` on sections
(`SheafOfModules.unitToPushforwardObjUnit_val_app_apply`, `rfl`). -/
theorem weightPartιApp_one_app (U : S.Opens) (x : Γ(S, U)) :
    GroupSchemeAction.weightPartιApp α 0 U ((GroupSchemeAction.gradedAlgebra α).one.app U x) =
      (T.hom.app U).hom x := by
  have h : GroupSchemeAction.weightOne α ≫
      CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α 0) =
      (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf T.hom).one :=
    CategoryTheory.Limits.kernel.lift_ι _ _ _
  have h2 := congrArg (fun g => (g.val.app (Opposite.op U)).hom x) h
  exact h2

/-- `ι_0` sends the graded unit `1_U = S.one.app U 1` to `1`. -/
theorem weightPartιApp_sectionsGOne (U : S.Opens) :
    GroupSchemeAction.weightPartιApp α 0 U ((GroupSchemeAction.gradedAlgebra α).sectionsGOne U) = 1 := by
  rw [AlgebraicGeometry.Scheme.GradedQCAlgebra.sectionsGOne, GroupSchemeAction.weightPartιApp_one_app]
  exact map_one _

end GroupSchemeAction

namespace AlgebraicGeometry.Scheme.AffineAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (A : X.AffineAlgebra)

private theorem eqToIso_hom_ι {Y : AlgebraicGeometry.Scheme.{u}} {W W' : Y.Opens} (h : W = W') :
    (eqToIso (congrArg AlgebraicGeometry.Scheme.Opens.toScheme h)).hom ≫ W'.ι = W.ι := by
  subst W'
  simp

/-- The chart identification followed by the chart is the inclusion of `π⁻¹U`:
`(preimageIsoSpec U).hom ≫ chart U = (π⁻¹U).ι` (`preimageIsoSpec = eqToIso ≪≫ isoOpensRange.symm`,
`Scheme.Hom.isoOpensRange_inv_comp`). Extracted from the inline proof `hchart` in JetWeightOfOrderQ.lean. -/
theorem preimageIsoSpec_hom_chart (U : X.AffineZariskiSite) :
    (A.preimageIsoSpec U).hom ≫ A.chart U = (A.relativeSpec.hom ⁻¹ᵁ U.toOpens).ι := by
  change ((eqToIso (congrArg AlgebraicGeometry.Scheme.Opens.toScheme
      (A.preimage_eq_opensRange U)) ≪≫ (A.chart U).isoOpensRange.symm).hom ≫ A.chart U) = _
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, AlgebraicGeometry.Scheme.Hom.isoOpensRange_inv_comp]
  exact eqToIso_hom_ι (A.preimage_eq_opensRange U)

/-- The chart `Spec A(U) ≅ π⁻¹U` lies over `U`: `(preimageIsoSpec U).hom ≫ chartToOpen U = π ∣_ U`
(`chart_hom`, `resLE_comp_ι`, `cancel_mono U.ι`). Extracted from the inline proof `hpre` in
JetWeightOfOrderQ.lean. Source: Stacks 01LQ. -/
theorem preimageIsoSpec_hom_chartToOpen (U : X.AffineZariskiSite) :
    (A.preimageIsoSpec U).hom ≫ A.chartToOpen U = A.relativeSpec.hom ∣_ U.toOpens := by
  apply (cancel_mono U.toOpens.ι).mp
  calc
    ((A.preimageIsoSpec U).hom ≫ A.chartToOpen U) ≫ U.toOpens.ι =
        (A.preimageIsoSpec U).hom ≫ A.chart U ≫ A.relativeSpec.hom := by
      simp only [Category.assoc, A.chart_hom]
    _ = (A.relativeSpec.hom ⁻¹ᵁ U.toOpens).ι ≫ A.relativeSpec.hom := by
      rw [← Category.assoc, A.preimageIsoSpec_hom_chart]
    _ = (A.relativeSpec.hom ∣_ U.toOpens) ≫ U.toOpens.ι := by
      rw [← AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict]
      exact (AlgebraicGeometry.Scheme.Hom.resLE_comp_ι _ _).symm

/-- Bookkeeping on an open subscheme: if `ψ ≫ D.ι = g`, then `ψ^♯(u|_D) = g.appLE D ⊤ u`
(same statement as `appTop_topIso_inv_eq_appLE` in Stacks01ne.lean, copied privately to avoid that import). -/
private theorem appTop_topIso_inv_eq_appLE_aux {T Y : AlgebraicGeometry.Scheme.{u}} (D : Y.Opens)
    (ψ : T ⟶ D.toScheme) (g : T ⟶ Y) (hψ : ψ ≫ D.ι = g) (u : Γ(Y, D)) (e : ⊤ ≤ g ⁻¹ᵁ D) :
    ψ.appTop (D.topIso.inv u) = g.appLE D ⊤ e u := by
  subst hψ
  have h := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE ψ D.ι D ⊤ ⊤
    D.ι_preimage_self.ge (le_rfl : (⊤ : T.Opens) ≤ ψ ⁻¹ᵁ ⊤)
  rw [← h, CommRingCat.comp_apply]
  have h1 : D.ι.appLE D ⊤ D.ι_preimage_self.ge u = D.topIso.inv u := by
    rw [AlgebraicGeometry.Scheme.Opens.ι_appLE, AlgebraicGeometry.Scheme.Opens.topIso_inv]
    rfl
  have h2 : ψ.appLE ⊤ ⊤ (le_rfl : (⊤ : T.Opens) ≤ ψ ⁻¹ᵁ ⊤) = ψ.appTop := by
    change ψ.app ⊤ ≫ T.presheaf.map (𝟙 _) = ψ.app ⊤
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [h1, h2]

/-- `(π ∣_ U)^♯ (U.topIso.inv a) = (π⁻¹U).topIso.inv (π^♯ a)`: restriction of `π` to `U` on global
sections is `π.app U`, transported along the two `topIso`s (`morphismRestrict_ι`, `comp_appLE`, `Opens.ι_appLE`). -/
theorem morphismRestrict_appTop_topIso_inv {T Y : AlgebraicGeometry.Scheme.{u}} (π : T ⟶ Y) (U : Y.Opens)
    (a : Γ(Y, U)) :
    (π ∣_ U).appTop (U.topIso.inv a) = (π ⁻¹ᵁ U).topIso.inv ((π.app U).hom a) := by
  have e : (⊤ : (π ⁻¹ᵁ U).toScheme.Opens) ≤ ((π ⁻¹ᵁ U).ι ≫ π) ⁻¹ᵁ U := by
    rw [AlgebraicGeometry.Scheme.Hom.comp_preimage, AlgebraicGeometry.Scheme.Opens.ι_preimage_self]
  rw [appTop_topIso_inv_eq_appLE_aux U (π ∣_ U) ((π ⁻¹ᵁ U).ι ≫ π) (AlgebraicGeometry.morphismRestrict_ι π U) a e]
  have h := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE (π ⁻¹ᵁ U).ι π U (π ⁻¹ᵁ U) ⊤ le_rfl
    (π ⁻¹ᵁ U).ι_preimage_self.ge
  rw [← h, CommRingCat.comp_apply, AlgebraicGeometry.Scheme.Hom.appLE_eq_app]
  have h1 : ∀ x : Γ(T, π ⁻¹ᵁ U), (π ⁻¹ᵁ U).ι.appLE (π ⁻¹ᵁ U) ⊤ (π ⁻¹ᵁ U).ι_preimage_self.ge x =
      (π ⁻¹ᵁ U).topIso.inv x := by
    intro x
    rw [AlgebraicGeometry.Scheme.Opens.ι_appLE, AlgebraicGeometry.Scheme.Opens.topIso_inv]
    rfl
  exact h1 _

/-- **The chart identification is compatible with the structure maps** (general form, any
`A : X.AffineAlgebra`): `(A.sectionsPreimageEquiv U).symm (A.unitHom U a) = (π⁻¹U).topIso.inv (π^♯ a)`.
Proof: unfold `sectionsPreimageEquiv` (`(preimageIsoSpec U).hom.appTop ∘ (ΓSpecIso A(U)).inv`),
`ΓSpecIso_inv_naturality`, `preimageIsoSpec_hom_chartToOpen` (so `preimageIsoSpec.hom ≫ Spec.map unit =
(π ∣_ U) ≫ isoSpec.hom`), `IsAffineOpen.isoSpec_hom_appTop`, `morphismRestrict_appTop_topIso_inv`.
Source: Stacks 01LQ. -/
theorem sectionsPreimageEquiv_symm_unitHom (U : X.AffineZariskiSite) (a : Γ(X, U.toOpens)) :
    (A.sectionsPreimageEquiv U).symm (A.unitHom U a) =
      (A.relativeSpec.hom ⁻¹ᵁ U.toOpens).topIso.inv ((A.relativeSpec.hom.app U.toOpens).hom a) := by
  have h0 : (A.sectionsPreimageEquiv U).symm (A.unitHom U a) =
      (A.preimageIsoSpec U).hom.appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (A.sections U)).inv ((A.unit.app (Opposite.op U)).hom a)) := rfl
  have h1 : (AlgebraicGeometry.Scheme.ΓSpecIso (A.sections U)).inv ((A.unit.app (Opposite.op U)).hom a) =
      (AlgebraicGeometry.Spec.map (A.unit.app (Opposite.op U))).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, U.toOpens)).inv a) :=
    congrArg (fun φ => φ.hom a)
      (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality (A.unit.app (Opposite.op U)))
  have h2 : (A.preimageIsoSpec U).hom ≫ AlgebraicGeometry.Spec.map (A.unit.app (Opposite.op U)) =
      (A.relativeSpec.hom ∣_ U.toOpens) ≫ U.2.isoSpec.hom := by
    have hpre' : ((A.preimageIsoSpec U).hom ≫ AlgebraicGeometry.Spec.map (A.unit.app (Opposite.op U))) ≫
        U.2.isoSpec.inv = A.relativeSpec.hom ∣_ U.toOpens :=
      (Category.assoc _ _ _).trans (A.preimageIsoSpec_hom_chartToOpen U)
    exact (Iso.comp_inv_eq _).mp hpre'
  have h3 : (A.preimageIsoSpec U).hom.appTop
        ((AlgebraicGeometry.Spec.map (A.unit.app (Opposite.op U))).appTop
          ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, U.toOpens)).inv a)) =
      ((A.preimageIsoSpec U).hom ≫ AlgebraicGeometry.Spec.map (A.unit.app (Opposite.op U))).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, U.toOpens)).inv a) := rfl
  have h4 : U.2.isoSpec.hom.appTop ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, U.toOpens)).inv a) =
      U.toOpens.topIso.inv a := by
    have h4' := congrArg (fun φ => φ.hom ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, U.toOpens)).inv a))
      (AlgebraicGeometry.IsAffineOpen.isoSpec_hom_appTop U.2)
    refine h4'.trans ?_
    show U.toOpens.topIso.inv ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, U.toOpens)).hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, U.toOpens)).inv a)) = _
    rw [CategoryTheory.Iso.inv_hom_id_apply]
  rw [h0, h1, h3, h2]
  change (A.relativeSpec.hom ∣_ U.toOpens).appTop
    (U.2.isoSpec.hom.appTop ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, U.toOpens)).inv a)) = _
  rw [h4]
  exact AlgebraicGeometry.Scheme.AffineAlgebra.morphismRestrict_appTop_topIso_inv A.relativeSpec.hom U.toOpens a

end AlgebraicGeometry.Scheme.AffineAlgebra

section Jet

variable {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
  [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C)
  [AlgebraicGeometry.IsAffineHom Z.hom]
  (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)

/-- **Chart identification** `χ_U : A(U) ≃+* Γ(J, π⁻¹U)` for `A = jetGradedAffineAlgebra Z s hs r`
(so `A(U) = J_r(B_U, ε_U)`) and `J = relativeJetScheme Z s hs r` (which is `A.toAffineAlgebra.relativeSpec`
by `rfl`, `relativeJetScheme_eq`): `AffineAlgebra.sectionsPreimageEquiv`
(`Γ((π⁻¹U).toScheme, ⊤) ≃+* A(U)`, from the chart `Spec A(U) ≅ π⁻¹U`) followed by `Opens.topIso`.
It agrees with `relativeJetScheme.chartSections U` transported along `preimage_eq_chartOpen U`
(both are `ΓSpecIso⁻¹ ≫ isoOpensRange⁻¹.appTop ≫ topIso` for the same open immersion
`chart U = colimit.ι = gluingData.cover.f U`). -/
def relativeJetScheme.chartEquiv (U : C.AffineZariskiSite) :
    (jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.sections U ≃+*
      Γ((relativeJetScheme (k := k) Z s hs r).left,
        (relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.toOpens) :=
  ((jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.sectionsPreimageEquiv U).symm.trans
    ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.toOpens).topIso.commRingCatIsoToRingEquiv


/-- The chart identification is compatible with the structure maps: `χ_U (algebraMap a) = π^♯ a` for `a ∈ Γ(C, U)`
(here `unitHom U a = algebraMap a` by definition of `coefficientMap`). A specialisation of
`AffineAlgebra.sectionsPreimageEquiv_symm_unitHom` above.

Source: Stacks 01LQ (the chart `Spec A(U) → Spec_C A` is a `U`-morphism); §2 of the paper.

Proof sketch (a statement about any `A : X.AffineAlgebra`, with
`A := (jetGradedAffineAlgebra Z s hs r).toAffineAlgebra` and `relativeJetScheme = A.relativeSpec` by `rfl`).
* Unfold: `χ_U = topIso.hom ∘ (A.sectionsPreimageEquiv U).symm`, and
  `A.sectionsPreimageEquiv U = ((Γ.mapIso (A.preimageIsoSpec U).op).symm ≪≫ ΓSpecIso (A(U))).commRingCatIsoToRingEquiv`
  (RelativeSpecSections.lean), so `(sectionsPreimageEquiv U).symm z = (preimageIsoSpec U).hom.appTop ((ΓSpecIso (A(U))).inv z)`.
* `(ΓSpecIso (A(U))).inv (A.unit.app (op U) a) = (Spec.map (A.unit.app (op U))).appTop ((ΓSpecIso Γ(C,U)).inv a)`
  by `Scheme.ΓSpecIso_naturality` (`(Spec.map f).appTop ≫ (ΓSpecIso R).hom = (ΓSpecIso S).hom ≫ f`, rearranged).
* `(A.preimageIsoSpec U).hom ≫ Spec.map (A.unit.app (op U)) = (A.preimageIsoSpec U).hom ≫ A.chartToOpen U ≫ U.2.isoSpec.hom`
  (`chartToOpen U = Spec.map (unit) ≫ U.2.isoSpec.inv`, definitional), and
  `(A.preimageIsoSpec U).hom ≫ A.chartToOpen U = A.relativeSpec.hom ∣_ U`
  (`AffineAlgebra.preimageIsoSpec_hom_chartToOpen`, via `A.chart_hom`, `Scheme.Hom.isoOpensRange_inv_comp`,
  `resLE_comp_ι`, `cancel_mono U.ι`).
* `U.2.isoSpec.hom.appTop ((ΓSpecIso Γ(C,U)).inv a) = U.topIso.inv a` (`IsAffineOpen.isoSpec_hom`,
  `Scheme.Opens.toSpecΓ_appTop`), and `(π ∣_ U).appTop (U.topIso.inv a) = (π⁻¹U).topIso.inv (π.app U a)`
  (`morphismRestrict_appTop`); finally `topIso.hom ∘ topIso.inv = id`. -/
theorem relativeJetScheme.chartEquiv_unitHom (U : C.AffineZariskiSite) (a : Γ(C, U.toOpens)) :
    relativeJetScheme.chartEquiv (k := k) Z s hs r U
        ((jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.unitHom U a) =
      ((relativeJetScheme (k := k) Z s hs r).hom.app U.toOpens).hom a := by
  have h : ((jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.sectionsPreimageEquiv U).symm
        ((jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.unitHom U a) =
      ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.toOpens).topIso.inv
        (((relativeJetScheme (k := k) Z s hs r).hom.app U.toOpens).hom a) :=
    (jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.sectionsPreimageEquiv_symm_unitHom U a
  show ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.toOpens).topIso.hom
    (((jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.sectionsPreimageEquiv U).symm
      ((jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.unitHom U a)) = _
  rw [h, CategoryTheory.Iso.inv_hom_id_apply]

/-- Transport of global sections along an equality of opens `h : W = W'`:
`W.topIso.hom ((eqToIso h).hom.appTop z) = (Y.presheaf.map (eqToHom h).op) (W'.topIso.hom z)`. -/
private theorem topIso_hom_eqToIso_appTop {Y : AlgebraicGeometry.Scheme.{u}} {W W' : Y.Opens} (h : W = W')
    (z : Γ(W'.toScheme, ⊤)) :
    W.topIso.hom ((CategoryTheory.eqToIso (congrArg AlgebraicGeometry.Scheme.Opens.toScheme h)).hom.appTop z) =
      (Y.presheaf.map (CategoryTheory.eqToHom h).op).hom (W'.topIso.hom z) := by
  subst h
  simp

/-- `χ_U` agrees with the older chart map `relativeJetScheme.chartSections U` transported along
`preimage_eq_chartOpen U` (both are `ΓSpecIso⁻¹ ≫ isoOpensRange⁻¹.appTop ≫ topIso` for the same open
immersion `chart U = colimit.ι = gluingData.cover.f U`; the transport is `topIso_hom_eqToIso_appTop`). -/
theorem relativeJetScheme.chartEquiv_eq_chartSections (U : C.AffineZariskiSite)
    (hU : (relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1 = relativeJetScheme.chartOpen (k := k) Z s hs r U)
    (y : (jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.sections U) :
    (relativeJetScheme.chartEquiv (k := k) Z s hs r U) y =
      ((relativeJetScheme (k := k) Z s hs r).left.presheaf.map (CategoryTheory.eqToHom hU).op).hom
        ((relativeJetScheme.chartSections (k := k) Z s hs r U).hom y) :=
  topIso_hom_eqToIso_appTop ((jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.preimage_eq_opensRange U)
    (((jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.chart U).isoOpensRange.inv.appTop
      ((AlgebraicGeometry.Scheme.ΓSpecIso _).inv y))

private theorem appLE_congr_hom_aux {X Y : AlgebraicGeometry.Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V e' := by
  subst h
  rfl

/-- **`act^♯ ∘ χ_U = Θ ∘ coaction`** on the chart: for `y ∈ A(U) = J_r(B_U, ε_U)`,
`act^♯ (χ_U y) = Θ (coaction y)` where `Θ = eval₂ (pr₂^♯ ∘ χ_U) λ : A(U)[X] → Γ(W, q⁻¹U)`.
Both sides are ring homomorphisms out of a quotient of `MvPolynomial (Fin r × B_U) Γ(C,U)`
(`Ideal.Quotient.ringHom_ext`, `MvPolynomial.ringHom_ext`); on `algebraMap a` both are `pr₂^♯ (π^♯ a)`
(`chartEquiv_unitHom`, `act_over`, `comp_appLE`, `coaction_algebraMap`), on `X (q, b) = d_q b` both are
`λ^{q+1} · pr₂^♯ (χ_U (d_q b))` (`jetRescalingAction_act_appLE_coeffClass` via `chartEquiv_eq_chartSections`,
`coaction_coeffClass`). Source: §2 of the paper; Stacks 0EKK.
(Proof written in term style: `rw` fails on these goals — the `AffineZariskiSite` coercion `U.1` makes them
"not type-correct under implicit transparency".) -/
theorem relativeJetScheme.act_appLE_chartEquiv (U : C.AffineZariskiSite) (hle : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ (jetRescalingAction (k := k) Z s hs r).act ⁻¹ᵁ ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1))
    (y : (jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.sections U) :
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    ((jetRescalingAction (k := k) Z s hs r).act.appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) hle).hom ((relativeJetScheme.chartEquiv (k := k) Z s hs r U) y) = (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) (BasedJetAlgebra.coaction (relativeJetScheme.augmentation Z s hs U.1) r y) := by
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  have hU := relativeJetScheme.preimage_eq_chartOpen (k := k) Z s hs r U
  have key : ((jetRescalingAction (k := k) Z s hs r).act.appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) hle).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom =
      (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))).comp (BasedJetAlgebra.coaction (relativeJetScheme.augmentation Z s hs U.1) r) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      show ((jetRescalingAction (k := k) Z s hs r).act.appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) hle).hom ((relativeJetScheme.chartEquiv (k := k) Z s hs r U) (algebraMap Γ(C, U.1) (BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.1) r) a)) = (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) (BasedJetAlgebra.coaction (relativeJetScheme.augmentation Z s hs U.1) r (algebraMap Γ(C, U.1) (BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.1) r) a))
      have e1 : BasedJetAlgebra.coaction (relativeJetScheme.augmentation Z s hs U.1) r (algebraMap Γ(C, U.1) (BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.1) r) a) = Polynomial.C (algebraMap Γ(C, U.1) (BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.1) r) a) :=
        BasedJetAlgebra.coaction_algebraMap (relativeJetScheme.augmentation Z s hs U.1) r a
      have e2 : (relativeJetScheme.chartEquiv (k := k) Z s hs r U) (algebraMap Γ(C, U.1) (BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.1) r) a) = ((relativeJetScheme (k := k) Z s hs r).hom.app U.1).hom a :=
        relativeJetScheme.chartEquiv_unitHom (k := k) Z s hs r U a
      have e3 : (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) (Polynomial.C (algebraMap Γ(C, U.1) (BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.1) r) a)) = ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom ((relativeJetScheme.chartEquiv (k := k) Z s hs r U) (algebraMap Γ(C, U.1) (BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.1) r) a)) :=
        Polynomial.eval₂_C _ _
      have c1 := congrArg (fun φ => φ.hom a)
        (AlgebraicGeometry.Scheme.Hom.comp_appLE (jetRescalingAction (k := k) Z s hs r).act (relativeJetScheme (k := k) Z s hs r).hom U.1 (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) hle)
      have c2 := congrArg (fun φ => φ.hom a)
        (AlgebraicGeometry.Scheme.Hom.comp_appLE (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) (relativeJetScheme (k := k) Z s hs r).hom U.1 (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1)
          (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le)
      have c3 : ((jetRescalingAction (k := k) Z s hs r).act ≫ (relativeJetScheme (k := k) Z s hs r).hom).appLE U.1 (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) hle =
          ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom).appLE U.1 (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le :=
        appLE_congr_hom_aux (jetRescalingAction (k := k) Z s hs r).act_over _ _ _ _
      have hB : ((jetRescalingAction (k := k) Z s hs r).act.appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) hle).hom (((relativeJetScheme (k := k) Z s hs r).hom.app U.1).hom a) = ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom (((relativeJetScheme (k := k) Z s hs r).hom.app U.1).hom a) :=
        c1.symm.trans ((congrArg (fun φ => φ.hom a) c3).trans c2)
      exact (congrArg ((jetRescalingAction (k := k) Z s hs r).act.appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) hle).hom e2).trans (hB.trans ((congrArg ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom e2).symm.trans
        (e3.symm.trans (congrArg (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) e1).symm)))
    · rintro ⟨⟨qv, hq⟩, b⟩
      show ((jetRescalingAction (k := k) Z s hs r).act.appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) hle).hom ((relativeJetScheme.chartEquiv (k := k) Z s hs r U) (Ideal.Quotient.mk _ (MvPolynomial.X (⟨qv, hq⟩, b)))) =
        (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) (BasedJetAlgebra.coaction (relativeJetScheme.augmentation Z s hs U.1) r (Ideal.Quotient.mk _ (MvPolynomial.X (⟨qv, hq⟩, b))))
      have e0 : (Ideal.Quotient.mk _ (MvPolynomial.X (⟨qv, hq⟩, b)) : (BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.1) r)) = (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r (qv + 1) b) :=
        (BasedJetAlgebra.coeffClass_succ (relativeJetScheme.augmentation Z s hs U.1) r qv hq b).symm
      have e1 : BasedJetAlgebra.coaction (relativeJetScheme.augmentation Z s hs U.1) r (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r (qv + 1) b) = Polynomial.C (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r (qv + 1) b) * Polynomial.X ^ (qv + 1) :=
        BasedJetAlgebra.coaction_coeffClass (relativeJetScheme.augmentation Z s hs U.1) r (qv + 1) hq b
      have e2 : (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) (Polynomial.C (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r (qv + 1) b) * Polynomial.X ^ (qv + 1)) =
          ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom ((relativeJetScheme.chartEquiv (k := k) Z s hs r U) (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r (qv + 1) b)) * (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k))) ^ (qv + 1) :=
        (map_mul (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) _ _).trans (congrArg₂ (· * ·) (Polynomial.eval₂_C _ _)
          ((map_pow (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) _ _).trans (congrArg (· ^ (qv + 1)) (Polynomial.eval₂_X _ _))))
      have e4 : (relativeJetScheme.chartEquiv (k := k) Z s hs r U) (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r (qv + 1) b) = (((relativeJetScheme (k := k) Z s hs r).left.presheaf.map (CategoryTheory.eqToHom hU).op).hom ((relativeJetScheme.chartSections (k := k) Z s hs r U).hom (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r (qv + 1) b))) :=
        relativeJetScheme.chartEquiv_eq_chartSections (k := k) Z s hs r U hU _
      have h := jetRescalingAction_act_appLE_coeffClass (k := k) Z s hs r U ⟨qv, hq⟩ b hU hle
      have hpow : ((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom (((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)) ^ (qv + 1)) = (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k))) ^ (qv + 1) := map_pow _ _ _
      have hA : ((jetRescalingAction (k := k) Z s hs r).act.appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) hle).hom ((relativeJetScheme.chartEquiv (k := k) Z s hs r U) (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r (qv + 1) b)) = (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k))) ^ (qv + 1) * ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom ((relativeJetScheme.chartEquiv (k := k) Z s hs r U) (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r (qv + 1) b)) :=
        (congrArg ((jetRescalingAction (k := k) Z s hs r).act.appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) hle).hom e4).trans (h.trans (congrArg₂ (· * ·) hpow
          (congrArg ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom e4).symm))
      exact (congrArg (fun z => ((jetRescalingAction (k := k) Z s hs r).act.appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) hle).hom ((relativeJetScheme.chartEquiv (k := k) Z s hs r U) z)) e0).trans ((hA.trans ((mul_comm _ _).trans
        (e2.symm.trans (congrArg (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) e1.symm)))).trans
        (congrArg (fun z => (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) (BasedJetAlgebra.coaction (relativeJetScheme.augmentation Z s hs U.1) r z)) e0).symm)
  exact DFunLike.congr_fun key y

/-- `Θ = eval₂ (pr₂^♯ ∘ χ_U) λ : A(U)[X] → Γ(W, q⁻¹U)` is injective: `Θ p = Σ_n pr₂^♯ (χ_U (coeff p n)) λ^n`,
and the powers of `λ` are linearly independent over `Γ(J, π⁻¹U)` (`Gm_pullback_lambda_pow_independent`,
`π⁻¹U` affine since `π` is affine); `χ_U` is injective. -/
theorem relativeJetScheme.eval₂RingHom_chartEquiv_lambdaOn_injective (U : C.AffineZariskiSite) :
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    Function.Injective (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) := by
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  refine (injective_iff_map_eq_zero (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k))))).mpr fun p hp => ?_
  have hV : AlgebraicGeometry.IsAffineOpen ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) := U.2.preimage (relativeJetScheme (k := k) Z s hs r).hom
  let yf : ℕ →₀ Γ((relativeJetScheme (k := k) Z s hs r).left, ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1)) :=
    Finsupp.onFinset p.support (fun n => (relativeJetScheme.chartEquiv (k := k) Z s hs r U) (p.coeff n)) (fun n hn =>
      Polynomial.mem_support_iff.mpr (fun h0 => hn ((congrArg (relativeJetScheme.chartEquiv (k := k) Z s hs r U) h0).trans (map_zero _))))
  have hΘp : (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) p =
      ∑ n ∈ p.support, ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom ((relativeJetScheme.chartEquiv (k := k) Z s hs r U) (p.coeff n)) * (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k))) ^ n :=
    Polynomial.eval₂_eq_sum
  have hsum : (yf.sum fun n a => (Gm.lambdaOn ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k)))) ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1)) ^ n *
      ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) _ le_rfl).hom a) = 0 :=
    (Finsupp.onFinset_sum _ (fun n =>
      (congrArg (fun t => (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k))) ^ n * t) (map_zero _)).trans (mul_zero _))).trans
      ((Finset.sum_congr rfl (fun n _ => mul_comm _ _)).trans (hΘp.symm.trans hp))
  have hy0 := Gm_pullback_lambda_pow_independent ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k)))) ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) hV yf hsum
  refine Polynomial.ext fun n => ?_
  have h1 : yf n = 0 := (congrArg (fun y : ℕ →₀ Γ((relativeJetScheme (k := k) Z s hs r).left, ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1)) => y n) hy0).trans Finsupp.zero_apply
  have h2 : (relativeJetScheme.chartEquiv (k := k) Z s hs r U) (p.coeff n) = 0 := h1
  exact ((relativeJetScheme.chartEquiv (k := k) Z s hs r U).injective (h2.trans (map_zero _).symm)).trans (Polynomial.coeff_zero n).symm

/-- **Weight-defect kernel = grading piece** (assembled from `weightDefect_app_apply`, `act_appLE_chartEquiv`,
`eval₂RingHom_chartEquiv_lambdaOn_injective` and `mem_grading_iff_coaction` along the steps below):
for `y ∈ A(U) = J_r(B_U, ε_U)`, `φ_m(χ_U y) = 0` in `Γ(G_m ×_k J, q⁻¹U)` iff `y` lies in the `m`-th
piece `A.grading U m` (= `BasedJetAlgebra.grading ε_U r m`, membership is `Iff.rfl` via
`GradedRing.mem_addSubgroupGrading`). This is the relative, nonnegative Stacks 0EKK for the rescaling
action, at the level of one affine chart.

Source: §2 of the paper; Stacks 0EKK; Demailly [Dem11, (0.3)].

Proof sketch. Notation: `W = G_m ×_k J`, `pr₁, pr₂` its projections,
`q = pr₂ ≫ π`, `λ = pr₁^♯(T 1)|_{q⁻¹U}` (`Gm.lambdaOn`), `act = (jetRescalingAction Z s hs r).act`,
`x = χ_U y`.
1. `GroupSchemeAction.weightDefect_app_apply`:
   `φ_m x = act^♯ x − λ^m · pr₂^♯ x`, where `act^♯ = act.appLE (π⁻¹U) (q⁻¹U)` (inclusion
   `preimage_le_act_preimage`) and `pr₂^♯ = pr₂.appLE (π⁻¹U) (q⁻¹U)`.
2. Let `Θ : A(U)[X] →+* Γ(W, q⁻¹U)` be `Polynomial.eval₂RingHom (pr₂^♯ ∘ χ_U) λ`
   (so `Θ (C z) = pr₂^♯ (χ_U z)`, `Θ X = λ`). Claim: `act^♯ (χ_U y) = Θ (coaction y)` for all `y`
   (`BasedJetAlgebra.coaction : J_r(B,ε) →+* J_r(B,ε)[X]`). Both sides are
   ring homomorphisms out of `J_r(B_U, ε_U)`, a quotient of `MvPolynomial (Fin r × B_U) Γ(C,U)`, so
   by `Ideal.Quotient.ringHom_ext` + `MvPolynomial.ringHom_ext` (as in `bja_map_id_of`)
   it suffices to compare them on `algebraMap a` (`a ∈ Γ(C,U)`) and on the
   coefficient classes `d_q b = coeffClass ε_U r (q+1) b` (`q < r`, `b ∈ B_U`):
   * `act^♯ (χ_U (algebraMap a)) = act^♯ (π^♯ a)` (`relativeJetScheme.chartEquiv_unitHom`)
     `= (act ≫ π)^♯ a = (pr₂ ≫ π)^♯ a = pr₂^♯ (π^♯ a)` (`α.act_over`, `Scheme.Hom.comp_appLE`), and
     `Θ (coaction (algebraMap a)) = Θ (C (algebraMap a)) = pr₂^♯ (χ_U (algebraMap a)) = pr₂^♯ (π^♯ a)`
     (`BasedJetAlgebra.coaction_algebraMap`).
   * `act^♯ (χ_U (d_q b)) = λ^{q+1} · pr₂^♯ (χ_U (d_q b))` is `jetRescalingAction_act_appLE_coeffClass`
     (it is stated with `chartSections U` transported along
     `preimage_eq_chartOpen U`, which is `χ_U` — see the docstring of `chartEquiv`), and
     `Θ (coaction (d_q b)) = Θ (C (d_q b) · X^{q+1}) = pr₂^♯ (χ_U (d_q b)) · λ^{q+1}`
     (`BasedJetAlgebra.coaction_coeffClass`).
3. Hence `φ_m (χ_U y) = Θ (coaction y) − Θ (C y · X^m) = Θ (coaction y − C y · X^m)`.
4. `Θ` is injective: `Gm_pullback_sections_tensorEquiv` (for
   `T := J.left`, `V := π⁻¹U`, affine because `π` is affine) identifies `Γ(W, q⁻¹U)` with
   `k[λ^{±1}] ⊗_k Γ(J, π⁻¹U)` sending `pr₂^♯ z ↦ 1 ⊗ z`, `λ ↦ T 1 ⊗ 1`, so `Θ (Σ_i C z_i X^i) = Σ_i T^i ⊗ χ_U z_i`
   and `{T^i}` is a `k`-basis (`laurentTmulIndep`); equivalently apply
   `Gm_pullback_lambda_pow_independent` to the coefficient family of `coaction y − C y · X^m`
   (`χ_U` is injective). Note `q⁻¹U = pr₂⁻¹(π⁻¹U)` (`Scheme.Hom.comp_preimage`).
5. So `φ_m (χ_U y) = 0 ⟺ coaction y = C y · X^m ⟺ y ∈ grading ε_U r m`
   (`BasedJetAlgebra.mem_grading_iff_coaction`).
Edge cases: `r = 0` (no coefficient classes, `A(U) = Γ(C,U)`, grading in degree 0 only: `φ_m (π^♯ a) =
(1 − λ^m) pr₂^♯ π^♯ a`, zero iff `m = 0` or `a = 0`, consistent); `U = ⊥` (zero rings); `m > r`
(weights of monomials exceed `r`, nothing changes). -/
theorem relativeJetScheme.weightDefect_app_chartEquiv_eq_zero_iff (U : C.AffineZariskiSite) (m : ℕ)
    (y : (jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.sections U) :
    ((GroupSchemeAction.weightDefect (jetRescalingAction (k := k) Z s hs r) m).val.app
        (Opposite.op U.toOpens)).hom
      (show (((AlgebraicGeometry.Scheme.Modules.pushforward (relativeJetScheme (k := k) Z s hs r).hom).obj
          (SheafOfModules.unit (relativeJetScheme (k := k) Z s hs r).left.ringCatSheaf)).val.obj
            (Opposite.op U.toOpens) : Type u) from
        relativeJetScheme.chartEquiv (k := k) Z s hs r U y) = 0 ↔
      y ∈ (jetGradedAffineAlgebra Z s hs r).grading U m := by
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  have hle : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ (jetRescalingAction (k := k) Z s hs r).act ⁻¹ᵁ ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) :=
    GroupSchemeAction.preimage_le_act_preimage (jetRescalingAction (k := k) Z s hs r) U.1
  have h1 := GroupSchemeAction.weightDefect_app_apply (jetRescalingAction (k := k) Z s hs r) m U.1
    ((relativeJetScheme.chartEquiv (k := k) Z s hs r U) y) hle
  have h2 : ((jetRescalingAction (k := k) Z s hs r).act.appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) hle).hom ((relativeJetScheme.chartEquiv (k := k) Z s hs r U) y) = (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) (BasedJetAlgebra.coaction (relativeJetScheme.augmentation Z s hs U.1) r (y : BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.1) r)) :=
    relativeJetScheme.act_appLE_chartEquiv (k := k) Z s hs r U hle y
  have hΘC : (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) (Polynomial.C (R := (BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.1) r)) y) = ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom ((relativeJetScheme.chartEquiv (k := k) Z s hs r U) y) := Polynomial.eval₂_C _ _
  have hΘX : (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) Polynomial.X = (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k))) := Polynomial.eval₂_X _ _
  have hsub : (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) (BasedJetAlgebra.coaction (relativeJetScheme.augmentation Z s hs U.1) r (y : BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.1) r) - Polynomial.C (R := (BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.1) r)) y * Polynomial.X ^ m) =
      ((jetRescalingAction (k := k) Z s hs r).act.appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) hle).hom ((relativeJetScheme.chartEquiv (k := k) Z s hs r U) y) - (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k))) ^ m * ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom ((relativeJetScheme.chartEquiv (k := k) Z s hs r U) y) :=
    (map_sub (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) _ _).trans (congrArg₂ (· - ·) h2.symm ((map_mul (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) _ _).trans
      ((congrArg₂ (· * ·) hΘC ((map_pow (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) _ _).trans (congrArg (· ^ m) hΘX))).trans (mul_comm _ _))))
  have hpow : ((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom (((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)) ^ m) = (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k))) ^ m := map_pow _ _ _
  have h1' := h1.trans (congrArg (fun t => ((jetRescalingAction (k := k) Z s hs r).act.appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) hle).hom ((relativeJetScheme.chartEquiv (k := k) Z s hs r U) y) - t * ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom ((relativeJetScheme.chartEquiv (k := k) Z s hs r U) y)) hpow)
  have hmem : y ∈ (jetGradedAffineAlgebra Z s hs r).grading U m ↔
      (y : BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.1) r) ∈ BasedJetAlgebra.grading (relativeJetScheme.augmentation Z s hs U.1) r m := Iff.rfl
  have hinj := relativeJetScheme.eval₂RingHom_chartEquiv_lambdaOn_injective (k := k) Z s hs r U
  refine (Iff.of_eq (congrArg (· = 0) (h1'.trans hsub.symm))).trans ?_
  refine Iff.trans ⟨fun h => hinj (h.trans (map_zero _).symm),
    fun h => (congrArg (Polynomial.eval₂RingHom (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appLE ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom.comp (relativeJetScheme.chartEquiv (k := k) Z s hs r U).toRingHom) (((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).presheaf.map (CategoryTheory.homOfLE (le_top : (((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))) ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1) ≤ ⊤)).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ (AlgebraicGeometry.Spec (CommRingCat.of k))))).appTop.hom (Gm.lambda k)))) h).trans (map_zero _)⟩ ?_
  exact (sub_eq_zero.trans (BasedJetAlgebra.mem_grading_iff_coaction (relativeJetScheme.augmentation Z s hs U.1) r m (y : BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.1) r)).symm).trans hmem.symm

/-- **The geometric and the algebraic jet graded algebra agree on an affine chart** (assembled from the lemmas
above): `e : ⨁_m Γ(U, ker φ_m) ≃+* J_r(B_U, ε_U)` matches the gradings and the structure maps.
See the module docstring for the route. -/
theorem jetGradedAlgebra_sections_equiv_jetGradedAffineAlgebra (U : C.AffineZariskiSite) :
    ∃ e : ((jetGradedAlgebra (k := k) Z s hs r).1).toGradedAffineAlgebra.toAffineAlgebra.sections U ≃+*
        (jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.sections U,
      (∀ (m : ℕ)
          (a : ((jetGradedAlgebra (k := k) Z s hs r).1).toGradedAffineAlgebra.toAffineAlgebra.sections U),
        a ∈ ((jetGradedAlgebra (k := k) Z s hs r).1).toGradedAffineAlgebra.grading U m ↔
          e a ∈ (jetGradedAffineAlgebra Z s hs r).grading U m) ∧
      (∀ a : Γ(C, U.toOpens),
        e (((jetGradedAlgebra (k := k) Z s hs r).1).toGradedAffineAlgebra.toAffineAlgebra.unitHom U a) =
          (jetGradedAffineAlgebra Z s hs r).toAffineAlgebra.unitHom U a) := by
  classical
  let α := jetRescalingAction (k := k) Z s hs r
  let S := GroupSchemeAction.gradedAlgebra α
  let A := jetGradedAffineAlgebra Z s hs r
  let χ := relativeJetScheme.chartEquiv (k := k) Z s hs r U
  let p : ∀ m : ℕ, S.sectionsPiece U.toOpens m →+ A.toAffineAlgebra.sections U :=
    fun m => χ.symm.toAddMonoidHom.comp (GroupSchemeAction.weightPartιApp α m U.toOpens)
  have hp : ∀ (m : ℕ) (a : S.sectionsPiece U.toOpens m),
      p m a = χ.symm (GroupSchemeAction.weightPartιApp α m U.toOpens a) := fun _ _ => rfl
  have hone : p 0 GradedMonoid.GOne.one = 1 := by
    show χ.symm (GroupSchemeAction.weightPartιApp α 0 U.toOpens (S.sectionsGOne U.toOpens)) = 1
    rw [GroupSchemeAction.weightPartιApp_sectionsGOne]
    exact map_one χ.symm
  have hmul : ∀ {i j : ℕ} (a : S.sectionsPiece U.toOpens i) (b : S.sectionsPiece U.toOpens j),
      p (i + j) (GradedMonoid.GMul.mul a b) = p i a * p j b := by
    intro i j a b
    show χ.symm (GroupSchemeAction.weightPartιApp α (i + j) U.toOpens (S.sectionsGMul U.toOpens a b)) =
      χ.symm (GroupSchemeAction.weightPartιApp α i U.toOpens a) *
        χ.symm (GroupSchemeAction.weightPartιApp α j U.toOpens b)
    rw [GroupSchemeAction.weightPartιApp_sectionsGMul, map_mul]
  let f : (⨁ m, S.sectionsPiece U.toOpens m) →+* A.toAffineAlgebra.sections U :=
    DirectSum.toSemiring p hone hmul
  have hf_of : ∀ (m : ℕ) (a : S.sectionsPiece U.toOpens m),
      f (DirectSum.of (S.sectionsPiece U.toOpens) m a) = p m a := fun m a =>
    DirectSum.toSemiring_of p hone hmul m a
  -- each piece lands in the m-th grading
  have hp_mem : ∀ (m : ℕ) (a : S.sectionsPiece U.toOpens m), p m a ∈ A.grading U m := by
    intro m a
    rw [← relativeJetScheme.weightDefect_app_chartEquiv_eq_zero_iff (k := k) Z s hs r U m (p m a), hp,
      RingEquiv.apply_symm_apply]
    exact AlgebraicGeometry.Scheme.Modules.kernel_ι_app_apply
      (GroupSchemeAction.weightDefect α m) U.toOpens a
  -- each element of the m-th grading comes from a piece
  have hp_surj : ∀ (m : ℕ) (y : A.toAffineAlgebra.sections U), y ∈ A.grading U m →
      ∃ a : S.sectionsPiece U.toOpens m, p m a = y := by
    intro m y hy
    have h0 := (relativeJetScheme.weightDefect_app_chartEquiv_eq_zero_iff (k := k) Z s hs r U m y).mpr hy
    obtain ⟨a, ha⟩ := AlgebraicGeometry.Scheme.Modules.exists_kernel_section
      (GroupSchemeAction.weightDefect α m) U.toOpens _ h0
    refine ⟨a, ?_⟩
    have ha' : GroupSchemeAction.weightPartιApp α m U.toOpens a = χ y := ha
    exact (hp m a).trans ((congrArg χ.symm ha').trans (χ.symm_apply_apply y))
  -- the decomposition of f x
  have hdec : ∀ (x : ⨁ m, S.sectionsPiece U.toOpens m) (i : ℕ),
      ((DirectSum.decompose (A.grading U) (f x) i : A.grading U i) : A.toAffineAlgebra.sections U) =
        p i (x i) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero =>
      intro i
      rw [map_zero, DirectSum.decompose_zero, DirectSum.zero_apply, DirectSum.zero_apply, map_zero]
      rfl
    | of j b =>
      intro i
      rw [hf_of]
      by_cases hij : i = j
      · subst hij
        rw [DirectSum.decompose_of_mem_same (A.grading U) (hp_mem i b), DirectSum.of_eq_same]
      · rw [DirectSum.decompose_of_mem_ne (A.grading U) (hp_mem j b) (Ne.symm hij),
          DirectSum.of_eq_of_ne j i b hij, map_zero]
    | add x y hx hy =>
      intro i
      rw [map_add, DirectSum.decompose_add, DirectSum.add_apply, AddSubgroup.coe_add, hx i, hy i,
        DirectSum.add_apply, map_add]
  have hinj : Function.Injective f := by
    intro x y hxy
    refine DirectSum.ext fun i => ?_
    apply GroupSchemeAction.weightPartιApp_injective α i U.toOpens
    apply χ.symm.injective
    have h1 := hdec x i
    have h2 := hdec y i
    rw [hxy] at h1
    exact h1.symm.trans h2
  have hsurj : Function.Surjective f := by
    intro y
    have hy : y ∈ f.range := by
      rw [← DirectSum.sum_support_decompose (A.grading U) y]
      refine Subring.sum_mem _ fun m _ => ?_
      obtain ⟨a, ha⟩ := hp_surj m _ (SetLike.coe_mem (DirectSum.decompose (A.grading U) y m))
      exact ⟨DirectSum.of (S.sectionsPiece U.toOpens) m a, (hf_of m a).trans ha⟩
    exact hy
  have hgrade : ∀ (m : ℕ) (a : ⨁ m, S.sectionsPiece U.toOpens m),
      a ∈ S.sectionsGrading U.toOpens m ↔ f a ∈ A.grading U m := by
    intro m a
    constructor
    · rintro ⟨b, rfl⟩
      rw [hf_of]
      exact hp_mem m b
    · intro h
      refine ⟨a m, ?_⟩
      refine DirectSum.ext fun i => ?_
      by_cases hi : i = m
      · subst hi
        exact DirectSum.of_eq_same i (a i)
      · rw [DirectSum.of_eq_of_ne m i (a m) hi]
        apply GroupSchemeAction.weightPartιApp_injective α i U.toOpens
        apply χ.symm.injective
        have h1 := hdec a i
        rw [DirectSum.decompose_of_mem_ne (A.grading U) h (Ne.symm hi)] at h1
        rw [map_zero, map_zero]
        exact h1
  have hunit : ∀ a : Γ(C, U.toOpens),
      f (DirectSum.of (S.sectionsPiece U.toOpens) 0 (S.one.app U.toOpens a)) =
        A.toAffineAlgebra.unitHom U a := by
    intro a
    have h1 := hf_of 0 (S.one.app U.toOpens a)
    have h2 := hp 0 (S.one.app U.toOpens a)
    have h3 := GroupSchemeAction.weightPartιApp_one_app α U.toOpens a
    have h4 := relativeJetScheme.chartEquiv_unitHom (k := k) Z s hs r U a
    exact h1.trans (h2.trans ((congrArg χ.symm h3).trans
      ((congrArg χ.symm h4.symm).trans (χ.symm_apply_apply _))))
  refine ⟨RingEquiv.ofBijective
    (f : S.sectionsRing U.toOpens →+* A.toAffineAlgebra.sections U) ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro m a
    exact hgrade m a
  · intro a
    exact hunit a

end Jet

end
