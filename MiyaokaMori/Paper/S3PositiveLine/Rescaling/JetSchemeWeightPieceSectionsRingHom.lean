import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGradedAlgebraSectionsBridge

/-! # The weight-piece sections ring as functions on the jet scheme
(helpers for the two main lemmas of `PositiveLineCoreWeightedRescaling_AffineJet`, Lemma 3.1 of the paper)

For a `G_m`-action `α` on `T → S` affine over `S`, the weight pieces `Γ(U, ker φ_m)` of the old
encoding `GroupSchemeAction.gradedAlgebra α` sit inside `Γ(T, π⁻¹U)` through `weightPartιApp`
(`kernel.ι` on sections). Here this is packaged as a **ring homomorphism**
`Θ_U : (gradedAlgebra α).sectionsRing U →+* Γ(T, π⁻¹U)` (`weightPartιRingHom`; multiplicativity is
`weightPartιApp_sectionsGMul`), compatible with the structure maps (`weightPartιRingHom_sectionsUnitHom`)
and with restriction (`weightPartιRingHom_restrict`). For the jet scheme `J_r^s` and an affine `U`,
`Θ_U` is **bijective** (`relativeJetScheme.weightPartιRingHom_bijective`): this is exactly the
bijectivity part of `jetGradedAlgebra_sections_equiv_jetGradedAffineAlgebra`
(`JetGradedAlgebraSectionsBridge`), whose proof is repeated here because that statement does not
expose how its equivalence acts on the pieces (only the grading and the unit are recorded there).
Source: Stacks 0EKK (the graded algebra `⊕ ker φ_m` of a `G_m`-action is `π_*𝒪_T`); §2.1–2.2 of the paper.

Also here, for any scheme: a `K`-point of an affine open `U ⊆ X` with prescribed ring map
`ψ : Γ(X, U) → K`, namely `Spec.map ψ ≫ hU.fromSpec`, together with its `appLE` on `U`
(`IsAffineOpen.appLE_SpecMap_fromSpec`) and the converse factorization of any `Spec R → X` landing in
`U` (`IsAffineOpen.eq_SpecMap_appLE_fromSpec`). Source: Stacks 01I1 (`Spec`–`Γ` adjunction on an
affine open); Mathlib `IsAffineOpen.SpecMap_appLE_fromSpec`.

.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry DirectSum

noncomputable section

namespace GroupSchemeAction

variable {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
  [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}
  [AlgebraicGeometry.IsAffineHom T.hom] (α : GmActionOver k T)

/-- **The weight pieces as functions, as a ring homomorphism**
`Θ_U : ⊕_m Γ(U, ker φ_m) →+* Γ(T, π⁻¹U)`, `ofPiece m a ↦ ι_m a` (`weightPartιApp`); it is a ring
homomorphism by `weightPartιApp_sectionsGOne` and `weightPartιApp_sectionsGMul`
(`DirectSum.toSemiring`). -/
def weightPartιRingHom (U : S.Opens) :
    (GroupSchemeAction.gradedAlgebra α).sectionsRing U →+* Γ(T.left, T.hom ⁻¹ᵁ U) :=
  DirectSum.toSemiring (fun m => GroupSchemeAction.weightPartιApp α m U)
    (GroupSchemeAction.weightPartιApp_sectionsGOne α U)
    (fun {i j} a b => GroupSchemeAction.weightPartιApp_sectionsGMul α i j U a b)

theorem weightPartιRingHom_ofPiece (U : S.Opens) (m : ℕ)
    (a : (GroupSchemeAction.gradedAlgebra α).sectionsPiece U m) :
    GroupSchemeAction.weightPartιRingHom α U ((GroupSchemeAction.gradedAlgebra α).ofPiece U m a) =
      GroupSchemeAction.weightPartιApp α m U a :=
  DirectSum.toSemiring_of _ _ _ m a

/-- `Θ_U` is compatible with the structure maps: `Θ_U (algebraMap r) = π^♯ r`
(`weightPartιApp_one_app`). -/
theorem weightPartιRingHom_sectionsUnitHom (U : S.Opens) (r : Γ(S, U)) :
    GroupSchemeAction.weightPartιRingHom α U
        ((GroupSchemeAction.gradedAlgebra α).sectionsUnitHom U r) =
      (T.hom.app U).hom r := by
  exact (GroupSchemeAction.weightPartιRingHom_ofPiece α U 0
    ((GroupSchemeAction.gradedAlgebra α).one.app U r)).trans
    (GroupSchemeAction.weightPartιApp_one_app α U r)

/-- `Θ` is compatible with restriction: `(Θ_V x)|_{π⁻¹U} = Θ_U (x|_U)` (naturality of `kernel.ι`
on sections, `PresheafOfModules.naturality_apply`; both sides are ring homomorphisms in `x`,
`DirectSum.ringHom_ext`). -/
theorem weightPartιRingHom_restrict {U V : S.Opens} (h : U ≤ V) (h' : T.hom ⁻¹ᵁ U ≤ T.hom ⁻¹ᵁ V)
    (x : (GroupSchemeAction.gradedAlgebra α).sectionsRing V) :
    (T.left.presheaf.map (homOfLE h').op).hom (GroupSchemeAction.weightPartιRingHom α V x) =
      GroupSchemeAction.weightPartιRingHom α U
        ((GroupSchemeAction.gradedAlgebra α).sectionsRestrictHom h x) := by
  have key : (T.left.presheaf.map (homOfLE h').op).hom.comp
        (GroupSchemeAction.weightPartιRingHom α V) =
      (GroupSchemeAction.weightPartιRingHom α U).comp
        ((GroupSchemeAction.gradedAlgebra α).sectionsRestrictHom h) := by
    refine DirectSum.ringHom_ext fun m a => ?_
    show (T.left.presheaf.map (homOfLE h').op).hom
        (GroupSchemeAction.weightPartιRingHom α V
          ((GroupSchemeAction.gradedAlgebra α).ofPiece V m a)) =
      GroupSchemeAction.weightPartιRingHom α U
        ((GroupSchemeAction.gradedAlgebra α).sectionsRestrictHom h
          ((GroupSchemeAction.gradedAlgebra α).ofPiece V m a))
    rw [(GroupSchemeAction.gradedAlgebra α).sectionsRestrictHom_ofPiece h m a,
      GroupSchemeAction.weightPartιRingHom_ofPiece, GroupSchemeAction.weightPartιRingHom_ofPiece]
    exact (PresheafOfModules.naturality_apply
      (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m)).val (homOfLE h).op a).symm
  exact DFunLike.congr_fun key x

end GroupSchemeAction

section Jet

variable {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
  [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C)
  [AlgebraicGeometry.IsAffineHom Z.hom]
  (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)

/-- **`Θ_U` is bijective on affine opens of the base, for the jet scheme.** Proof (the bijectivity
part of `jetGradedAlgebra_sections_equiv_jetGradedAffineAlgebra`, repeated): compose with the chart
identification `χ_U⁻¹ : Γ(J, π⁻¹U) ≃ A(U)` (`relativeJetScheme.chartEquiv`) to
`f := χ⁻¹ ∘ Θ`; `f (ofPiece m a) = χ⁻¹ (ι_m a)` lies in the `m`-th graded piece of `A(U)`
(`weightDefect_app_chartEquiv_eq_zero_iff`, `kernel_ι_app_apply`), every element of that piece is
of this form (`exists_kernel_section`), and the `m`-th component of the decomposition of `f x` is
`χ⁻¹ (ι_m (x m))` (`DirectSum.decompose_of_mem_same/ne`); injectivity then follows from
`weightPartιApp_injective`, surjectivity from `DirectSum.sum_support_decompose`. -/
theorem relativeJetScheme.weightPartιRingHom_bijective (U : C.AffineZariskiSite) :
    Function.Bijective
      (GroupSchemeAction.weightPartιRingHom (jetRescalingAction (k := k) Z s hs r) U.toOpens) := by
  classical
  let α := jetRescalingAction (k := k) Z s hs r
  let S := GroupSchemeAction.gradedAlgebra α
  let A := jetGradedAffineAlgebra Z s hs r
  let χ := relativeJetScheme.chartEquiv (k := k) Z s hs r U
  let Θ := GroupSchemeAction.weightPartιRingHom α U.toOpens
  let f : (⨁ m, S.sectionsPiece U.toOpens m) →+* A.toAffineAlgebra.sections U :=
    χ.symm.toRingHom.comp (Θ : (⨁ m, S.sectionsPiece U.toOpens m) →+* _)
  let p : ∀ m : ℕ, S.sectionsPiece U.toOpens m → A.toAffineAlgebra.sections U :=
    fun m a => χ.symm (GroupSchemeAction.weightPartιApp α m U.toOpens a)
  have hf_of : ∀ (m : ℕ) (a : S.sectionsPiece U.toOpens m),
      f (DirectSum.of (S.sectionsPiece U.toOpens) m a) = p m a := by
    intro m a
    show χ.symm (Θ (S.ofPiece U.toOpens m a)) = _
    rw [GroupSchemeAction.weightPartιRingHom_ofPiece]
  -- each piece lands in the m-th grading
  have hp_mem : ∀ (m : ℕ) (a : S.sectionsPiece U.toOpens m), p m a ∈ A.grading U m := by
    intro m a
    rw [← relativeJetScheme.weightDefect_app_chartEquiv_eq_zero_iff (k := k) Z s hs r U m (p m a)]
    show ((GroupSchemeAction.weightDefect α m).val.app (Opposite.op U.toOpens)).hom
      (χ (χ.symm (GroupSchemeAction.weightPartιApp α m U.toOpens a))) = 0
    rw [RingEquiv.apply_symm_apply]
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
    exact (congrArg χ.symm ha').trans (χ.symm_apply_apply y)
  -- the decomposition of f x
  have hdec : ∀ (x : ⨁ m, S.sectionsPiece U.toOpens m) (i : ℕ),
      ((DirectSum.decompose (A.grading U) (f x) i : A.grading U i) : A.toAffineAlgebra.sections U) =
        p i (x i) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero =>
      intro i
      rw [map_zero, DirectSum.decompose_zero, DirectSum.zero_apply, DirectSum.zero_apply]
      show (0 : A.toAffineAlgebra.sections U) = χ.symm (GroupSchemeAction.weightPartιApp α i U.toOpens 0)
      rw [map_zero, map_zero]
    | of j b =>
      intro i
      rw [hf_of]
      by_cases hij : i = j
      · subst hij
        rw [DirectSum.decompose_of_mem_same (A.grading U) (hp_mem i b), DirectSum.of_eq_same]
      · rw [DirectSum.decompose_of_mem_ne (A.grading U) (hp_mem j b) (Ne.symm hij),
          DirectSum.of_eq_of_ne j i b hij]
        show (0 : A.toAffineAlgebra.sections U) = χ.symm (GroupSchemeAction.weightPartιApp α i U.toOpens 0)
        rw [map_zero, map_zero]
    | add x y hx hy =>
      intro i
      rw [map_add, DirectSum.decompose_add, DirectSum.add_apply, AddSubgroup.coe_add, hx i, hy i,
        DirectSum.add_apply]
      show _ = χ.symm (GroupSchemeAction.weightPartιApp α i U.toOpens (x i + y i))
      rw [map_add, map_add]
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
  refine ⟨fun x y hxy => hinj ?_, fun z => ?_⟩
  · show χ.symm (Θ x) = χ.symm (Θ y)
    rw [hxy]
  · obtain ⟨x, hx⟩ := hsurj (χ.symm z)
    refine ⟨x, ?_⟩
    have hx' : χ.symm (Θ x) = χ.symm z := hx
    exact χ.symm.injective hx'

end Jet

namespace AlgebraicGeometry.IsAffineOpen

variable {X : AlgebraicGeometry.Scheme.{u}} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
  {R : CommRingCat.{u}}

/-- The point `Spec.map ψ ≫ hU.fromSpec : Spec R → X` lands in `U` (`range_fromSpec`). -/
theorem top_le_preimage_SpecMap_fromSpec (ψ : Γ(X, U) ⟶ R) :
    (⊤ : (AlgebraicGeometry.Spec R).Opens) ≤ (AlgebraicGeometry.Spec.map ψ ≫ hU.fromSpec) ⁻¹ᵁ U := by
  intro x _
  show hU.fromSpec.base ((AlgebraicGeometry.Spec.map ψ).base x) ∈ U
  exact hU.range_fromSpec.le ⟨_, rfl⟩

/-- **`appLE` of the point attached to a ring map**: on `U` the morphism `Spec.map ψ ≫ hU.fromSpec`
acts on sections as `ψ` followed by the identification `R ≅ Γ(Spec R, ⊤)`
(`appLE_comp_appLE`, `fromSpec_app_self`, `ΓSpecIso_inv_naturality`). -/
theorem appLE_SpecMap_fromSpec (ψ : Γ(X, U) ⟶ R)
    (e : (⊤ : (AlgebraicGeometry.Spec R).Opens) ≤ (AlgebraicGeometry.Spec.map ψ ≫ hU.fromSpec) ⁻¹ᵁ U) :
    (AlgebraicGeometry.Spec.map ψ ≫ hU.fromSpec).appLE U ⊤ e =
      ψ ≫ (AlgebraicGeometry.Scheme.ΓSpecIso R).inv := by
  have e₁ : (⊤ : (AlgebraicGeometry.Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U :=
    hU.fromSpec_preimage_self.ge
  have e₂ : (⊤ : (AlgebraicGeometry.Spec R).Opens) ≤ (AlgebraicGeometry.Spec.map ψ) ⁻¹ᵁ ⊤ :=
    fun _ _ => trivial
  have hcomp := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE (AlgebraicGeometry.Spec.map ψ)
    hU.fromSpec U ⊤ ⊤ e₁ e₂
  have h1 : hU.fromSpec.appLE U ⊤ e₁ = (AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [AlgebraicGeometry.Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp,
      ← op_comp]
    have : (homOfLE e₁ ≫ eqToHom hU.fromSpec_preimage_self :
        (⊤ : (AlgebraicGeometry.Spec Γ(X, U)).Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
    rw [this, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  have h2 : (AlgebraicGeometry.Spec.map ψ).appLE ⊤ ⊤ e₂ = (AlgebraicGeometry.Spec.map ψ).appTop := by
    rw [AlgebraicGeometry.Scheme.Hom.appTop, AlgebraicGeometry.Scheme.Hom.app_eq_appLE]
    rfl
  rw [← hcomp, h1, h2]
  exact (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality ψ).symm

/-- **Any `Spec R → X` landing in the affine open `U` is the point attached to its ring map**
`Γ(X, U) → Γ(Spec R, ⊤) ≅ R` (`SpecMap_appLE_fromSpec` with `V = ⊤`, `fromSpec_top`,
`isoSpec_Spec_inv`). -/
theorem eq_SpecMap_appLE_fromSpec (y : AlgebraicGeometry.Spec R ⟶ X)
    (e : (⊤ : (AlgebraicGeometry.Spec R).Opens) ≤ y ⁻¹ᵁ U) :
    y = AlgebraicGeometry.Spec.map (y.appLE U ⊤ e ≫ (AlgebraicGeometry.Scheme.ΓSpecIso R).hom) ≫
      hU.fromSpec := by
  have h := hU.SpecMap_appLE_fromSpec y (AlgebraicGeometry.isAffineOpen_top _) e
  rw [AlgebraicGeometry.IsAffineOpen.fromSpec_top, AlgebraicGeometry.Scheme.isoSpec_Spec_inv] at h
  rw [AlgebraicGeometry.Spec.map_comp, Category.assoc, h, ← Category.assoc,
    ← AlgebraicGeometry.Spec.map_comp, Iso.inv_hom_id, AlgebraicGeometry.Spec.map_id, Category.id_comp]

end AlgebraicGeometry.IsAffineOpen

end
