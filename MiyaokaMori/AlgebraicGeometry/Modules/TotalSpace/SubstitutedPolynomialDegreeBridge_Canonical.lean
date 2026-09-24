import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceCanonicallyOver
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousAtSections
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotSectionsPolynomial
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.SubstitutedPolynomialDegreeBridge_XiDegreeAdd
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.SubstitutedPolynomialDegreeBridge_XiDegreePullbackMap
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.SubstitutedPolynomialDegreeBridge_UnitDegree

/-! # The ξ-degree bound with the canonical identification

**The paper's bound with the canonical identification.** On `Tot(L)`, substituting sections `P_ℓ` of ξ-degree
`≤ r₀` into a homogeneous polynomial `F` of degree `d` gives a section of `(p^*M)^{⊗d}`; transported to
`p^*(M^d)` by the canonical isomorphism `θ₀ := tensorPowPullbackZpowIso L M d` (built recursively from
`p^*(A ⊗ B) ≅ p^*A ⊗ p^*B` and `M^e ⊗ M ≅ M^{e+1}`), it has ξ-degree `≤ d·r₀`. (In the paper:
"`F_j(P_0,…,P_N)` … has fiber degree at most `d_j r_0`".)

Route:
1. `evalHomogeneousAtSections` is `Σ_α φ(a_α) • (P_{g 0} ⊗ ⋯ ⊗ P_{g (d-1)})` (definition).
2. Each monomial: induction on `e`; `θ₀ (e+1) (x ⊗ y) = p^*(ζ_e) (xiSectionMul (θ₀ e x) y)`
   (`tensorPowPullbackZpowIso_succ_sectionTensor`), `xiDegree_mul_le`, naturality
   (`xiDegree_pullback_map_le`), base case `xiDegree_pullbackUnitIso_inv_one_le_zero`.
3. Sums take the max (`xiDegree_sum_le`); base scalars `φ(a) = p^#(ψ(a))` do not raise the degree
   (`xiCoefficient_smul_base`, `totalSpace_base_scalar`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- ζ_e : `(M^e ⊗ M) ≅ M^{e+1}` on the base (`zpowAddIso`, `zpowOneIso`, and the cast `(e : ℤ) + 1 = ↑(e+1)`). -/
noncomputable def LineBundle.zpowSuccTensorIso {k : Type u} [Field k] {X : Variety k}
    (M : LineBundle X) (e : ℕ) :
    ((M.zpow (e : ℤ)).tensor M).toModules ≅ (M.zpow ((e + 1 : ℕ) : ℤ)).toModules :=
  AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (M.zpow (e : ℤ)).toModules M.toModules ≪≫
    CategoryTheory.MonoidalCategory.tensorIso (CategoryTheory.Iso.refl _) M.zpowOneIso.symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (M.zpow (e : ℤ)).toModules
      (M.zpow 1).toModules).symm ≪≫
    (M.zpowAddIso (e : ℤ) 1).symm ≪≫
    CategoryTheory.eqToIso (congrArg (fun z : ℤ => (M.zpow z).toModules) (by push_cast; ring))

/-- θ₀ e : `(p^*M)^{⊗e} ≅ p^*(M^e)`, the canonical isomorphism, defined recursively: `θ₀ 0 = (pullbackUnitIso p).symm`,
`θ₀ (e+1) = (θ₀ e ⊗ 𝟙) ≫ (p^*(M^e) ⊗ p^*M ≅ p^*(M^e ⊗ M)) ≫ p^*(ζ_e)`. -/
noncomputable def tensorPowPullbackZpowIso {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) :
    (e : ℕ) → (AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules) e ≅
      (AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj (M.zpow (e : ℤ)).toModules)
  | 0 => (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).symm
  | e + 1 =>
    AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫
      CategoryTheory.MonoidalCategory.tensorIso (tensorPowPullbackZpowIso L M e)
        (CategoryTheory.Iso.refl _) ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
        (M.zpow (e : ℤ)).toModules M.toModules).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).mapIso (M.zpowSuccTensorIso e)

/-- Base scalars: `xiCoefficient ((p^# a) • P) q = a • xiCoefficient P q` (every layer of the coefficient map is
linear over `Γ(C, ⊤)`, the `Γ(Tot, ⊤)`-action on `Γ(C, p_*N)` being the restriction of scalars along `p^#`). -/
theorem xiCoefficient_smul_base {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) (a : Γ(C.toScheme, ⊤))
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) (q : ℕ) :
    xiCoefficient L M ((show (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf.obj.obj
        (Opposite.op ⊤) from (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.appTop a) • P) q =
      (show C.toScheme.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) • xiCoefficient L M P q := by
  unfold xiCoefficient AlgebraicGeometry.Scheme.totalSpace.coefficient
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward
  rw [map_smul]
  have hcast : (show (((AlgebraicGeometry.Scheme.Modules.pushforward
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (CategoryTheory.MonoidalCategoryStruct.tensorObj
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)
          (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf))).val.obj
        (Opposite.op ⊤) : Type u) from
      (show (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf.obj.obj
        (Opposite.op ⊤) from (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.appTop a) •
        ((CategoryTheory.MonoidalCategoryStruct.rightUnitor
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)).inv.val.app
          (Opposite.op ⊤)).hom P)
      = (show C.toScheme.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) •
        (show (((AlgebraicGeometry.Scheme.Modules.pushforward
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (CategoryTheory.MonoidalCategoryStruct.tensorObj
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)
          (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf))).val.obj
        (Opposite.op ⊤) : Type u) from
        ((CategoryTheory.MonoidalCategoryStruct.rightUnitor
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)).inv.val.app
          (Opposite.op ⊤)).hom P) := rfl
  erw [hcast]
  repeat' rw [map_smul]

/-- `tensorIsoTensorObj.inv` sends the monoidal pairing back to `sectionTensor`
(local copy of the private lemma in `EvaluateHomogeneousLocalFormula`). -/
theorem tensorIsoTensorObj_inv_tensorSections' {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} (s : (M.val.obj (Opposite.op ⊤) : Type u))
    (t : (N.val.obj (Opposite.op ⊤) : Type u)) :
    ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M N).inv.val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t) =
      sectionTensor s t := by
  let e := AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M N
  have hinj : Function.Injective (fun z => (e.hom.val.app (Opposite.op ⊤)).hom z) := by
    intro a b hab
    have h := congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom) e.hom_inv_id
    have h' := congrArg (fun φ => φ a) h
    have h'' := congrArg (fun φ => φ b) h
    change (e.inv.val.app (Opposite.op ⊤)).hom
        ((e.hom.val.app (Opposite.op ⊤)).hom a) = a at h'
    change (e.inv.val.app (Opposite.op ⊤)).hom
        ((e.hom.val.app (Opposite.op ⊤)).hom b) = b at h''
    calc
      a = (e.inv.val.app (Opposite.op ⊤)).hom
          ((e.hom.val.app (Opposite.op ⊤)).hom a) := h'.symm
      _ = (e.inv.val.app (Opposite.op ⊤)).hom
          ((e.hom.val.app (Opposite.op ⊤)).hom b) := congrArg _ hab
      _ = b := h''
  apply hinj
  have h := congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom
      (AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t)) e.inv_hom_id
  change (e.hom.val.app (Opposite.op ⊤)).hom
      ((e.inv.val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t)) =
    AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t at h
  exact h

/-- **Key computation**: `θ₀ (e+1) (x ⊗ y) = p^*(ζ_e) (xiSectionMul (θ₀ e x) y)`. -/
theorem tensorPowPullbackZpowIso_succ_sectionTensor {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) (e : ℕ)
    (x : ((AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules) e).val.obj
          (Opposite.op ⊤) : Type u))
    (y : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    (tensorPowPullbackZpowIso L M (e + 1)).hom.app ⊤ (sectionTensor x y) =
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map (M.zpowSuccTensorIso e).hom).app ⊤
        (xiSectionMul L (M.zpow (e : ℤ)) M ((tensorPowPullbackZpowIso L M e).hom.app ⊤ x) y) := by
  have h1 : ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
      (AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules) e)
      ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)).hom.val.app
        (Opposite.op ⊤)).hom (sectionTensor x y) =
      AlgebraicGeometry.Scheme.Modules.tensorSections _ _ ⊤ x y := rfl
  have h2 : ((CategoryTheory.MonoidalCategoryStruct.tensorHom
      (C := (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules)
      (tensorPowPullbackZpowIso L M e).hom (CategoryTheory.CategoryStruct.id _)).val.app
        (Opposite.op ⊤)).hom (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ ⊤ x y) =
      AlgebraicGeometry.Scheme.Modules.tensorSections _ _ ⊤
        (((tensorPowPullbackZpowIso L M e).hom.val.app (Opposite.op ⊤)).hom x) y := by
    rw [AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections]
    rfl
  have h3 := tensorIsoTensorObj_inv_tensorSections'
    (M := (AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj (M.zpow (e : ℤ)).toModules)
    (N := (AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)
    (((tensorPowPullbackZpowIso L M e).hom.val.app (Opposite.op ⊤)).hom x) y
  change (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map
          (M.zpowSuccTensorIso e).hom).val.app (Opposite.op ⊤)).hom
    (((AlgebraicGeometry.Scheme.Modules.pullbackTensorIso
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
        (M.zpow (e : ℤ)).toModules M.toModules).inv.val.app (Opposite.op ⊤)).hom
      (((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv.val.app (Opposite.op ⊤)).hom
        (((CategoryTheory.MonoidalCategoryStruct.tensorHom
          (C := (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules)
          (tensorPowPullbackZpowIso L M e).hom (CategoryTheory.CategoryStruct.id _)).val.app
            (Opposite.op ⊤)).hom
          (((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom.val.app
            (Opposite.op ⊤)).hom (sectionTensor x y))))) = _
  rw [h1, h2, h3]
  rfl


/-- Scalars coming from the base do not raise the ξ-degree. -/
theorem xiDegree_smul_base_le {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) (a : Γ(C.toScheme, ⊤))
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    xiDegree L M ((show (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf.obj.obj
        (Opposite.op ⊤) from (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.appTop a) • P) ≤
      xiDegree L M P := by
  unfold xiDegree
  apply Finset.max_le
  intro q hq
  have hne := (xiCoefficient_finite_support L M _).mem_toFinset.mp hq
  simp only [Set.mem_ofPred_eq] at hne
  have h0 := xiCoefficient_smul_base L M a P q
  rw [h0] at hne
  have hne' : xiCoefficient L M P q ≠ 0 := fun h => hne (by rw [h, smul_zero])
  exact Finset.le_max ((xiCoefficient_finite_support L M P).mem_toFinset.mpr hne')

/-- The k-scalars on Tot(L) factor through the base: φ_Tot c = p^# (φ_C c). -/
theorem totalSpace_base_scalar {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) (c : k) :
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom c =
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.appTop
      (((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom c) := by
  have hbase : (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)) := rfl
  have hbaseTop : (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop ≫
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.appTop =
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)).appTop := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_appTop, hbase]
  change ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left ↘
      AlgebraicGeometry.Spec (CommRingCat.of k)).appTop
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) =
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.appTop
      ((C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))
  exact (congrArg (fun h => h ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))
    (congrArg (fun h => h.hom) hbaseTop)).symm

/-- Monomials: ξ-degree of θ₀_e (P_{g 0} ⊗ ⋯ ⊗ P_{g (e-1)}) is at most e·r₀. -/
theorem xiDegree_canonical_monomial_le {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) {N r₀ : ℕ}
    (P : Fin (N + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ ℓ, xiDegree L M (P ℓ) ≤ (r₀ : WithBot ℕ)) :
    ∀ (e : ℕ) (g : Fin e → Fin (N + 1)),
      xiDegree L (M.zpow (e : ℤ)) ((tensorPowPullbackZpowIso L M e).hom.app ⊤
        (evalHomogeneousAtSections.monomial _ P e g)) ≤ ((e * r₀ : ℕ) : WithBot ℕ)
  | 0, g => by
    simp only [Nat.zero_mul]
    exact xiDegree_pullbackUnitIso_inv_one_le_zero L M
  | e + 1, g => by
    rw [evalHomogeneousAtSections.monomial, tensorPowPullbackZpowIso_succ_sectionTensor]
    refine le_trans (xiDegree_pullback_map_le L _ _ _ _) ?_
    refine le_trans (xiDegree_mul_le L (M.zpow (e : ℤ)) M _ _) ?_
    have h1 := xiDegree_canonical_monomial_le L M P hP e (fun i => g i.castSucc)
    have h2 := hP (g (Fin.last e))
    calc _ ≤ ((e * r₀ : ℕ) : WithBot ℕ) + (r₀ : WithBot ℕ) := add_le_add h1 h2
      _ = (((e + 1) * r₀ : ℕ) : WithBot ℕ) := by
        have h : (e + 1) * r₀ = e * r₀ + r₀ := by ring
        rw [h, Nat.cast_add]

/-- **Canonical form of the bound**: with θ₀ = `tensorPowPullbackZpowIso`. -/
theorem xiDegree_evalHomogeneousAtSections_canonical_le {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {N r₀ dj : ℕ}
    (L M : LineBundle C.toVariety)
    (P : Fin (N + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ ℓ, xiDegree L M (P ℓ) ≤ (r₀ : WithBot ℕ))
    (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous dj) :
    xiDegree L (M.zpow dj)
        ((tensorPowPullbackZpowIso L M dj).hom.app ⊤ (evalHomogeneousAtSections _ F hF P)) ≤
      ((dj * r₀ : ℕ) : WithBot ℕ) := by
  simp only [evalHomogeneousAtSections]
  change xiDegree L (M.zpow dj) ((((tensorPowPullbackZpowIso L M dj).hom.val.app
    (Opposite.op ⊤)).hom) (∑ α ∈ F.support.attach, _)) ≤ _
  rw [map_sum]
  apply xiDegree_sum_le
  intro α _
  change xiDegree L (M.zpow dj) ((((tensorPowPullbackZpowIso L M dj).hom.val.app
    (Opposite.op ⊤)).hom)
    ((show (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf.obj.obj
        (Opposite.op ⊤) from
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left ↘
          AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom (F.coeff α.1)) •
      evalHomogeneousAtSections.monomial _ P dj
        (evalHomogeneousAtSections.indices α.1 (hF (MvPolynomial.mem_support_iff.mp α.2))))) ≤ _
  rw [map_smul, totalSpace_base_scalar]
  refine le_trans (xiDegree_smul_base_le L (M.zpow dj) _ _) ?_
  exact xiDegree_canonical_monomial_le L M P hP dj _

end
