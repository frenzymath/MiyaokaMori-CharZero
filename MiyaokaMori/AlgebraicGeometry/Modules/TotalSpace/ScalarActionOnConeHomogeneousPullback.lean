import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualPowerContraction
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerSheafMul
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousAtSections
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousLocalFormula
import MiyaokaMori.AlgebraicGeometry.Modules.HomogeneousEquationAsSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivCoordinates
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle

/-! # Scaling invariance of the pullback of a homogeneous equation section

"Scaling invariance" of the pullback of the homogeneous equation section `F(τ) ∈ Γ(Tot V, (π^*A)^{⊗e})`
(`V = A^{⊕(N+1)}`, `τ` the tautological section) along a morphism `j : S → Tot V`: if `j, j₀ : S → Tot V` lie
over the same `C`-structure `b`, the coordinates of `j` are those of `j₀` multiplied by `a ∈ Γ(S, O_S)`, and
`j₀^*(F(τ)) = 0`, then `j^*(F(τ)) = 0`. This is the common core of the scalar action on the cone (`λ·z` stays
in the cone) and of the cone scaling action (`u·g` stays in the cone), at the variable level.

Proof (the standard homogeneity argument: `F_j` is homogeneous, so `F_j(λz) = λ^{d_j} F_j(z)`):
1. `evalHomogeneousAtSections_pullback`: `θ_e (j^*F(τ)) = F(j^*τ_0, …, j^*τ_N)`, `θ_e = pullbackTensorPowIso`.
2. Transport of coordinates `totalSpaceHomEquiv_coordinate_homMk`: the `i`-th coordinate of `Over.homMk j hb`
   is `θ(j^*τ_i)`, `θ = pullbackComp j π` followed by `pullbackCongr hb` (`totalSpaceHomEquiv_naturality_coordinate`
   plus `subst`).
3. The coordinate hypothesis gives `j^*τ_i = a • ψ(j₀^*τ_i)`, `ψ := θ₀.hom ≫ θ.inv` (the inverse of `θ` is linear).
4. Homogeneity `evalHomogeneousAtSections_smul_pow`: `F(a•x) = a^e • F(x)`; naturality
   `evalHomogeneousAtSections_map`: `F(ψ x) = ψ^{⊗e}(F x)` (`tensorPowMap`, layerwise from `tensorMap_section`).
5. Together: `F(j^*τ) = a^e • ψ^{⊗e}(F(j₀^*τ)) = a^e • ψ^{⊗e}(θ_e(j₀^*F(τ))) = 0`, and the inverse of `θ_e` gives
   `j^*F(τ) = 0`.

General lemmas proved along the way: `Modules.tensorPowMap` (functoriality of tensor powers in morphisms),
`evalHomogeneousAtSections_map`, `evalHomogeneousAtSections_smul_pow` (the same statement as
`evalHomogeneousAtSections_smul` of `ConeScalingAction`, which cannot be reused here because of the import
direction), `totalSpaceHomEquiv_coordinate_homMk`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Functoriality of tensor powers in morphisms of modules: `φ : L ⟶ L'` gives `L^{⊗e} ⟶ L'^{⊗e}` (following
the right-recursion of `tensorPow`: `e = 0` is the identity, `e + 1` is `tensorMap (tensorPowMap φ e) φ`). -/
noncomputable def AlgebraicGeometry.Scheme.Modules.tensorPowMap {X : AlgebraicGeometry.Scheme.{u}}
    {L L' : X.Modules} (φ : L ⟶ L') : (e : ℕ) →
      (AlgebraicGeometry.Scheme.Modules.tensorPow L e ⟶ AlgebraicGeometry.Scheme.Modules.tensorPow L' e)
  | 0 => CategoryTheory.CategoryStruct.id _
  | e + 1 => AlgebraicGeometry.Scheme.Modules.tensorMap
      (AlgebraicGeometry.Scheme.Modules.tensorPowMap φ e) φ

/-- Naturality of monomial sections in morphisms of modules: `φ(f_{g 0}) ⊗ ⋯ ⊗ φ(f_{g (e-1)}) = φ^{⊗e}(f_{g 0} ⊗ ⋯)`,
layerwise by `tensorMap_section`. -/
theorem evalHomogeneousAtSections.monomial_map {X : AlgebraicGeometry.Scheme.{u}} {L L' : X.Modules}
    (φ : L ⟶ L') {N : ℕ} (f : Fin (N + 1) → (L.val.obj (Opposite.op ⊤) : Type u)) (e : ℕ)
    (g : Fin e → Fin (N + 1)) :
    evalHomogeneousAtSections.monomial L' (fun i => (φ.val.app (Opposite.op ⊤)).hom (f i)) e g
      = ((AlgebraicGeometry.Scheme.Modules.tensorPowMap φ e).val.app (Opposite.op ⊤)).hom
          (evalHomogeneousAtSections.monomial L f e g) := by
  induction e with
  | zero => rfl
  | succ e ih =>
    simp only [evalHomogeneousAtSections.monomial]
    rw [ih (fun i => g i.castSucc)]
    exact (AlgebraicGeometry.Scheme.Modules.ModuleDualPowerContraction.tensorMap_section (U := ⊤) _ _ _ _).symm

/-- Naturality of homogeneous evaluation in morphisms of modules: `F(φ(f_0), …, φ(f_N)) = φ^{⊗e}(F(f_0, …, f_N))`. -/
theorem evalHomogeneousAtSections_map {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {L L' : X.Modules} [L.IsLineBundle] [L'.IsLineBundle]
    (φ : L ⟶ L') {N e : ℕ} (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous e)
    (f : Fin (N + 1) → (L.val.obj (Opposite.op ⊤) : Type u)) :
    evalHomogeneousAtSections L' F hF (fun i => (φ.val.app (Opposite.op ⊤)).hom (f i))
      = ((AlgebraicGeometry.Scheme.Modules.tensorPowMap φ e).val.app (Opposite.op ⊤)).hom
          (evalHomogeneousAtSections L F hF f) := by
  simp only [evalHomogeneousAtSections]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [evalHomogeneousAtSections.monomial_map φ f e _]
  exact (((AlgebraicGeometry.Scheme.Modules.tensorPowMap φ e).val.app (Opposite.op ⊤)).hom.map_smul _ _).symm

/-- Homogeneity (monomials): `monomial(a•f) = a^e • monomial(f)`, layerwise by `moduleTensorSection_smul`.
The same statement as `evalHomogeneousAtSections.monomial_smul` of `ConeScalingAction` (renamed because of the
import direction). -/
theorem evalHomogeneousAtSections.monomial_smul_pow {X : AlgebraicGeometry.Scheme.{u}} (A : X.Modules) {N : ℕ}
    (a : Γ(X, ⊤)) (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u)) (e : ℕ) (g : Fin e → Fin (N + 1)) :
    evalHomogeneousAtSections.monomial A (fun i => (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) • f i) e g
      = (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from a ^ e) • evalHomogeneousAtSections.monomial A f e g := by
  induction e with
  | zero =>
    simp only [evalHomogeneousAtSections.monomial, pow_zero]
    exact (one_smul _ _).symm
  | succ e ih =>
    simp only [evalHomogeneousAtSections.monomial]
    rw [ih (fun i => g i.castSucc), pow_succ]
    exact AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul (U := ⊤) _ _ _ _

/-- Homogeneity: for `F` a homogeneous polynomial of degree `e`, `F(a•f_0, …, a•f_N) = a^e • F(f_0, …, f_N)`.
The same statement as `evalHomogeneousAtSections_smul` of `ConeScalingAction` (renamed because of the import
direction). -/
theorem evalHomogeneousAtSections_smul_pow {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : X.Modules) [A.IsLineBundle]
    {N e : ℕ} (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous e)
    (a : Γ(X, ⊤)) (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u)) :
    evalHomogeneousAtSections A F hF (fun i => (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) • f i)
      = (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from a ^ e) • evalHomogeneousAtSections A F hF f := by
  have hcomm : ∀ (c : Γ(X, ⊤)) (m : ((AlgebraicGeometry.Scheme.Modules.tensorPow A e).val.obj (Opposite.op ⊤) : Type u)),
      (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from c) • ((show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from a ^ e) • m)
        = (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from a ^ e) • ((show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from c) • m) := by
    intro c m
    rw [smul_smul, smul_smul]
    congr 1
    exact mul_comm c (a ^ e)
  unfold evalHomogeneousAtSections
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [evalHomogeneousAtSections.monomial_smul_pow, hcomm]

/-- Transport of coordinates: `j : S → Tot(⨁A)`, `b : S → X`, `hb : j ≫ π = b`. The `ℓ`-th coordinate of
`Over.homMk j hb : Over.mk b ⟶ Tot` is `j^*τ_ℓ` (`τ_ℓ` the `ℓ`-th coordinate of the tautological section)
transported to `b^*(A ℓ)` by `pullbackComp j π` and `pullbackCongr hb`. -/
theorem AlgebraicGeometry.Scheme.totalSpaceHomEquiv_coordinate_homMk {X : AlgebraicGeometry.Scheme.{u}}
    {n : ℕ} (A : Fin n → X.Modules) [(⨁ A).IsLocallyFree] [(⨁ A).IsFiniteType]
    {S : AlgebraicGeometry.Scheme.{u}} (j : S ⟶ (AlgebraicGeometry.Scheme.totalSpace (⨁ A)).left)
    (b : S ⟶ X) (hb : j ≫ (AlgebraicGeometry.Scheme.totalSpace (⨁ A)).hom = b) (ℓ : Fin n) :
    (((AlgebraicGeometry.Scheme.Modules.pullback b).map (biproduct.π A ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (⨁ A) (CategoryTheory.Over.mk b)
          (CategoryTheory.Over.homMk j hb))
      = (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hb).hom.app (A ℓ)).val.app (Opposite.op ⊤)).hom
          ((((AlgebraicGeometry.Scheme.Modules.pullbackComp j
              (AlgebraicGeometry.Scheme.totalSpace (⨁ A)).hom).hom.app (A ℓ)).val.app (Opposite.op ⊤)).hom
            (sectionPullbackAlong j
              ((((AlgebraicGeometry.Scheme.Modules.pullback
                  (AlgebraicGeometry.Scheme.totalSpace (⨁ A)).hom).map (biproduct.π A ℓ)).val.app
                (Opposite.op ⊤)).hom
                (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (⨁ A)
                  (AlgebraicGeometry.Scheme.totalSpace (⨁ A)) (CategoryTheory.CategoryStruct.id _))))) := by
  subst hb
  have h := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality_coordinate A
    (AlgebraicGeometry.Scheme.totalSpace (⨁ A)) j (CategoryTheory.CategoryStruct.id _) ℓ
  rw [CategoryTheory.Category.comp_id] at h
  rw [h]
  rfl

/-- Scaling invariance of the pullback of the homogeneous equation section (core lemma, variable level):
`j, j₀ : S → Tot(A^{⊕(N+1)})` over the same `C`-structure `b` (`hb`, `hb₀`), every coordinate of `j` is the
corresponding coordinate of `j₀` times `a` (`hcoord`), and `j₀^*F(τ) = 0` (`h₀`); then `j^*F(τ) = 0`.
Proof route in the module docstring (5 steps). -/
theorem homogeneousEquationSection_pullback_eq_zero_of_coordinates_smul
    {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {e : ℕ} (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous e)
    {S : AlgebraicGeometry.Scheme.{u}} (b : S ⟶ C)
    (j₀ j : S ⟶ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).left)
    (hb₀ : j₀ ≫ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom = b)
    (hb : j ≫ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom = b)
    (a : Γ(S, ⊤))
    (hcoord : ∀ i : Fin (N + 1),
      (((AlgebraicGeometry.Scheme.Modules.pullback b).map
          (biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
          (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
            (CategoryTheory.Over.mk b) (CategoryTheory.Over.homMk j hb))
        = (show S.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) •
          (((AlgebraicGeometry.Scheme.Modules.pullback b).map
            (biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
            (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
              (CategoryTheory.Over.mk b) (CategoryTheory.Over.homMk j₀ hb₀)))
    (h₀ : sectionPullbackAlong j₀ (homogeneousEquationSection A N F hF) = 0) :
    sectionPullbackAlong j (homogeneousEquationSection A N F hF) = 0 := by
  let V := AlgebraicGeometry.Scheme.Modules.pow A (N + 1)
  let π := (AlgebraicGeometry.Scheme.totalSpace V).hom
  let _ : S.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨b ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  let _ : (AlgebraicGeometry.Scheme.totalSpace V).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨π ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have hj : j.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨by
    change j ≫ (π ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) =
      b ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    rw [← CategoryTheory.Category.assoc, hb]⟩
  have hj₀ : j₀.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨by
    change j₀ ≫ (π ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) =
      b ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    rw [← CategoryTheory.Category.assoc, hb₀]⟩
  -- the coordinates τ_i of the tautological section
  let τ : Fin (N + 1) → (((AlgebraicGeometry.Scheme.Modules.pullback π).obj A).val.obj (Opposite.op ⊤) : Type u) :=
    fun i => ((AlgebraicGeometry.Scheme.Modules.pullback π).map
        (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (AlgebraicGeometry.Scheme.totalSpace V)
        (CategoryTheory.CategoryStruct.id _))
  have hpull : ∀ (g : S ⟶ (AlgebraicGeometry.Scheme.totalSpace V).left)
      [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))],
      ((AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso g
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) e).hom.val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong g (homogeneousEquationSection A N F hF))
        = evalHomogeneousAtSections
            ((AlgebraicGeometry.Scheme.Modules.pullback g).obj ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A))
            F hF (fun i => sectionPullbackAlong g (τ i)) := by
    intro g _
    exact evalHomogeneousAtSections_pullback g ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) F hF τ
  -- the transport isomorphisms
  let θ₀ : (AlgebraicGeometry.Scheme.Modules.pullback j₀).obj ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback b).obj A :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp j₀ π).app A ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr hb₀).app A
  let θ : (AlgebraicGeometry.Scheme.Modules.pullback j).obj ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback b).obj A :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp j π).app A ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr hb).app A
  have hc₀ : ∀ i, (((AlgebraicGeometry.Scheme.Modules.pullback b).map
          (biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
          (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk b) (CategoryTheory.Over.homMk j₀ hb₀))
        = (θ₀.hom.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong j₀ (τ i)) := fun i =>
    AlgebraicGeometry.Scheme.totalSpaceHomEquiv_coordinate_homMk (fun _ : Fin (N + 1) => A) j₀ b hb₀ i
  have hc : ∀ i, (((AlgebraicGeometry.Scheme.Modules.pullback b).map
          (biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
          (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk b) (CategoryTheory.Over.homMk j hb))
        = (θ.hom.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong j (τ i)) := fun i =>
    AlgebraicGeometry.Scheme.totalSpaceHomEquiv_coordinate_homMk (fun _ : Fin (N + 1) => A) j b hb i
  have hinv : ∀ x, (θ.inv.val.app (Opposite.op ⊤)).hom ((θ.hom.val.app (Opposite.op ⊤)).hom x) = x := by
    intro x
    have h := congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom x) θ.hom_inv_id
    exact h
  have hτ : ∀ i, sectionPullbackAlong j (τ i)
      = (show S.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) •
        ((θ₀.hom ≫ θ.inv).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong j₀ (τ i)) := by
    intro i
    have h1 := hcoord i
    rw [hc i, hc₀ i] at h1
    calc sectionPullbackAlong j (τ i)
        = (θ.inv.val.app (Opposite.op ⊤)).hom ((θ.hom.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong j (τ i))) :=
          (hinv _).symm
      _ = (θ.inv.val.app (Opposite.op ⊤)).hom ((show S.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) •
            (θ₀.hom.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong j₀ (τ i))) := by rw [h1]
      _ = (show S.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) •
            (θ.inv.val.app (Opposite.op ⊤)).hom ((θ₀.hom.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong j₀ (τ i))) :=
          map_smul _ _ _
      _ = (show S.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) •
            ((θ₀.hom ≫ θ.inv).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong j₀ (τ i)) := rfl
  have heval : evalHomogeneousAtSections
      ((AlgebraicGeometry.Scheme.Modules.pullback j).obj ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A))
      F hF (fun i => sectionPullbackAlong j (τ i)) = 0 := by
    have hfun : (fun i => sectionPullbackAlong j (τ i)) = fun i =>
        (show S.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) •
          ((θ₀.hom ≫ θ.inv).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong j₀ (τ i)) := funext hτ
    rw [hfun, evalHomogeneousAtSections_smul_pow, evalHomogeneousAtSections_map, ← hpull j₀, h₀, map_zero,
      map_zero, smul_zero]
  have h1 := hpull j
  rw [heval] at h1
  have h2 : ∀ x, ((AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso j
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) e).inv.val.app (Opposite.op ⊤)).hom
        (((AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso j
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) e).hom.val.app (Opposite.op ⊤)).hom x) = x := by
    intro x
    have h := congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom x)
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso j
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) e).hom_inv_id
    exact h
  rw [← h2 (sectionPullbackAlong j (homogeneousEquationSection A N F hF)), h1, map_zero]

end
