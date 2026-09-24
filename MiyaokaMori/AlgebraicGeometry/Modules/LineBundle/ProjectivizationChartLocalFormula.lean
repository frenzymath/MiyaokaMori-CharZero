import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousAtSections
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.NonvanishingLocusTensorSection
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveCoordinateRatio

/-! # Local formulas for the charts of a projectivization

Chart-level bookkeeping for the projectivization `V → P^N` of a nowhere-simultaneously-vanishing
tuple `P` of sections of a line bundle `M`, placed **below** `ProjectivizationOfNowhereZeroTuple` so that
module can use it.

1. **Local formula** (`res_evalHomogeneousAtSections`): on an open `U` where every `f_j = r_j • s`,
   `F(f_0,…,f_N)|_U = F(r_0,…,r_N) • s^{⊗d}` (`monomialOn`).
2. **Tensor powers of a frame are torsion-free** (`eq_zero_of_smul_monomialOn_eq_zero`):
   if `s` is a frame of `M` on `U` then `c • s^{⊗d} = 0 ⇒ c = 0`. Proof through stalks: a frame gives
   `M_y ≃ 𝒪_y` with `s_y ↦ 1` (`IsFrame.stalkEquiv`); Stacks 01CB `(L ⊗ N)_y ≅ L_y ⊗ N_y` turns two such
   equivalences into one for `L ⊗ N` sending `(e ⊗ f)_y ↦ 1`; induct on `d` (the `d = 0` case is the
   structure sheaf with frame `1`); finally a section with all germs zero is zero.
3. **Chart map on sections** (`chartMap_appTop_section`): pulling back the section of `D₊(X_j)` given
   by a degree-zero fraction `z` along `chartMap` evaluates the fraction.
4. `eval₂_res_eq_topIso_hom`: the coefficient map of the local formula is `topIso.hom` of the
   chart evaluation `eval₂Hom` used to define the chart morphisms.

Items 1 and 3 also appear in `ProjectiveFactorEquationVanishes` (a module *above*
`ProjectivizationOfNowhereZeroTuple`, which therefore cannot be imported there); they are reproduced here
under the namespace `ProjectivizationChartLocalFormula`.

References: the paper (the projectivization factors through `X` when the equations vanish); Stacks 01CB
(stalk of a tensor product).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjectivizationChartLocalFormula

/-! ## 1. Monomial sections over an open and the local formula -/

/-- Monomial section over an open `U`: `f_{g 0} ⊗ ⋯ ⊗ f_{g (e-1)} ∈ Γ(U, A^{⊗e})`, with the same
right-nested recursion as `evalHomogeneousAtSections.monomial`. -/
noncomputable def monomialOn {X : AlgebraicGeometry.Scheme.{u}} (A : X.Modules) {N : ℕ}
    (U : X.Opens) (f : Fin (N + 1) → Γ(A, U)) :
    (e : ℕ) → (Fin e → Fin (N + 1)) → Γ(AlgebraicGeometry.Scheme.Modules.tensorPow A e, U)
  | 0, _ => (1 : X.ringCatSheaf.obj.obj (Opposite.op U))
  | e + 1, g =>
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (monomialOn A U f e (fun i => g i.castSucc)) (f (g (Fin.last e)))

theorem monomialOn_const {X : AlgebraicGeometry.Scheme.{u}} (A : X.Modules) {N : ℕ}
    (U : X.Opens) (s : Γ(A, U)) :
    ∀ (e : ℕ) (q : Fin e → Fin (N + 1)),
      monomialOn A U (fun _ => s) e q = monomialOn A U (fun _ => s) e (fun _ => (0 : Fin (N + 1)))
  | 0, _ => rfl
  | e + 1, _ =>
      congrArg (fun m => AlgebraicGeometry.Scheme.Modules.moduleTensorSection m s) (monomialOn_const A U s e _)

theorem monomialOn_smul {X : AlgebraicGeometry.Scheme.{u}} (A : X.Modules) {N : ℕ}
    (U : X.Opens) (r : Fin (N + 1) → Γ(X, U)) (s : Γ(A, U)) :
    ∀ (e : ℕ) (q : Fin e → Fin (N + 1)),
      monomialOn A U (fun j => r j • s) e q = (∏ i, r (q i)) • monomialOn A U (fun _ => s) e q
  | 0, _ => by
      rw [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
      rfl
  | e + 1, q => by
      show AlgebraicGeometry.Scheme.Modules.moduleTensorSection (monomialOn A U (fun j => r j • s) e (fun i => q i.castSucc))
          (r (q (Fin.last e)) • s) = _
      rw [monomialOn_smul A U r s e, AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul, Fin.prod_univ_castSucc]
      rfl

theorem monomial_res {X : AlgebraicGeometry.Scheme.{u}} (A : X.Modules) {N : ℕ}
    (U : X.Opens) (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u)) :
    ∀ (e : ℕ) (q : Fin e → Fin (N + 1)),
      (AlgebraicGeometry.Scheme.Modules.tensorPow A e).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          (evalHomogeneousAtSections.monomial A f e q) =
        monomialOn A U (fun j => A.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (f j)) e q
  | 0, _ => by
      show X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (1 : Γ(X, ⊤)) = (1 : Γ(X, U))
      exact map_one _
  | e + 1, q => by
      refine (AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict
        (M := AlgebraicGeometry.Scheme.Modules.tensorPow A e) (N := A)
        (homOfLE (le_top : U ≤ ⊤))
        (evalHomogeneousAtSections.monomial A f e (fun i => q i.castSucc))
        (f (q (Fin.last e)))).trans ?_
      exact congrArg (fun m => AlgebraicGeometry.Scheme.Modules.moduleTensorSection m
        (A.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (f (q (Fin.last e)))))
        (monomial_res A U f e (fun i => q i.castSucc))

/-- The product of `g` over the sorted index list of an exponent `α` is `∏ j ∈ α.support, g j ^ α j`. -/
theorem prod_indices {N e : ℕ} {R : Type u} [CommMonoid R] (g : Fin (N + 1) → R)
    (α : Fin (N + 1) →₀ ℕ) (hα : Finsupp.weight 1 α = e) :
    (∏ i : Fin e, g (evalHomogeneousAtSections.indices α hα i)) = ∏ j ∈ α.support, g j ^ α j := by
  let s := α.toMultiset.sort (· ≤ ·)
  have hslen : s.length = e := by
    dsimp [s]
    rw [Multiset.length_sort, Finsupp.card_toMultiset, ← hα, Finsupp.weight_apply]
    simp [Finsupp.sum]
  have hprod : (∏ i : Fin e, g (s.get (i.cast hslen.symm))) = (s.map g).prod := by
    calc
      (∏ i : Fin e, g (s.get (i.cast hslen.symm))) =
          ∏ j : Fin s.length, g (s.get j) := by
        apply Fintype.prod_equiv (finCongr hslen.symm)
        intro i
        rfl
      _ = (s.map g).prod := Fin.prod_univ_fun_getElem s g
  have hprod' : (∏ i : Fin e, g (evalHomogeneousAtSections.indices α hα i)) = (s.map g).prod := by
    simpa [evalHomogeneousAtSections.indices, s] using hprod
  have hsort : (s.map g).prod = (α.toMultiset.map g).prod := by
    have hs : (s : Multiset (Fin (N + 1))) = α.toMultiset := by
      dsimp [s]
      exact Multiset.sort_eq _ _
    have hmap := congrArg (Multiset.map g) hs
    rw [← Multiset.prod_coe]
    rw [← Multiset.map_coe]
    exact congrArg Multiset.prod hmap
  rw [hprod', hsort, Finset.prod_multiset_map_count, Finsupp.toFinset_toMultiset]
  simp only [Finsupp.count_toMultiset]

/-- **Local formula.** Restriction of `F(f_0,…,f_N)` to an open `U` on which every `f_j` is a multiple
`r_j • s` of one section `s`: it equals `F(r_0,…,r_N) • s^{⊗d}` (coefficients through the restricted
structure map). -/
theorem res_evalHomogeneousAtSections {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : X.Modules) [A.IsLineBundle]
    {N d : ℕ} (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous d)
    (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u)) (U : X.Opens) (s : Γ(A, U))
    (r : Fin (N + 1) → Γ(X, U))
    (hf : ∀ j, A.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (f j) = r j • s) :
    (AlgebraicGeometry.Scheme.Modules.tensorPow A d).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (evalHomogeneousAtSections A F hF f) =
      MvPolynomial.eval₂ ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp
          ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
            (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom) r F •
        monomialOn A (N := N) U (fun _ => s) d (fun _ => 0) := by
  simp only [evalHomogeneousAtSections]
  rw [MvPolynomial.eval₂_eq, ← F.support.sum_attach, Finset.sum_smul]
  erw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  refine (AlgebraicGeometry.Scheme.Modules.map_smul
    (AlgebraicGeometry.Scheme.Modules.tensorPow A d) (homOfLE (le_top : U ≤ ⊤)) _ _).trans ?_
  rw [monomial_res]
  simp only [hf]
  rw [monomialOn_smul, monomialOn_const, prod_indices, smul_smul]
  rfl

/-! ## 2. Tensor powers of a frame are torsion-free (through stalks) -/

/-- If some `𝒪_y`-linear equivalence `Θ : P_y ≃ 𝒪_y` sends the germ of `m` to `1`, then
`c • m_y = 0 ⇒ c = 0`. -/
theorem germ_eq_zero_of_smul_germ_eq_zero {X : AlgebraicGeometry.Scheme.{u}} {P : X.Modules}
    {W : X.Opens} {m : Γ(P, W)} {y : X} (hy : y ∈ W)
    (Θ : P.presheaf.stalk y ≃ₗ[X.presheaf.stalk y] X.presheaf.stalk y)
    (hΘ : Θ (P.presheaf.germ W y hy m) = 1) (c : X.presheaf.stalk y)
    (hc : c • P.presheaf.germ W y hy m = 0) : c = 0 := by
  have h := congrArg Θ hc
  rw [map_smul, hΘ, smul_eq_mul, mul_one, map_zero] at h
  exact h

/-- A section `m` whose germ is a free generator at every point of `W` (witnessed by linear
equivalences `P_y ≃ 𝒪_y`, `m_y ↦ 1`) is torsion-free: `r • m = 0 ⇒ r = 0`. Proof: the germs of `r`
all vanish (`germ_eq_zero_of_smul_germ_eq_zero`), so `r = 0` by the sheaf axiom
(`TopCat.Presheaf.section_ext`). -/
theorem eq_zero_of_smul_eq_zero_of_stalkEquiv {X : AlgebraicGeometry.Scheme.{u}} {P : X.Modules}
    {W : X.Opens} (m : Γ(P, W))
    (hst : ∀ (y : X) (hy : y ∈ W),
      ∃ Θ : P.presheaf.stalk y ≃ₗ[X.presheaf.stalk y] X.presheaf.stalk y,
        Θ (P.presheaf.germ W y hy m) = 1)
    (r : Γ(X, W)) (hr : r • m = 0) : r = 0 := by
  apply TopCat.Presheaf.section_ext X.sheaf W r 0
  intro y hy
  obtain ⟨Θ, hΘ⟩ := hst y hy
  show X.presheaf.germ W y hy r = X.presheaf.germ W y hy 0
  rw [map_zero]
  apply germ_eq_zero_of_smul_germ_eq_zero hy Θ hΘ
  rw [← AlgebraicGeometry.Scheme.Modules.germ_smul', hr, map_zero]

/-- A frame gives the stalk equivalence `M_y ≃ 𝒪_y`, `e_y ↦ 1` (inverse of `IsFrame.stalkEquiv`). -/
theorem exists_stalkEquiv_of_isFrame {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules}
    {W : X.Opens} {e : Γ(M, W)} (hf : AlgebraicGeometry.Scheme.Modules.IsFrame M W e) {y : X}
    (hy : y ∈ W) :
    ∃ Θ : M.presheaf.stalk y ≃ₗ[X.presheaf.stalk y] X.presheaf.stalk y,
      Θ (M.presheaf.germ W y hy e) = 1 :=
  ⟨(hf.stalkEquiv hy).symm, by
    rw [LinearEquiv.symm_apply_eq, AlgebraicGeometry.Scheme.Modules.IsFrame.stalkEquiv_apply,
      one_smul]⟩

/-- **Stacks 01CB at the level of generators.** Given `Θ₁ : L_y ≃ 𝒪_y` with `e_y ↦ 1` and
`Θ₂ : N_y ≃ 𝒪_y` with `f_y ↦ 1`, the composite
`(L ⊗ N)_y ≅ L_y ⊗ N_y ≅ 𝒪_y ⊗ 𝒪_y ≅ 𝒪_y` sends `(e ⊗ f)_y` to `1`
(same construction as `IsFrame.tensorStalkEquivOfFrames`, with arbitrary witnesses in place of the
frame equivalences). -/
theorem exists_stalkEquiv_moduleTensorSection {X : AlgebraicGeometry.Scheme.{u}}
    {L N : X.Modules} {W : X.Opens} {e : Γ(L, W)} {f : Γ(N, W)} {y : X} (hy : y ∈ W)
    (Θ₁ : L.presheaf.stalk y ≃ₗ[X.presheaf.stalk y] X.presheaf.stalk y)
    (h₁ : Θ₁ (L.presheaf.germ W y hy e) = 1)
    (Θ₂ : N.presheaf.stalk y ≃ₗ[X.presheaf.stalk y] X.presheaf.stalk y)
    (h₂ : Θ₂ (N.presheaf.germ W y hy f) = 1) :
    ∃ Θ : (AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.stalk y ≃ₗ[X.presheaf.stalk y]
        X.presheaf.stalk y,
      Θ ((AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ W y hy
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection e f)) = 1 := by
  refine ⟨AlgebraicGeometry.Scheme.Modules.moduleStalkLinearEquiv X y
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L N) ≪≫ₗ
    AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv L N y ≪≫ₗ
    TensorProduct.congr Θ₁ Θ₂ ≪≫ₗ
    TensorProduct.lid (X.presheaf.stalk y) (X.presheaf.stalk y), ?_⟩
  have step1 : AlgebraicGeometry.Scheme.Modules.moduleStalkLinearEquiv X y
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L N)
      ((AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ W y hy
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection e f)) =
      (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) L N).presheaf.germ W y hy
        (AlgebraicGeometry.Scheme.Modules.tensorSections L N W e f) :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkLinearEquiv_germ X y
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L N) W hy
      (AlgebraicGeometry.Scheme.Modules.moduleTensorSection e f)
  have step2 : AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv L N y
      ((CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) L N).presheaf.germ W y hy
        (AlgebraicGeometry.Scheme.Modules.tensorSections L N W e f)) =
      (L.presheaf.germ W y hy) e ⊗ₜ[X.presheaf.stalk y] (N.presheaf.germ W y hy) f :=
    AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv_germ_tensorSections L N y W hy e f
  simp only [LinearEquiv.trans_apply]
  rw [step1, step2, TensorProduct.congr_tmul, h₁, h₂, TensorProduct.lid_tmul, one_smul]

/-- `1` is a frame of the structure sheaf (as a module over itself) on any open. -/
theorem isFrame_unit_one {X : AlgebraicGeometry.Scheme.{u}} (U : X.Opens) :
    AlgebraicGeometry.Scheme.Modules.IsFrame (SheafOfModules.unit X.ringCatSheaf) U
      (1 : Γ(X, U)) := by
  intro W' h
  refine ⟨fun a b hab => ?_, fun x => ⟨x, ?_⟩⟩
  · change a * X.presheaf.map (homOfLE h).op (1 : Γ(X, U)) =
      b * X.presheaf.map (homOfLE h).op (1 : Γ(X, U)) at hab
    rwa [map_one, mul_one, mul_one] at hab
  · change (show Γ(X, W') from x) * X.presheaf.map (homOfLE h).op (1 : Γ(X, U)) =
      (show Γ(X, W') from x)
    rw [map_one, mul_one]

/-- Tensor powers of a frame are free generators on every stalk: for a frame `s` of `M` on `U` and
`y ∈ U`, there is `Θ : (M^{⊗d})_y ≃ 𝒪_y` with `(s^{⊗d})_y ↦ 1`. Induction on `d`
(`d = 0`: `isFrame_unit_one`; step: `exists_stalkEquiv_moduleTensorSection`). -/
theorem exists_stalkEquiv_monomialOn {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) {N : ℕ}
    (U : X.Opens) (s : Γ(M, U)) (hs : AlgebraicGeometry.Scheme.Modules.IsFrame M U s) {y : X}
    (hy : y ∈ U) :
    ∀ (d : ℕ) (q : Fin d → Fin (N + 1)),
      ∃ Θ : (AlgebraicGeometry.Scheme.Modules.tensorPow M d).presheaf.stalk y ≃ₗ[X.presheaf.stalk y]
          X.presheaf.stalk y,
        Θ ((AlgebraicGeometry.Scheme.Modules.tensorPow M d).presheaf.germ U y hy
          (monomialOn M U (fun _ => s) d q)) = 1
  | 0, _ => exists_stalkEquiv_of_isFrame (isFrame_unit_one U) hy
  | d + 1, q => by
      obtain ⟨Θ₁, h₁⟩ := exists_stalkEquiv_monomialOn M U s hs hy d (fun i => q i.castSucc)
      obtain ⟨Θ₂, h₂⟩ := exists_stalkEquiv_of_isFrame hs hy
      exact exists_stalkEquiv_moduleTensorSection hy Θ₁ h₁ Θ₂ h₂

/-- **Tensor powers of a frame are torsion-free**: `c • s^{⊗d} = 0 ⇒ c = 0` on `U`. -/
theorem eq_zero_of_smul_monomialOn_eq_zero {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)
    {N : ℕ} (U : X.Opens) (s : Γ(M, U)) (hs : AlgebraicGeometry.Scheme.Modules.IsFrame M U s)
    (d : ℕ) (q : Fin d → Fin (N + 1)) (r : Γ(X, U))
    (hr : r • monomialOn M U (fun _ => s) d q = 0) : r = 0 :=
  eq_zero_of_smul_eq_zero_of_stalkEquiv _ (fun y hy => exists_stalkEquiv_monomialOn M U s hs hy d q)
    r hr

/-! ## 3. The chart map on sections -/

/-- Two restriction maps of the structure sheaf between the same opens agree (the category of
opens is thin). -/
theorem presheaf_map_congr_hom {X : AlgebraicGeometry.Scheme.{u}} {A B : X.Opens}
    (m₁ m₂ : B ⟶ A) (x : Γ(X, A)) :
    X.presheaf.map m₁.op x = X.presheaf.map m₂.op x := by
  rw [Subsingleton.elim m₁ m₂]

set_option backward.isDefEq.respectTransparency.types false in
/-- Pulling back the section of `D₊(X_j)` given by a degree-zero fraction `z` along the chart map
of a tuple with `ψ(X_j)` invertible evaluates the fraction (generalizes
`ProjectiveSpaceOverChart.chartMap_appTop_ratio` from `X_i/X_j` to any `z`). -/
theorem chartMap_appTop_section {k : Type u} [Field k] (T : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (ψ : MvPolynomial (Fin (n + 1)) k →+* Γ(T, ⊤)) (j : Fin (n + 1))
    (hj : IsUnit (ψ (MvPolynomial.X j)))
    (z : HomogeneousLocalization.Away (AlgebraicGeometry.Proj.projectiveGrading k n) (MvPolynomial.X j)) :
    (ProjectiveSpaceOverChart.chartMap T n ψ j hj).appTop
        ((AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k n)
          (MvPolynomial.X j)).topIso.inv
          (AlgebraicGeometry.Proj.awayToSection (AlgebraicGeometry.Proj.projectiveGrading k n)
            (MvPolynomial.X j) z)) =
      ProjectiveSpaceOverChart.chartEvaluation n ψ j hj z := by
  let φ := ProjectiveSpaceOverChart.chartEvaluation n ψ j hj
  have hs : (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k n)
        (MvPolynomial.X j)).topIso.inv
      (AlgebraicGeometry.Proj.awayToSection (AlgebraicGeometry.Proj.projectiveGrading k n)
        (MvPolynomial.X j) z) =
      (AlgebraicGeometry.Proj.basicOpenIsoSpec (AlgebraicGeometry.Proj.projectiveGrading k n) (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X k j) Nat.zero_lt_one).hom.appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
          (AlgebraicGeometry.Proj.projectiveGrading k n) (MvPolynomial.X j)))).inv z) := by
    change _ = ((AlgebraicGeometry.Proj.basicOpenToSpec (AlgebraicGeometry.Proj.projectiveGrading k n)
      (MvPolynomial.X j)).app ⊤) _
    rw [AlgebraicGeometry.Proj.basicOpenToSpec_app_top]
    change _ = (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k n) _).topIso.inv
      (AlgebraicGeometry.Proj.awayToSection (AlgebraicGeometry.Proj.projectiveGrading k n) _
        ((AlgebraicGeometry.Scheme.ΓSpecIso _).hom ((AlgebraicGeometry.Scheme.ΓSpecIso _).inv z)))
    rw [Iso.inv_hom_id_apply]
  have hnat : (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)).appTop
      ((AlgebraicGeometry.Scheme.ΓSpecIso _).inv z) =
      (AlgebraicGeometry.Scheme.ΓSpecIso _).inv (φ z) := by
    simpa only [CommRingCat.comp_apply, CategoryTheory.comp_apply,
      CommRingCat.hom_ofHom, CommRingCat.of_carrier] using
      congrArg (fun h ↦ h z)
        (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
  rw [hs]
  change ((ProjectiveSpaceOverChart.chartMap T n ψ j hj) ≫
    (AlgebraicGeometry.Proj.basicOpenIsoSpec (AlgebraicGeometry.Proj.projectiveGrading k n) (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X k j) Nat.zero_lt_one).hom).appTop
    ((AlgebraicGeometry.Scheme.ΓSpecIso _).inv z) = φ z
  simp only [ProjectiveSpaceOverChart.chartMap, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hnat,
    AlgebraicGeometry.Scheme.toSpecΓ_appTop, Iso.inv_hom_id_apply]

/-! ## 4. The coefficient map of the local formula is the chart evaluation -/

set_option backward.isDefEq.respectTransparency false in
/-- `F(r_0,…,r_N)` computed in `Γ(V, W)` through the restricted structure map equals `topIso.hom` of
`F` evaluated by the chart evaluation `eval₂Hom (ΓSpecIso.inv ≫ (W.ι ≫ V ↘ Spec k).appTop) (topIso.inv ∘ r)`
on the open subscheme `W`. -/
theorem eval₂_res_eq_topIso_hom {k : Type u} [Field k] {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ} (W : V.Opens)
    (r : Fin (N + 1) → Γ(V, W)) (F : MvPolynomial (Fin (N + 1)) k) :
    MvPolynomial.eval₂
        ((V.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom.comp
          ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
            (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom) r F =
      W.topIso.hom (MvPolynomial.eval₂Hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (W.ι ≫ (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop).hom
        (fun j => W.topIso.inv.hom (r j)) F) := by
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  refine congrArg₂ (fun (f : k →+* Γ(V, W)) (r : Fin (N + 1) → Γ(V, W)) =>
    MvPolynomial.eval₂ f r F) ?_ ?_
  · ext a
    show V.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
        (((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop) a) =
      W.topIso.hom (W.ι.appTop
        (((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop) a))
    refine (presheaf_map_congr_hom (X := V) (homOfLE le_top)
      (eqToHom W.ι_image_top.symm ≫ homOfLE (le_top : W.ι ''ᵁ ⊤ ≤ ⊤)) _).trans ?_
    rw [op_comp, Functor.map_comp, CommRingCat.comp_apply]
    rfl
  · funext j
    exact (Iso.inv_hom_id_apply W.topIso _).symm

end ProjectivizationChartLocalFormula

end
