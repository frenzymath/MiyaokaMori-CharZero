import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOfNowhereZeroTuple
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SeedHomogeneousConeFractions
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveChartEquationEvaluation

/-! # Equations of `X` vanish on tuples whose projectivization factors through `X`

Statement. Let `P` be a nowhere-simultaneously-vanishing tuple of sections of a line bundle `M` on `V`, and
suppose its projectivization morphism `V → P^N` equals `g ≫ e.emb` for a closed embedding `e : X → P^N`. If the
homogeneous polynomial `F` lies in the homogeneous vanishing ideal of `X`, then evaluating `F` at the sections
`P` gives the zero section of `M^{⊗d}`.

Proof.
1. Cover `V` by the opens `V_ℓ = {P_ℓ ≠ 0}` (`hP`); by the separation property of sheaves
   (`TopCat.Sheaf.eq_of_locally_eq'`) it suffices to show that `F(P)` restricts to zero on each `V_ℓ`.
2. On `V_ℓ`, `P_ℓ` is a frame and `P_j| = r_{ℓj} • P_ℓ|` (`projectivizationRatio_smul`). Expanding the
   definition of `evalHomogeneousAtSections` (a sum of coefficient • monomial) and using the bilinearity and
   restriction compatibility of `moduleTensorSection` gives the local formula
   `F(P)|_{V_ℓ} = F(r_{ℓ0},…,r_{ℓN}) • P_ℓ|^{⊗d}` (`ProjectiveFactorEquationVanishes.res_evalHomogeneousAtSections`).
3. The coefficient `F(r_{ℓ·})` is `projectivizationChartEval P ℓ F` (via `topIso`). The chart morphism
   `V_ℓ → P^N` is `Proj.fromOfGlobalSections`, which equals `chartMap ≫ D₊(X_ℓ).ι`
   (`ProjectiveSpaceOverChart.chartMap_ι`) and also `V_ℓ.ι ≫ g ≫ e.emb` (`hproj`).
   `F ∈ projectiveVanishingIdeal` means that `F/X_ℓ^d` lies in the kernel ideal of `e.emb` over `D₊(X_ℓ)`
   (`projectiveVanishingIdeal_le_chartKernel`), so its pullback along `V_ℓ → X → P^N` is `0`;
   the pullback along `chartMap` is `chartEvaluation (F/X_ℓ^d)`
   (`ProjectiveFactorEquationVanishes.chartMap_appTop_section`), and
   `chartEvaluation (F/X_ℓ^d) · ψ(X_ℓ)^d = ψ(F)` with `ψ(X_ℓ) = 1`
   (`AlgebraicGeometry.Proj.ProjectiveChartEquationEvaluation.chartEvaluation_mk_mul`). Hence `ψ(F) = 0`
   (`ProjectiveFactorEquationVanishes.projectivizationChartEval_eq_zero`).
4. `0 • P_ℓ^{⊗d} = 0`.

Sources: §2 of the paper (Section 2), the homogeneous ideal `I_X` and the equations of the cone;
Stacks 01M3 (the standard open cover of `Proj` and sections over `D₊(f)` as the degree-zero homogeneous
localization).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every homogeneous equation in the projective vanishing ideal dehomogenizes into the
scheme-theoretic kernel on each standard chart of the given embedding. -/
private theorem projectiveVanishingIdeal_le_chartKernel
    {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (i : Fin (N + 1)) :
    (projectiveVanishingIdeal e.emb.ker).toIdeal ≤
      (AlgebraicGeometry.Proj.ProjectiveEmbedding.chartKernelAway e.emb i).comap
        (AlgebraicGeometry.Proj.embeddingChartLocalizationMap k N i) := by
  change Ideal.span (⋃ d, projectiveVanishingIdealDeg e.emb.ker d) ≤ _
  apply Ideal.span_le.mpr
  intro G hG
  obtain ⟨q, hG⟩ := Set.mem_iUnion.mp hG
  rcases hG with ⟨hhom, hsections⟩
  change AlgebraicGeometry.Proj.embeddingChartLocalizationMap k N i G ∈
    AlgebraicGeometry.Proj.ProjectiveEmbedding.chartKernelAway e.emb i
  rw [AlgebraicGeometry.Proj.SeedHomogeneousConeFractions.embeddingChartLocalizationMap_homogeneous
    k N i hhom]
  exact hsections i

namespace ProjectiveFactorEquationVanishes

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

/-- Restriction of `F(f_0,…,f_N)` to an open `U` on which every `f_j` is a multiple `r_j • s` of one
section `s`: it equals `F(r_0,…,r_N) • s^{⊗d}` (coefficients through the restricted structure map). -/
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

set_option backward.isDefEq.respectTransparency false in
/-- **Chart vanishing.** If the projectivization of `P` factors as `g ≫ e.emb`, then on the chart
`V_ℓ = {P_ℓ ≠ 0}` the dehomogenized equation `F(P_0/P_ℓ, …, P_N/P_ℓ)` is zero. Proof: the chart
morphism `V_ℓ → P^N` is `chartMap ≫ ι` and equals `V_ℓ.ι ≫ g ≫ e.emb`; the section
`F/X_ℓ^d ∈ Γ(D₊(X_ℓ), O)` lies in the kernel of `e.emb` (as `F` is in the vanishing ideal), so its
pullback along `V_ℓ → X → P^N` is zero; but along `chartMap` it is `chartEvaluation (F/X_ℓ^d)`,
and `chartEvaluation (F/X_ℓ^d) · ψ(X_ℓ)^d = ψ(F)` with `ψ(X_ℓ) = 1`. -/
theorem projectivizationChartEval_eq_zero {k : Type u} [Field k]
    {V X : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N d : ℕ}
    (e : ProjectiveEmbedding k X N) (g : V ⟶ X)
    (M : V.Modules) [M.IsLineBundle]
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ i, ¬ IsZeroAt (P i) v)
    (hproj : projectivizationMorphism (k := k) M P hP = g ≫ e.emb)
    (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous d)
    (hmem : F ∈ (projectiveVanishingIdeal e.emb.ker).toIdeal) (ℓ : Fin (N + 1)) :
    projectivizationChartEval (k := k) P ℓ F = 0 := by
  have hunit : IsUnit (projectivizationChartEval (k := k) P ℓ (MvPolynomial.X ℓ)) := by
    rw [projectivizationChartEval_X_self]; exact isUnit_one
  let U : (ProjectiveSpace N k).Opens := ProjectiveSpaceOver.chart N k ℓ
  let T := (projectivizationChart P ℓ).toScheme
  let χ : T ⟶ U.toScheme := ProjectiveSpaceOverChart.chartMap T N
    (projectivizationChartEval (k := k) P ℓ) ℓ hunit
  let z := AlgebraicGeometry.Proj.embeddingChartLocalizationMap k N ℓ F
  let s : Γ(ProjectiveSpace N k, U) := (AlgebraicGeometry.Proj.ProjectiveEmbedding.chartIso k N ℓ).hom z
  -- the chart morphism factors through `X`
  have hφ : χ ≫ U.ι = (projectivizationChart P ℓ).ι ≫ (g ≫ e.emb) := by
    rw [← hproj, projectivizationMorphism_restrict]
    exact ProjectiveSpaceOverChart.chartMap_ι _ _ _
      (projectivizationChartEval_irrelevant_map_eq_top (k := k) P ℓ) ℓ hunit
  -- `F / X_ℓ^d` lies in the scheme-theoretic kernel on the chart
  have hz : z ∈ AlgebraicGeometry.Proj.ProjectiveEmbedding.chartKernelAway e.emb ℓ :=
    projectiveVanishingIdeal_le_chartKernel e ℓ hmem
  have hsec : e.emb.app U s = 0 := by
    rw [← AlgebraicGeometry.Proj.ProjectiveEmbeddingChartFactorization.ker_sectionMap] at hz
    exact RingHom.mem_ker.mp hz
  have hle : (⊤ : T.Opens) ≤ (χ ≫ U.ι) ⁻¹ᵁ U := by
    rw [AlgebraicGeometry.Scheme.Hom.comp_preimage, AlgebraicGeometry.Scheme.Opens.ι_preimage_self]
    exact le_top
  -- pulling `s` back along the factorization gives zero
  have h2 : ∀ (Φ : T ⟶ ProjectiveSpace N k), (projectivizationChart P ℓ).ι ≫ (g ≫ e.emb) = Φ →
      ∀ hle : (⊤ : T.Opens) ≤ Φ ⁻¹ᵁ U, Φ.appLE U ⊤ hle s = 0 := by
    rintro Φ rfl hle
    rw [AlgebraicGeometry.Scheme.Hom.comp_appLE, CommRingCat.comp_apply,
      AlgebraicGeometry.Scheme.Hom.comp_app, CommRingCat.comp_apply, hsec, map_zero, map_zero]
  -- pulling `s` back along the chart map evaluates the fraction
  have h1 : (χ ≫ U.ι).appLE U ⊤ hle s =
      ProjectiveSpaceOverChart.chartEvaluation N
        (projectivizationChartEval (k := k) P ℓ) ℓ hunit z := by
    rw [← chartMap_appTop_section, ← AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE χ U.ι U ⊤ ⊤
      (by rw [AlgebraicGeometry.Scheme.Opens.ι_preimage_self]) le_top, CommRingCat.comp_apply]
    have hs' : U.ι.appLE U ⊤ (by rw [AlgebraicGeometry.Scheme.Opens.ι_preimage_self]) s =
        U.topIso.inv (AlgebraicGeometry.Proj.awayToSection (AlgebraicGeometry.Proj.projectiveGrading k N)
          (MvPolynomial.X ℓ) z) := by
      rw [AlgebraicGeometry.Scheme.Opens.ι_appLE, AlgebraicGeometry.Scheme.Opens.topIso_inv]
      exact presheaf_map_congr_hom _ _ _
    rw [hs']
    exact congrArg (fun m => (ConcreteCategory.hom m) (U.topIso.inv
      (AlgebraicGeometry.Proj.awayToSection (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X ℓ) z)))
      (AlgebraicGeometry.Scheme.Hom.appLE_eq_app χ (U := ⊤))
  have h0 : ProjectiveSpaceOverChart.chartEvaluation N
      (projectivizationChartEval (k := k) P ℓ) ℓ hunit z = 0 :=
    h1.symm.trans (h2 _ hφ.symm hle)
  -- conclude: `chartEvaluation (F/X_ℓ^d) * ψ(X_ℓ)^d = ψ F`
  have hzmk : z = HomogeneousLocalization.Away.mk (AlgebraicGeometry.Proj.projectiveGrading k N)
      (AlgebraicGeometry.Proj.ProjectiveChartEquationEvaluation.X_mem_projectiveGrading N ℓ) d F
      (by simpa using hF) :=
    AlgebraicGeometry.Proj.SeedHomogeneousConeFractions.embeddingChartLocalizationMap_homogeneous
      k N ℓ hF
  have hmul := AlgebraicGeometry.Proj.ProjectiveChartEquationEvaluation.chartEvaluation_mk_mul N
    (projectivizationChartEval (k := k) P ℓ) ℓ hunit F d hF
  rw [← hzmk, h0, zero_mul] at hmul
  exact hmul.symm

end ProjectiveFactorEquationVanishes

open ProjectiveFactorEquationVanishes in
set_option backward.isDefEq.respectTransparency false in
/-- **Equations of `X ⊂ P^N` vanish on any tuple whose projectivization factors through `X`.**
If the projectivization `V → P^N` of a nowhere-simultaneously-vanishing tuple `P` of sections of a
line bundle `M` equals `g ≫ e.emb` for some `g : V ⟶ X`, then every homogeneous `F` in the
projective vanishing ideal of `X` satisfies `F(P_0, …, P_N) = 0` in `Γ(V, M^{⊗d})`.
Source: §2 of the paper (Section 2). Proof: see the module docstring (sheaf locality over the
charts `{P_ℓ ≠ 0}`, the local formula `res_evalHomogeneousAtSections`, and the chart vanishing
`projectivizationChartEval_eq_zero`). -/
theorem evalHomogeneousAtSections_eq_zero_of_projectivization_factors
    {k : Type u} [Field k] {V X : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N d : ℕ}
    (e : ProjectiveEmbedding k X N) (g : V ⟶ X)
    (M : V.Modules) [M.IsLineBundle]
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ i, ¬ IsZeroAt (P i) v)
    (hproj : projectivizationMorphism (k := k) M P hP = g ≫ e.emb)
    (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous d)
    (hmem : F ∈ (projectiveVanishingIdeal e.emb.ker).toIdeal) :
    evalHomogeneousAtSections M F hF P = 0 := by
  have hcov : (⊤ : V.Opens) ≤ iSup (projectivizationChart P) := by
    intro v _
    obtain ⟨ℓ, hℓ⟩ := hP v
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨ℓ, hℓ⟩
  refine TopCat.Sheaf.eq_of_locally_eq'
    ⟨(AlgebraicGeometry.Scheme.Modules.tensorPow M d).presheaf,
      (AlgebraicGeometry.Scheme.Modules.tensorPow M d).isSheaf⟩
    (projectivizationChart P) ⊤ (fun ℓ => homOfLE le_top) hcov _ _ (fun ℓ => ?_)
  rw [map_zero]
  have hf : ∀ j, M.presheaf.map (homOfLE (le_top : projectivizationChart P ℓ ≤ ⊤)).op (P j) =
      projectivizationRatio P ℓ j •
        M.presheaf.map (homOfLE (le_top : projectivizationChart P ℓ ≤ ⊤)).op (P ℓ) := by
    intro j
    have h := projectivizationRatio_smul P ℓ j
    rw [AlgebraicGeometry.Scheme.Modules.res_self] at h
    exact h.symm
  rw [res_evalHomogeneousAtSections M F hF P (projectivizationChart P ℓ) _ _ hf]
  have hψ : MvPolynomial.eval₂
      ((V.presheaf.map (homOfLE (le_top : projectivizationChart P ℓ ≤ ⊤)).op).hom.comp
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom)
      (projectivizationRatio P ℓ) F =
      (projectivizationChart P ℓ).topIso.hom (projectivizationChartEval (k := k) P ℓ F) := by
    rw [projectivizationChartEval, projectivizationChartEvalOver, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
    refine congrArg₂ (fun (f : k →+* Γ(V, projectivizationChart P ℓ))
      (r : Fin (N + 1) → Γ(V, projectivizationChart P ℓ)) => MvPolynomial.eval₂ f r F) ?_ ?_
    · ext a
      show V.presheaf.map (homOfLE (le_top : projectivizationChart P ℓ ≤ ⊤)).op
          (((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
            (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop) a) =
        (projectivizationChart P ℓ).topIso.hom ((projectivizationChart P ℓ).ι.appTop
          (((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
            (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop) a))
      refine (presheaf_map_congr_hom (X := V) (homOfLE le_top)
        (eqToHom (projectivizationChart P ℓ).ι_image_top.symm ≫
          homOfLE (le_top : (projectivizationChart P ℓ).ι ''ᵁ ⊤ ≤ ⊤)) _).trans ?_
      rw [op_comp, Functor.map_comp, CommRingCat.comp_apply]
      rfl
    · funext j
      exact (Iso.inv_hom_id_apply (projectivizationChart P ℓ).topIso _).symm
  rw [hψ, projectivizationChartEval_eq_zero e g M P hP hproj F hF hmem ℓ, map_zero, zero_smul]


end
