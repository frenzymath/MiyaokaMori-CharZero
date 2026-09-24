import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01nr

/-! # Chart sections of the twisting sheaf on a relative Proj

The comparison map `twistAffineHom U n : O(n)|_{π⁻¹U} ⟶ e_U^* O_U(n)` of Stacks 01NR is replaced by its
**restriction** version `chartSections S U n : O(n)|_{π⁻¹U} ⟶ O_U(n)|_{e_U}` (composing with the inverse of
`restrictFunctorIsoPullback e_U`). Its sections over `A ⊆ π⁻¹U` are the sections of the limit projection `twistπ`
(`chartSections_app`); consequently, for a principal refinement `W = D_U(f) ≤ U`, the `chartSections` of the two
charts are related through `twistπ_transition` (the transition map `θ` is pointwise `Localization.localRingHom`).
The identification of `twistAffineHom` with `chartSections` is `twistAffineHom_comp_eq_chartSections`.

Sources: Stacks 01NR, 01MX; Lemma 2.2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Under the adjunction `R_f ⊣ f_*` between restriction along an open immersion `f` and pushforward, the components
of `R_f T ⟶ Q` are given by those of its transpose `T ⟶ f_* Q`:
    `g.app A = (g^♭).app (f''A) ≫ Q(f⁻¹f''A) → Q(A)`. -/
theorem AlgebraicGeometry.Scheme.Modules.restrict_hom_app_eq_homEquiv_app
    {Y P : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ P) [AlgebraicGeometry.IsOpenImmersion f]
    {T : P.Modules} {Q : Y.Modules} (g : T.restrict f ⟶ Q) (A : Y.Opens) :
    g.app A =
      ((AlgebraicGeometry.Scheme.Modules.restrictAdjunction f).homEquiv T Q g).app (f ''ᵁ A) ≫
        Q.presheaf.map (CategoryTheory.eqToHom (f.preimage_image_eq A).symm).op := by
  refine (congrArg (fun k => AlgebraicGeometry.Scheme.Modules.Hom.app k A)
    (((AlgebraicGeometry.Scheme.Modules.restrictAdjunction f).homEquiv T Q).symm_apply_apply g).symm).trans ?_
  refine (congrArg (fun k => AlgebraicGeometry.Scheme.Modules.Hom.app k A)
    (CategoryTheory.Adjunction.homEquiv_counit (AlgebraicGeometry.Scheme.Modules.restrictAdjunction f) _ _ _)).trans ?_
  rfl

/-- The value on sections of the abstract form of the comparison map of 01NR: for `ι = e ≫ c` (`e` an isomorphism,
    `c` an open immersion) and `t : T ⟶ c_* N`, the component at `A` of
    `(rFIP ι).hom ≫ (pullbackCongr) ≫ (pullbackComp e c).inv ≫ e^*(t^♯) ≫ (rFIP e).inv`
    is the component of `t` at `ι''A` (transported along `e''A = c⁻¹(ι''A)`). -/
theorem AlgebraicGeometry.Scheme.Modules.chart_comparison_app
    {Y P Z : AlgebraicGeometry.Scheme.{u}} (ι : Y ⟶ P) [AlgebraicGeometry.IsOpenImmersion ι]
    (e : Y ≅ Z) [AlgebraicGeometry.IsOpenImmersion e.hom] (c : Z ⟶ P) [AlgebraicGeometry.IsOpenImmersion c]
    (p : ι = e.hom ≫ c) (T : P.Modules) (N : Z.Modules)
    (t : T ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward c).obj N)
    (φ : (AlgebraicGeometry.Scheme.Modules.pullback c).obj T ⟶ N)
    (hφ : φ = ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction c).homEquiv _ _).symm t)
    (A : Y.Opens) (hA : e.hom ''ᵁ A = c ⁻¹ᵁ (ι ''ᵁ A)) :
    (((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback ι).hom.app T ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr p).hom.app T ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp e.hom c).inv.app T ≫
      (AlgebraicGeometry.Scheme.Modules.pullback e.hom).map φ) ≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback e.hom).inv.app N).app A =
    t.app (ι ''ᵁ A) ≫ N.presheaf.map (CategoryTheory.eqToHom hA).op := by
  subst hφ
  have hc : e.hom ≫ c = ι := p.symm
  subst hc
  simp only [CategoryTheory.Category.assoc]
  set g₁ := ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction c).homEquiv _ _).symm t with hg₁
  have ht : (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction c).homEquiv _ _ g₁ = t :=
    Equiv.apply_symm_apply _ _
  have hcongr : (AlgebraicGeometry.Scheme.Modules.pullbackCongr p).hom.app T = 𝟙 _ := rfl
  rw [hcongr, CategoryTheory.Category.id_comp,
    AlgebraicGeometry.Scheme.Modules.restrict_hom_app_eq_homEquiv_app]
  -- the transpose of the composite
  have key : (AlgebraicGeometry.Scheme.Modules.restrictAdjunction (e.hom ≫ c)).homEquiv T (N.restrict e.hom)
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (e.hom ≫ c)).hom.app T ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackComp e.hom c).inv.app T ≫
        (AlgebraicGeometry.Scheme.Modules.pullback e.hom).map g₁ ≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback e.hom).inv.app N) =
      t ≫ (AlgebraicGeometry.Scheme.Modules.pushforward c).map
          ((AlgebraicGeometry.Scheme.Modules.restrictAdjunction e.hom).unit.app N) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardComp e.hom c).hom.app (N.restrict e.hom) := by
    have h0 : (AlgebraicGeometry.Scheme.Modules.restrictAdjunction (e.hom ≫ c)).homEquiv T _
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (e.hom ≫ c)).hom.app T) =
        (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (e.hom ≫ c)).unit.app T :=
      CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ T
    rw [CategoryTheory.Adjunction.homEquiv_naturality_right, h0]
    have h1 := CategoryTheory.unit_conjugateEquiv
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction c).comp
        (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction e.hom))
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (e.hom ≫ c))
      (AlgebraicGeometry.Scheme.Modules.pullbackComp e.hom c).inv T
    rw [AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h1
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, ← CategoryTheory.Category.assoc,
      ← CategoryTheory.Category.assoc, ← h1, CategoryTheory.Category.assoc, CategoryTheory.Category.assoc,
      ← (AlgebraicGeometry.Scheme.Modules.pushforwardComp e.hom c).hom.naturality_assoc,
      ← (AlgebraicGeometry.Scheme.Modules.pushforwardComp e.hom c).hom.naturality,
      CategoryTheory.Adjunction.comp_unit_app]
    have h2 := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.naturality g₁
    simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map] at h2
    have h3 : (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app N ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward e.hom).map
          ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback e.hom).inv.app N) =
        (AlgebraicGeometry.Scheme.Modules.restrictAdjunction e.hom).unit.app N :=
      CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app
        (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction e.hom)
        (AlgebraicGeometry.Scheme.Modules.restrictAdjunction e.hom) N
    have h4 : ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app
          ((AlgebraicGeometry.Scheme.Modules.pullback c).obj T) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward e.hom).map
          ((AlgebraicGeometry.Scheme.Modules.pullback e.hom).map g₁)) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward e.hom).map
          ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback e.hom).inv.app N) =
        g₁ ≫ (AlgebraicGeometry.Scheme.Modules.restrictAdjunction e.hom).unit.app N := by
      rw [← h2, CategoryTheory.Category.assoc, h3]
    rw [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_map, CategoryTheory.Category.assoc,
      ← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc, h4,
      CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Category.assoc,
      ← CategoryTheory.Adjunction.homEquiv_unit, ht]
  rw [key]
  simp only [AlgebraicGeometry.Scheme.Modules.Hom.comp_app, AlgebraicGeometry.Scheme.Modules.pushforward_map_app,
    AlgebraicGeometry.Scheme.Modules.pushforwardComp_hom_app_app, CategoryTheory.Category.comp_id,
    AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app, AlgebraicGeometry.Scheme.Modules.restrict_map,
    CategoryTheory.Category.assoc, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.op_comp]
  erw [CategoryTheory.Category.comp_id, CategoryTheory.Category.assoc, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.op_comp]
  exact congrArg (fun k => t.app _ ≫ N.presheaf.map (Quiver.Hom.op k)) (Subsingleton.elim _ _)

/-- Unfolding of the definition of `twistChartHom` (a definitional equality; the kernel check takes about 4 s and is done
only here — downstream rewrites with this lemma instead of using `rfl`). -/
theorem AlgebraicGeometry.Scheme.GradedAffineAlgebra.twistChartHom_eq {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedAffineAlgebra) (n : ℤ) (U : X.AffineZariskiSite) :
    S.twistChartHom n U =
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (S.projChart U)).homEquiv
          (S.twist n) (AlgebraicGeometry.Proj.twist (S.grading U) n)).symm (S.twistπ n U) := rfl

/-- The chart-sections map in general shape: `ι = e ≫ c` (`e` an isomorphism, `c` an open immersion), `T` on `P`,
    `N` on `Z`, `φ : c^*T ⟶ N`, and
    `((rFIP ι).hom ≫ pullbackCongr ≫ (pullbackComp e c).inv ≫ e^*(φ)) ≫ (rFIP e).inv : T|_ι ⟶ N|_e`.
    A `def` with **variables** as parameters: its body contains no instance or proof that could be abstracted by
    nested-proof abstraction, so `chartSectionsAux_app` is a verbatim instance of `chart_comparison_app`. The body of
    `twistAffineHom` (Stacks 01NR) has exactly this shape. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.chartSectionsAux
    {Y P Z : AlgebraicGeometry.Scheme.{u}} (ι : Y ⟶ P) [AlgebraicGeometry.IsOpenImmersion ι]
    (e : Y ≅ Z) [AlgebraicGeometry.IsOpenImmersion e.hom] (c : Z ⟶ P) [AlgebraicGeometry.IsOpenImmersion c]
    (p : ι = e.hom ≫ c) (T : P.Modules) (N : Z.Modules)
    (φ : (AlgebraicGeometry.Scheme.Modules.pullback c).obj T ⟶ N) :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor ι).obj T ⟶
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor e.hom).obj N :=
  -- Starting with a `let`: the equation lemma is then a single delta step in the kernel (for "constant = composite
  -- starting with `≫`" the kernel would first unfold the right-hand side deeply).
  let T' := T
  ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback ι).hom.app T' ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr p).hom.app T' ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp e.hom c).inv.app T' ≫
      (AlgebraicGeometry.Scheme.Modules.pullback e.hom).map φ) ≫
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback e.hom).inv.app N

/-- The section formula for `chartSectionsAux` (a verbatim instance of `chart_comparison_app`). -/
theorem AlgebraicGeometry.Scheme.Modules.chartSectionsAux_app
    {Y P Z : AlgebraicGeometry.Scheme.{u}} (ι : Y ⟶ P) [AlgebraicGeometry.IsOpenImmersion ι]
    (e : Y ≅ Z) [AlgebraicGeometry.IsOpenImmersion e.hom] (c : Z ⟶ P) [AlgebraicGeometry.IsOpenImmersion c]
    (p : ι = e.hom ≫ c) (T : P.Modules) (N : Z.Modules)
    (t : T ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward c).obj N)
    (φ : (AlgebraicGeometry.Scheme.Modules.pullback c).obj T ⟶ N)
    (hφ : φ = ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction c).homEquiv _ _).symm t)
    (A : Y.Opens) (hA : e.hom ''ᵁ A = c ⁻¹ᵁ (ι ''ᵁ A)) :
    (AlgebraicGeometry.Scheme.Modules.chartSectionsAux ι e c p T N φ).app A =
      t.app (ι ''ᵁ A) ≫ N.presheaf.map (CategoryTheory.eqToHom hA).op := by
  unfold AlgebraicGeometry.Scheme.Modules.chartSectionsAux
  dsimp only
  exact AlgebraicGeometry.Scheme.Modules.chart_comparison_app ι e c p T N t φ hφ A hA


/-! ### Plain `def` wrappers

For two applications of an `abbrev` head (`≫`, `NatTrans.app`, `Functor.map`) the kernel does **not** compare the
arguments first but unfolds both sides, so a small difference in the spelling of the arguments costs tens of seconds;
for a plain `def` head it compares the arguments first. Wrapping the factors on the right-hand side in plain `def`s
brings the kernel check of `twistAffineHom_app` from a timeout down to a few seconds. -/

/-- `((restrictFunctorIsoPullback f).hom.app N).app A`, wrapped in a plain `def` (instances explicit). -/
noncomputable def AlgebraicGeometry.Scheme.Modules.rFIPhomApp {Y Z : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ Z)
    (hf : AlgebraicGeometry.IsOpenImmersion f) (N : Z.Modules) (A : Y.Opens) :
    Γ((@AlgebraicGeometry.Scheme.Modules.restrictFunctor Y Z f hf).obj N, A) ⟶
      Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N, A) :=
  ((@AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback Y Z f hf).hom.app N).app A

/-- `N.presheaf.map i.op`, wrapped in a plain `def`. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.presheafMapW {Z : AlgebraicGeometry.Scheme.{u}} (N : Z.Modules)
    {V W : Z.Opens} (i : V ⟶ W) : Γ(N, W) ⟶ Γ(N, V) :=
  N.presheaf.map i.op

theorem AlgebraicGeometry.Scheme.Modules.presheafMapW_def {Z : AlgebraicGeometry.Scheme.{u}} (N : Z.Modules)
    {V W : Z.Opens} (i : V ⟶ W) :
    AlgebraicGeometry.Scheme.Modules.presheafMapW N i = N.presheaf.map i.op := rfl

/-- The component of `rFIPhomApp` followed by `(restrictFunctorIsoPullback f).inv` is the identity. -/
theorem AlgebraicGeometry.Scheme.Modules.rFIPhomApp_comp_inv_app {Y Z : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ Z)
    (hf : AlgebraicGeometry.IsOpenImmersion f) (N : Z.Modules) (A : Y.Opens) :
    AlgebraicGeometry.Scheme.Modules.rFIPhomApp f hf N A ≫
        ((@AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback Y Z f hf).inv.app N).app A = 𝟙 _ := by
  unfold AlgebraicGeometry.Scheme.Modules.rFIPhomApp
  rw [← AlgebraicGeometry.Scheme.Modules.Hom.comp_app, CategoryTheory.Iso.hom_inv_id_app,
    AlgebraicGeometry.Scheme.Modules.Hom.id_app]

/-- The composite equality from two section formulas: if `F.app A = t ≫ s ≫ rFIPhomApp f hf N A` and
    `χ.app A = t ≫ s`, then `(F ≫ (rFIP f).inv.app N).app A = χ.app A`. A lemma at the level of variables; the concrete
    level only instantiates it with syntactically identical terms. -/
theorem AlgebraicGeometry.Scheme.Modules.app_comp_rFIP_inv_eq_of_formulas {Y Z : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ Z) (hf : AlgebraicGeometry.IsOpenImmersion f) (M : Y.Modules) (N : Z.Modules)
    (F : M ⟶ (AlgebraicGeometry.Scheme.Modules.pullback f).obj N)
    (χ : M ⟶ (@AlgebraicGeometry.Scheme.Modules.restrictFunctor Y Z f hf).obj N) (A : Y.Opens)
    {W : AddCommGrpCat.{u}} (t : Γ(M, A) ⟶ W)
    (s : W ⟶ Γ((@AlgebraicGeometry.Scheme.Modules.restrictFunctor Y Z f hf).obj N, A))
    (hF : F.app A = t ≫ s ≫ AlgebraicGeometry.Scheme.Modules.rFIPhomApp f hf N A) (hχ : χ.app A = t ≫ s) :
    (F ≫ (@AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback Y Z f hf).inv.app N).app A = χ.app A := by
  rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app, hF, hχ, CategoryTheory.Category.assoc,
    CategoryTheory.Category.assoc, AlgebraicGeometry.Scheme.Modules.rFIPhomApp_comp_inv_app,
    CategoryTheory.Category.comp_id]

/-- If `(X ≫ α.hom).app A = r ≫ s`, then `X.app A = r ≫ s ≫ α.inv.app A` (moving the isomorphism factor to the right). -/
theorem AlgebraicGeometry.Scheme.Modules.app_eq_of_comp_iso_app {Y : AlgebraicGeometry.Scheme.{u}}
    {M N₁ N₂ : Y.Modules} (X : M ⟶ N₁) (α : N₁ ≅ N₂) (A : Y.Opens) {W : AddCommGrpCat.{u}}
    (r : Γ(M, A) ⟶ W) (s : W ⟶ Γ(N₂, A)) (h : (X ≫ α.hom).app A = r ≫ s) :
    X.app A = r ≫ s ≫ α.inv.app A := by
  rw [← CategoryTheory.Category.assoc, ← h, ← AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    CategoryTheory.Category.assoc, CategoryTheory.Iso.hom_inv_id, CategoryTheory.Category.comp_id]

/-- `chart_comparison_app` without the final `(rFIP e).inv` factor, which is moved to the right-hand side. The
    instances are **explicit** parameters (so that `refine … _ …` assigns them by unification instead of instance
    search — instance search does not find `IsOpenImmersion (projChart ⟨U.1, _⟩)`), and the right-hand side uses only
    the plain `def` wrappers above. -/
theorem AlgebraicGeometry.Scheme.Modules.chart_comparison_app_noE
    {Y P Z : AlgebraicGeometry.Scheme.{u}} (ι : Y ⟶ P) (hι : AlgebraicGeometry.IsOpenImmersion ι)
    (e : Y ≅ Z) (he : AlgebraicGeometry.IsOpenImmersion e.hom) (c : Z ⟶ P) (hc : AlgebraicGeometry.IsOpenImmersion c)
    (p : ι = e.hom ≫ c) (T : P.Modules) (N : Z.Modules)
    (t : T ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward c).obj N)
    (φ : (AlgebraicGeometry.Scheme.Modules.pullback c).obj T ⟶ N)
    (hφ : φ = ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction c).homEquiv _ _).symm t)
    (A : Y.Opens) (hA : e.hom ''ᵁ A = c ⁻¹ᵁ (ι ''ᵁ A)) :
    ((@AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback Y P ι hι).hom.app T ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr p).hom.app T ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp e.hom c).inv.app T ≫
      (AlgebraicGeometry.Scheme.Modules.pullback e.hom).map φ).app A =
    t.app (ι ''ᵁ A) ≫ AlgebraicGeometry.Scheme.Modules.presheafMapW N (CategoryTheory.eqToHom hA) ≫
      AlgebraicGeometry.Scheme.Modules.rFIPhomApp e.hom he N A := by
  unfold AlgebraicGeometry.Scheme.Modules.rFIPhomApp AlgebraicGeometry.Scheme.Modules.presheafMapW
  exact AlgebraicGeometry.Scheme.Modules.app_eq_of_comp_iso_app _
    ((@AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback Y Z e.hom he).app N).symm A _ _
    (@AlgebraicGeometry.Scheme.Modules.chart_comparison_app Y P Z ι hι e he c hc p T N t φ hφ A hA)

/-- The chart `c_U = projChart ⟨U.1, U.2⟩`, with target written as `(relativeProj S).left`. Wrapped as a constant with
    atomic parameters, so that definitions containing it have no term that nested-proof abstraction could lift and
    no term that unfolds to different spellings at different places (see the module docstring). -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.chartMap {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (U : X.affineOpens) :
    AlgebraicGeometry.Proj (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U)) ⟶ (AlgebraicGeometry.Scheme.relativeProj S).left :=
  S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U)

/-- The chart `chartMap S U` is an open immersion. Stated as a `theorem` rather than a global `instance`; pass it
    explicitly with `@` where needed (as `chartSections` and `chartSections_app` of this module do). -/
theorem AlgebraicGeometry.Scheme.relativeProj.chartMap_isOpenImmersion {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (U : X.affineOpens) :
    AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Scheme.relativeProj.chartMap S U) :=
  AlgebraicGeometry.Scheme.GradedAffineAlgebra.projChart_isOpenImmersion _ _

/-- The twisting sheaf `O_U(n)` on the chart, wrapped as a constant. The body **deliberately** uses the spelling
    `Proj.twist (S.sectionsGrading U.1) n` from the type of `twistAffineHom` (Stacks 01NR), not
    `Proj.twist (S.grading (affineSite U)) n` (the two are definitionally equal): then `chartTwist S U n` and the
    codomain of `twistAffineHom` differ by one delta step, and the kernel sees syntactically identical terms after
    one unfolding. With `grading (affineSite U)` every comparison would unfold down to the fields of
    `toGradedAffineAlgebra`; the kernel check of `twistAffineHom_comp_eq_chartSections` drops from over 44 s to a few
    seconds. -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.chartTwist {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (U : X.affineOpens) (n : ℤ) :
    (AlgebraicGeometry.Proj (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U))).Modules :=
  AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) n

/-- The chart comparison map `c_U^* O(n) ⟶ O_U(n)` (`twistChartHom n ⟨U.1, U.2⟩`, wrapped as a constant). -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.chartComparison {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (U : X.affineOpens) (n : ℤ) :
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.chartMap S U)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S n) ⟶
      AlgebraicGeometry.Scheme.relativeProj.chartTwist S U n :=
  S.toGradedAffineAlgebra.twistChartHom n (AlgebraicGeometry.Scheme.affineSite U)

/-- `chartComparison` is the adjoint transpose of `twistπ` (the constant form of `twistChartHom_eq`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.chartComparison_eq {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (U : X.affineOpens) (n : ℤ) :
    AlgebraicGeometry.Scheme.relativeProj.chartComparison S U n =
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
          (AlgebraicGeometry.Scheme.relativeProj.chartMap S U)).homEquiv
          (AlgebraicGeometry.Scheme.relativeProj.twist S n)
          (AlgebraicGeometry.Scheme.relativeProj.chartTwist S U n)).symm
        (S.toGradedAffineAlgebra.twistπ n (AlgebraicGeometry.Scheme.affineSite U)) := by
  unfold AlgebraicGeometry.Scheme.relativeProj.chartComparison
  exact AlgebraicGeometry.Scheme.GradedAffineAlgebra.twistChartHom_eq _ n _

/-- The open immersion `ι_U = e_U ≫ c_U` (another form of `affineIso_inv_ι`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.ι_eq_affineIso_comp_chartMap {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (U : X.affineOpens) :
    ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι =
      (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom ≫
        AlgebraicGeometry.Scheme.relativeProj.chartMap S U := by
  refine Eq.symm ?_
  refine (congrArg (fun k => (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom ≫ k)
    (AlgebraicGeometry.Scheme.relativeProj.affineIso_inv_ι S U).symm).trans ?_
  refine (CategoryTheory.Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι)
    (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom_inv_id).trans ?_
  exact CategoryTheory.Category.id_comp _

/-- `e_U ''ᵁ A = c_U ⁻¹ᵁ (ι_U ''ᵁ A)` (`c_U = e_U⁻¹ ≫ ι_U` is the chart). -/
theorem AlgebraicGeometry.Scheme.relativeProj.affineIso_image_eq_chartMap_preimage
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (U : X.affineOpens)
    (A : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).toScheme.Opens) :
    (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom ''ᵁ A =
      AlgebraicGeometry.Scheme.relativeProj.chartMap S U ⁻¹ᵁ
        (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A) := by
  change _ = S.toGradedAffineAlgebra.projChart ⟨U.1, U.2⟩ ⁻¹ᵁ _
  rw [← AlgebraicGeometry.Scheme.relativeProj.affineIso_inv_ι S U]
  change _ = (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).inv ⁻¹ᵁ
    (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ
      (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A))
  rw [AlgebraicGeometry.Scheme.Hom.preimage_image_eq, AlgebraicGeometry.Scheme.Hom.inv_preimage]

/-- The chart-sections map `χ_U(n) : O(n)|_{π⁻¹U} ⟶ O_U(n)|_{e_U}`: the value of `chartSectionsAux` on the chart data
    of 01NR (`affineIso`, `chartMap`, `twist S n`, `chartTwist`, `chartComparison`); its relation to
    `twistAffineHom U n` (Stacks 01NR) is `twistAffineHom_comp_eq_chartSections`.
    Over `A ⊆ π⁻¹U` it is `Γ(O(n), ι_U''A) ⟶ Γ(O_U(n), e_U''A)`. -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.chartSections {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (U : X.affineOpens) (n : ℤ) :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S n) ⟶
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom).obj
        (AlgebraicGeometry.Scheme.relativeProj.chartTwist S U n) :=
  @AlgebraicGeometry.Scheme.Modules.chartSectionsAux _ _ _ ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι
    inferInstance (AlgebraicGeometry.Scheme.relativeProj.affineIso S U) inferInstance
    (AlgebraicGeometry.Scheme.relativeProj.chartMap S U)
    (AlgebraicGeometry.Scheme.relativeProj.chartMap_isOpenImmersion S U)
    (AlgebraicGeometry.Scheme.relativeProj.ι_eq_affineIso_comp_chartMap S U)
    (AlgebraicGeometry.Scheme.relativeProj.twist S n) (AlgebraicGeometry.Scheme.relativeProj.chartTwist S U n)
    (AlgebraicGeometry.Scheme.relativeProj.chartComparison S U n)

/-- **Section formula for `χ_U(n)`**: over `A ⊆ π⁻¹U`, `χ_U(n)` is the component of the limit projection `twistπ` at
    `ι_U''A` (transported along `e_U''A = c_U⁻¹(ι_U''A)`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.chartSections_app {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (U : X.affineOpens) (n : ℤ)
    (A : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).toScheme.Opens) :
    (AlgebraicGeometry.Scheme.relativeProj.chartSections S U n).app A =
      (S.toGradedAffineAlgebra.twistπ n (AlgebraicGeometry.Scheme.affineSite U)).app
          (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A) ≫
        (AlgebraicGeometry.Scheme.relativeProj.chartTwist S U n).presheaf.map
          (CategoryTheory.eqToHom
            (AlgebraicGeometry.Scheme.relativeProj.affineIso_image_eq_chartMap_preimage S U A)).op := by
  unfold AlgebraicGeometry.Scheme.relativeProj.chartSections
  exact @AlgebraicGeometry.Scheme.Modules.chartSectionsAux_app _ _ _
    ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι inferInstance
    (AlgebraicGeometry.Scheme.relativeProj.affineIso S U) inferInstance
    (AlgebraicGeometry.Scheme.relativeProj.chartMap S U)
    (AlgebraicGeometry.Scheme.relativeProj.chartMap_isOpenImmersion S U)
    (AlgebraicGeometry.Scheme.relativeProj.ι_eq_affineIso_comp_chartMap S U)
    (AlgebraicGeometry.Scheme.relativeProj.twist S n) (AlgebraicGeometry.Scheme.relativeProj.chartTwist S U n)
    (S.toGradedAffineAlgebra.twistπ n (AlgebraicGeometry.Scheme.affineSite U)) (AlgebraicGeometry.Scheme.relativeProj.chartComparison S U n)
    (AlgebraicGeometry.Scheme.relativeProj.chartComparison_eq S U n) A
    (AlgebraicGeometry.Scheme.relativeProj.affineIso_image_eq_chartMap_preimage S U A)

/-- **Section formula for `twistAffineHom`** (the component over `A ⊆ π⁻¹U` of the comparison map of Stacks 01NR):
    `(twistAffineHom S U n).app A = (component of twistπ at ι_U''A) ≫ (transport along e_U''A = c_U⁻¹(ι_U''A)) ≫
    (component of (rFIP e_U).hom)`.
    Proof: `unfold twistAffineHom; dsimp only`, then `refine` with `chart_comparison_app_noE`, writing `_` for **all
    data arguments** (`ι`, `e`, `c`, `p`, `T`, `N`, `φ` and the three instances) so that they are assigned by
    unification from the goal (the unfolded body of `twistAffineHom`); the instance of the lemma and the goal are then
    **syntactically identical** at every `≫`/`.app` node; only `hc` (absent from the conclusion) and `hφ` are closed
    separately with `?_`. On the right-hand side `presheafMapW` and `rFIPhomApp` are plain `def`s, and the spelling
    difference between `chartTwist S U n` and `Proj.twist (S.sectionsGrading U.1) n` in the body sits under a plain
    `def` head (the kernel compares arguments first, which is cheap). Measured: elaborator 0.3 s, kernel 4 s.
    Variants that exceed 60 s: passing `t`/`hA` explicitly (their types assign `?c ?T ?N` to the statement-side
    spelling first, the `≫` nodes mismatch and the kernel unfolds deeply); `rfl` for the whole equation
    `twistAffineHom = composite` (kernel 24–42 s); `congrArg₂ (· ≫ ·)` (Meta `isDefEq` timeout). -/
theorem AlgebraicGeometry.Scheme.relativeProj.twistAffineHom_app {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (U : X.affineOpens) (n : ℤ)
    (A : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).toScheme.Opens) :
    @AlgebraicGeometry.Scheme.Modules.Hom.app _ _
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom).obj
          (AlgebraicGeometry.Scheme.relativeProj.chartTwist S U n))
        (AlgebraicGeometry.Scheme.relativeProj.twistAffineHom S U n) A =
      (S.toGradedAffineAlgebra.twistπ n (AlgebraicGeometry.Scheme.affineSite U)).app
          (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A) ≫
        AlgebraicGeometry.Scheme.Modules.presheafMapW (AlgebraicGeometry.Scheme.relativeProj.chartTwist S U n)
          (CategoryTheory.eqToHom
            (AlgebraicGeometry.Scheme.relativeProj.affineIso_image_eq_chartMap_preimage S U A)) ≫
        AlgebraicGeometry.Scheme.Modules.rFIPhomApp (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom
          inferInstance (AlgebraicGeometry.Scheme.relativeProj.chartTwist S U n) A := by
  unfold AlgebraicGeometry.Scheme.relativeProj.twistAffineHom
  dsimp only
  refine AlgebraicGeometry.Scheme.Modules.chart_comparison_app_noE _ _ _ _ _ ?_ _ _ _ _ _ ?_ A _
  · exact S.toGradedAffineAlgebra.projChart_isOpenImmersion _
  · exact AlgebraicGeometry.Scheme.GradedAffineAlgebra.twistChartHom_eq S.toGradedAffineAlgebra n _

/-- The comparison map of 01NR followed by the inverse of `restrictFunctorIsoPullback e_U` is `χ_U(n)`.
    In the statement the middle object of `≫` is written explicitly with `@` as `(pullback e_U).obj (chartTwist S U n)`
    (matching the type of `chartSections`; the type of `twistAffineHom` spells it `Proj.twist (S.sectionsGrading U.1) n`,
    one delta step away from `chartTwist S U n`).

    **Proof**: both section formulas are available — `twistAffineHom_app` on the left and `chartSections_app` on the
    right; `(F ≫ (rFIP e_U).inv.app N).app A = F.app A ≫ ((rFIP e_U).inv.app N).app A`, and `rFIPhomApp_comp_inv_app`
    cancels the component of `(rFIP e_U).hom ≫ (rFIP e_U).inv`, so both sides agree at every `A`; `Modules.hom_ext`
    finishes. The assembly lemma `app_comp_rFIP_inv_eq_of_formulas` at the level of variables is exactly this step.

    **Compile-time remark**: when instantiating the assembly lemma one must pass `f := (affineIso S U).hom` and
    `N := chartTwist S U n` **explicitly** and write `_` for the rest. With all `_` the elaborator assigns
    `?F := twistAffineHom S U n` first and from its type sets `?N` to `Proj.twist (S.sectionsGrading U.1) n` (not the
    goal's `chartTwist S U n`); with only `N` explicit, `?Z` is set from the declared type of `chartTwist` to
    `Proj (grading (affineSite U))` (not `Proj (S.sectionsGrading U.1)`, the codomain of `e_U`). In both cases the term
    `(restrictFunctorIsoPullback e_U).inv.app N` of the conclusion differs in spelling from the goal's term under the
    `abbrev` heads `NatTrans.app`/`Iso.inv`, and the kernel unfolds `restrictFunctorIsoPullback` (`leftAdjointUniq`)
    wholesale: 24 s (`N` mismatch) or over 60 s (`Z` mismatch). With both `f` and `N` explicit all nodes agree with the
    goal syntactically: elaborator 1 s, kernel under 0.2 s. The other possible mismatches (`restrict` versus
    `(restrictFunctor ι).obj`, the middle object `Γ(N, e''A)` versus `Γ((restrictFunctor e).obj N, A)`, instances wrapped
    in `inferInstance`) are all cheap (under 0.3 s). -/
theorem AlgebraicGeometry.Scheme.relativeProj.twistAffineHom_comp_eq_chartSections
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (U : X.affineOpens) (n : ℤ) :
    @CategoryTheory.CategoryStruct.comp _ _ _
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom).obj
          (AlgebraicGeometry.Scheme.relativeProj.chartTwist S U n)) _
        (AlgebraicGeometry.Scheme.relativeProj.twistAffineHom S U n)
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback
          (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom).inv.app
          (AlgebraicGeometry.Scheme.relativeProj.chartTwist S U n)) =
      AlgebraicGeometry.Scheme.relativeProj.chartSections S U n := by
  refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ (fun A => ?_)
  refine AlgebraicGeometry.Scheme.Modules.app_comp_rFIP_inv_eq_of_formulas
    (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom _ _
    (AlgebraicGeometry.Scheme.relativeProj.chartTwist S U n) _ _ A _ _
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineHom_app S U n A) ?_
  exact (AlgebraicGeometry.Scheme.relativeProj.chartSections_app S U n A).trans
    (congrArg (fun k => _ ≫ k) (AlgebraicGeometry.Scheme.Modules.presheafMapW_def _ _).symm)
end
