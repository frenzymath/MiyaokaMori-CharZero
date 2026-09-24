import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecStructureIso
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackCompMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodToTotalSpace
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleZpowNegIso
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineCoefficientMap

/-! # Naturality of the coefficient chain under restriction to the thickening

The coefficient chain on the thickening `C̃_(κ)(L) = Spec_{C̃}(⊕_{q≤κ} L^{-q})` is the coefficient
chain on `Tot(L) = Spec_{C̃} Sym(L^∨)` composed with restriction along the closed immersion
`i : C̃_(κ)(L) ↪ Tot(L)` (for `q ≤ κ`).  This is the morphism-level content of
`xiCoefficient_restrictToThickening` (`ThickeningSectionsTruncated`).

Source: §3 of the paper (`C̃_(k)(L)` is the `k`-th infinitesimal neighbourhood of the zero
section of `Tot(L)`, "where products of degree greater than k are zero") and Lemma 4.1 ((4.1): restricting `P_ℓ` to the thickening keeps the coefficients `c_{ℓ,q}`, `q ≤ k`).

Structure:
* `pushforwardUnitAlong h g e`: the pushed-forward ring map `ψ : g_*O_T → g'_*O_{T'}` for
  `h : T' → T`, `g : T → X`, `h ≫ g = g'`.
* Leaf A `pullbackSectionToPushforward_comp`: `Γ(T, g^*M) → Γ(X, M ⊗ g_*O_T)` is
  natural in the morphism, i.e. commutes with restriction along `h` and with `M ◁ ψ`. It is the
  global-sections instance of the morphism identity (★)
  `whiskerLeft_pushforwardUnitAlong_comp_projectionFormulaHom`, proved by transposing along
  `g'^* ⊣ g'_*`; the ingredient `(pullbackComp).hom ≫ g'^*ψ ≫ ε_{g'} = h^*ε_g ≫ (pullbackUnitIso h).hom`
  is `pullbackComp_hom_app_comp_pullback_map_pushforwardUnitAlong_comp_counit`.
* Leaf B' `relativeSpec.toAlgebraMap_eq`: for `h : T → Spec_X A` over `X`, the algebra map
  attached to `h` by the universal property is `structureHom A ≫ ψ_h`.
  (Engineering note: `totalSpace L.toModules` and `relativeSpec (Sym L^∨)` are definitionally equal, but
  asking Lean to compare *composites* written in the two typings is extremely slow (> 60 s); always
  bridge with `congr 1` / `rw [show … from rfl]` on the plain `pushforwardUnitAlong` term instead.)
* Leaf C `truncatedJetAlgebra.truncation_π`: the `q`-th component of the truncation map.
* `jetNeighborhood.thickeningCoefficient_apply`: Leaf B (`σ ≫ ψ_i = truncation ≫ σ_κ`, from
  `relativeSpecHomEquiv.apply_symm_apply` and Leaf B') and Leaf C assembled at section level, verbatim in
  the shape used by `xiCoefficient_restrictToThickening`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

/-- For `h : T' ⟶ T`, `g : T ⟶ X` and `g' = h ≫ g`, the pushed-forward ring map
`ψ : g_*O_T ⟶ g'_*O_{T'}`: `g_*` of `h^♯ : O_T → h_*O_{T'}` (`SheafOfModules.unitToPushforwardObjUnit`),
followed by `g_*h_* ≅ (h ≫ g)_*` (`pushforwardComp`) and the transport along `e`. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.pushforwardUnitAlong
    {T' T X : AlgebraicGeometry.Scheme.{u}} (h : T' ⟶ T) (g : T ⟶ X) {g' : T' ⟶ X}
    (e : h ≫ g = g') :
    (AlgebraicGeometry.Scheme.Modules.pushforward g).obj (SheafOfModules.unit T.ringCatSheaf) ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward g').obj (SheafOfModules.unit T'.ringCatSheaf) :=
  (AlgebraicGeometry.Scheme.Modules.pushforward g).map
      (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) ≫
    (AlgebraicGeometry.Scheme.Modules.pushforwardComp h g).hom.app (SheafOfModules.unit T'.ringCatSheaf) ≫
    CategoryTheory.eqToHom (congrArg (fun f => (AlgebraicGeometry.Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit T'.ringCatSheaf)) e)

/-- Transport along an equality of morphisms, on sections: it is the restriction map of `N`
along the (definitional) equality of preimages. -/
theorem AlgebraicGeometry.Scheme.Modules.eqToHom_pushforward_obj_app
    {T' X : AlgebraicGeometry.Scheme.{u}} {g g' : T' ⟶ X} (e : g = g') (N : T'.Modules)
    (U : X.Opens) (s : Γ(N, g ⁻¹ᵁ U)) :
    (((CategoryTheory.eqToHom (congrArg (fun f => (AlgebraicGeometry.Scheme.Modules.pushforward f).obj N)
        e)).app U).hom s : Γ(N, g' ⁻¹ᵁ U)) =
      (N.presheaf.map (CategoryTheory.eqToHom (by rw [e])).op).hom s := by
  subst e
  simp
  rfl

/-- Sections of `ψ`: on `U ⊆ X` it is `h^♯` on `g⁻¹U` followed by the identification of preimages. -/
theorem AlgebraicGeometry.Scheme.Modules.pushforwardUnitAlong_app
    {T' T X : AlgebraicGeometry.Scheme.{u}} (h : T' ⟶ T) (g : T ⟶ X) {g' : T' ⟶ X}
    (e : h ≫ g = g') (U : X.Opens) (s : Γ(T, g ⁻¹ᵁ U)) :
    (((AlgebraicGeometry.Scheme.Modules.pushforwardUnitAlong h g e).app U).hom s : Γ(T', g' ⁻¹ᵁ U)) =
      (T'.presheaf.map (CategoryTheory.eqToHom
        (show g' ⁻¹ᵁ U = h ⁻¹ᵁ (g ⁻¹ᵁ U) by rw [← e]; rfl)).op).hom
        ((h.app (g ⁻¹ᵁ U)).hom s) := by
  change (((CategoryTheory.eqToHom (congrArg (fun f => (AlgebraicGeometry.Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit T'.ringCatSheaf)) e)).app U).hom
      ((((AlgebraicGeometry.Scheme.Modules.pushforwardComp h g).hom.app
          (SheafOfModules.unit T'.ringCatSheaf)).app U).hom
        ((((AlgebraicGeometry.Scheme.Modules.pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom)).app U).hom s)) : Γ(T', g' ⁻¹ᵁ U)) = _
  erw [AlgebraicGeometry.Scheme.Modules.eqToHom_pushforward_obj_app e]
  rfl

/-- **Leaf B'.** The algebra map attached by the universal property (Stacks 01LQ) to an `X`-morphism
`h : T → Spec_X A` is the structure map `A → π_*O_{Spec_X A}` followed by `ψ_h = π_*(h^♯)`.

Source: Stacks 01LQ; `RelativeSpecUniversalProperty.lean` (`pullbackSections`, `toAlgebraMap`).

Proof. Both sides are morphisms `A.carrier ⟶ (pushforward T.hom).obj O_T`; compare sections on each
open `U ⊆ X` (`Modules.hom_ext`). By definition `toAlgebraMap A T h` is, on `U`, the ring map
`pullbackSections A T h U = structureRingMap A (U) ≫ h.left.app (π⁻¹U) ≫ (transport of preimages)`.
On the right, `structureHom A` is `structureRingMap A` on sections (`structureHom_app_apply`) and
`ψ_h` is `h.left.app (π⁻¹U)` followed by the same transport (`pushforwardUnitAlong_app`). -/
theorem AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap_eq {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (T : CategoryTheory.Over X) (h : T ⟶ AlgebraicGeometry.Scheme.relativeSpec A) :
    AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap A T h =
      AlgebraicGeometry.Scheme.relativeSpec.structureHom A ≫
        AlgebraicGeometry.Scheme.Modules.pushforwardUnitAlong h.left
          (AlgebraicGeometry.Scheme.relativeSpec A).hom (CategoryTheory.Over.w h) := by
  refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ (fun U => ?_)
  ext a
  change AlgebraicGeometry.Scheme.relativeSpec.pullbackSections A T h U a = _
  rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app]
  change _ = (((AlgebraicGeometry.Scheme.Modules.pushforwardUnitAlong h.left
      (AlgebraicGeometry.Scheme.relativeSpec A).hom (CategoryTheory.Over.w h)).app U).hom
      ((AlgebraicGeometry.Scheme.relativeSpec.structureHom A).app U a) : Γ(T.left, T.hom ⁻¹ᵁ U))
  erw [AlgebraicGeometry.Scheme.Modules.pushforwardUnitAlong_app,
    AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_apply]
  rfl

/-- **Leaf B', with a free target.** Same as `toAlgebraMap_eq`, but the target of `h` is an arbitrary
`Z : Over X` together with `hZ : Z = Spec_X A`; the resulting `ψ` then carries the implicit arguments
of `Z`. Used with `Z := totalSpace L.toModules` (definitionally `Spec_{C̃} Sym(L^∨)`), so that `ψ` is
syntactically the one appearing in `pullbackSectionToPushforward_comp` for `toTotalSpace L κ`
(comparing the two typings of `ψ` definitionally forces Lean to unfold the relative-Spec gluing and does
not terminate in practice). -/
theorem AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap_eq' {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (T Z : CategoryTheory.Over X) (hZ : Z = AlgebraicGeometry.Scheme.relativeSpec A)
    (h : T ⟶ Z) :
    AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap A T (hZ ▸ h) =
      AlgebraicGeometry.Scheme.relativeSpec.structureHom A ≫
        CategoryTheory.eqToHom (congrArg (fun W : CategoryTheory.Over X =>
          (AlgebraicGeometry.Scheme.Modules.pushforward W.hom).obj
            (SheafOfModules.unit W.left.ringCatSheaf)) hZ.symm) ≫
        AlgebraicGeometry.Scheme.Modules.pushforwardUnitAlong h.left Z.hom (CategoryTheory.Over.w h) := by
  subst hZ
  rw [CategoryTheory.eqToHom_refl, Category.id_comp]
  exact AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap_eq A T h

/-- Component of the `q`-th graded projection on the `m`-th summand (`Sigma.ι_desc`). -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.ι_totalProj {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m q : ℕ) :
    CategoryTheory.Limits.Sigma.ι S.part m ≫ S.totalProj q =
      if h : m = q then CategoryTheory.eqToHom (congrArg S.part h) else 0 :=
  CategoryTheory.Limits.Sigma.ι_desc _ _

/-- **Leaf C.** The `q`-th component (`q ≤ κ`) of the truncation map `Sym(L^∨) → ⊕_{q≤κ} (L^{-1})^{⊗q}`
is the `q`-th graded projection followed by `Sym^q(L^∨) ≅ (L^∨)^{⊗q} ≅ (L^{-1})^{⊗q}`.

Source: §3 of the paper ("products of degree greater than k are zero");
`JetNeighborhoodToTotalSpace.lean` (`truncation` is `Sigma.desc` of the componentwise maps).

Proof. Both sides are maps out of the coproduct `∐_m Sym^m(L^∨)`; compare on each `Sigma.ι m`
(`Sigma.hom_ext`, `ι_truncation` from `JetNeighborhoodToTotalSpace.lean`, `ι_totalProj`). For `m = q`: left side
`symPartToMonoidalPow q ≫ pieceIso⁻¹ ≫ ι_q ≫ π_q` with `ι_q ≫ π_q = 𝟙` (`biproduct.ι_π_self`); right side
`eqToHom rfl ≫ …`. For `m ≠ q`, `m ≤ κ`: `ι_m ≫ π_q = 0` (`biproduct.ι_π`); for `m > κ` the left
component is `0`; the right side is `0 ≫ …`. -/
theorem truncatedJetAlgebra.truncation_π {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ q : ℕ) (hq : q ≤ κ) :
    truncatedJetAlgebra.truncation L κ ≫
        CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨q, Nat.lt_succ_of_le hq⟩ =
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalProj q ≫
        AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q ≫
        (truncatedJetAlgebra.pieceIso L q).inv := by
  refine CategoryTheory.Limits.Sigma.hom_ext
    (f := (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).part) _ _ (fun m => ?_)
  erw [← Category.assoc, ← Category.assoc, truncatedJetAlgebra.ι_truncation,
    AlgebraicGeometry.Scheme.GradedQCAlgebra.ι_totalProj]
  by_cases hm : m = q
  · subst hm
    rw [dif_pos hq, dif_pos rfl, CategoryTheory.eqToHom_refl, Category.id_comp]
    erw [Category.assoc, Category.assoc, CategoryTheory.Limits.biproduct.ι_π_self, Category.comp_id]
  · rw [dif_neg hm, zero_comp]
    by_cases hm' : m ≤ κ
    · rw [dif_pos hm']
      erw [Category.assoc, Category.assoc, CategoryTheory.Limits.biproduct.ι_π,
        dif_neg (fun h => hm (Fin.mk.inj_iff.mp h)), comp_zero]
    · rw [dif_neg hm']
      erw [zero_comp]

/-- Sections of a composite: `((f ≫ g).app U) x = (g.app U) ((f.app U) x)` (definitional). -/
theorem AlgebraicGeometry.Scheme.Modules.comp_val_app_apply {X : AlgebraicGeometry.Scheme.{u}}
    {A B C : X.Modules} (f : A ⟶ B) (g : B ⟶ C) (U : X.Opens) (x : (A.val.obj (Opposite.op U) : Type u)) :
    (((f ≫ g).val.app (Opposite.op U)).hom x : (C.val.obj (Opposite.op U) : Type u)) =
      (g.val.app (Opposite.op U)).hom ((f.val.app (Opposite.op U)).hom x) := rfl

/-- Sections of a whiskered composite: `(W ◁ g)(( W ◁ f) x) = (W ◁ (f ≫ g)) x`. -/
theorem AlgebraicGeometry.Scheme.Modules.whiskerLeft_val_app_apply {X : AlgebraicGeometry.Scheme.{u}}
    (W : X.Modules) {A B C : X.Modules} (f : A ⟶ B) (g : B ⟶ C) (U : X.Opens)
    (x : ((W ⊗ A).val.obj (Opposite.op U) : Type u)) :
    (((W ◁ g).val.app (Opposite.op U)).hom (((W ◁ f).val.app (Opposite.op U)).hom x) :
        ((W ⊗ C).val.obj (Opposite.op U) : Type u)) =
      ((W ◁ (f ≫ g)).val.app (Opposite.op U)).hom x := by
  rw [CategoryTheory.MonoidalCategory.whiskerLeft_comp]
  rfl

/-- **Leaf B (algebra-map form).** The algebra map attached by the universal property to the closed
immersion `toTotalSpace L κ` is `truncation ≫ σ_κ`: `relativeSpecHomEquiv` is an `Equiv`
(`Equiv.apply_symm_apply`) and `toTotalSpace` is `relativeSpecHomEquiv.symm ⟨truncation ≫ σ_κ, _⟩`.
Source: §3 of the paper; `JetNeighborhoodToTotalSpace.lean`. -/
theorem jetNeighborhood.toAlgebraMap_toTotalSpace {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ) :
    AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total
      (jetNeighborhood L κ) (jetNeighborhood.toTotalSpace L κ) = truncatedJetAlgebra.truncation L κ ≫
      AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ) := by
  have h1 : AlgebraicGeometry.Scheme.relativeSpecHomEquiv (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total
      (jetNeighborhood L κ) (jetNeighborhood.toTotalSpace L κ) =
      ⟨truncatedJetAlgebra.truncation L κ ≫
      AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ), jetNeighborhood.truncation_structureHom_isAlgebraMap L κ⟩ := by
    unfold jetNeighborhood.toTotalSpace
    exact Equiv.apply_symm_apply _ _
  exact congrArg Subtype.val h1

/-- **Section-level form, generic in `ψ`.** For any `ψ : p_*O_Tot ⟶ (p_κ)_*O` with
`σ ≫ ψ = truncation ≫ σ_κ` (Leaf B), applying the coefficient chain of `xiCoefficientThickening` to
`M ◁ ψ` of `pullbackSectionToPushforward p M P` gives the `q`-th ξ-coefficient of `P`
(`coefficientModuleIso ∘ totalSpace.coefficient`). Stated for a variable `ψ` so that the main module can
instantiate it by unification with whatever term Leaf A produces (comparing two syntactically different
spellings of `ψ` definitionally is prohibitively slow here).

Proof. `ψ ≫ σ_κ⁻¹ = σ⁻¹ ≫ truncation` (`structureIso = asIso structureHom`), Leaf C for
`truncation ≫ π_q`, then `comp_val_app_apply` / `whiskerLeft_val_app_apply` (explicit `Eq.trans` chains)
turn composites into nested applications on both sides. -/
theorem jetNeighborhood.thickeningCoefficient_apply_of {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L M : LineBundle Ct.toVariety) (κ q : ℕ) (hq : q ≤ κ)
    (ψ : (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf) ⟶
        (AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
          (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf))
    (hB : AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total ≫ ψ = truncatedJetAlgebra.truncation L κ ≫
      AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ))
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    (((CategoryTheory.MonoidalCategoryStruct.whiskerLeft M.toModules
          ((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
        CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨q, Nat.lt_succ_of_le hq⟩ ≫
        (truncatedJetAlgebra.pieceIso L q).hom ≫
        (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q).hom)) ≫
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules
          (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q)).inv ≫
        (L.coefficientModuleIso M q).hom).val.app (Opposite.op ⊤)).hom
        (((CategoryTheory.MonoidalCategoryStruct.whiskerLeft M.toModules ψ).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules P)) =
      (((L.coefficientModuleIso M q).hom).val.app (Opposite.op ⊤)).hom
        (((AlgebraicGeometry.Scheme.totalSpace.coefficientHom L.toModules M.toModules q).val.app (Opposite.op ⊤)).hom
          (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules P)) := by
  -- `ψ ≫ σ_κ⁻¹ = σ⁻¹ ≫ truncation` (`structureIso = asIso structureHom`).
  have hψ : ψ ≫ (AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv =
      (AlgebraicGeometry.Scheme.relativeSpec.structureIso (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).inv ≫
        truncatedJetAlgebra.truncation L κ := by
    unfold AlgebraicGeometry.Scheme.relativeSpec.structureIso
    erw [CategoryTheory.asIso_inv, CategoryTheory.asIso_inv, CategoryTheory.IsIso.comp_inv_eq,
      Category.assoc, CategoryTheory.IsIso.eq_inv_comp]
    exact hB
  -- Leaf C: the coefficient chain of the thickening after `ψ` is the coefficient chain of `Tot(L)`.
  have hmor : ψ ≫ (AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
        CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨q, Nat.lt_succ_of_le hq⟩ ≫
        (truncatedJetAlgebra.pieceIso L q).hom ≫
        (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q).hom = (AlgebraicGeometry.Scheme.relativeSpec.structureIso (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).inv ≫
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalProj q ≫
        AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower L.toModules q := by
    unfold AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower
    erw [← Category.assoc, hψ, Category.assoc, ← Category.assoc (truncatedJetAlgebra.truncation L κ),
      truncatedJetAlgebra.truncation_π L κ q hq]
    erw [Category.assoc, Category.assoc, CategoryTheory.Iso.inv_hom_id_assoc]
    rfl
  -- Section level: composites to nested applications (`comp_val_app_apply`, `whiskerLeft_val_app_apply`).
  refine (AlgebraicGeometry.Scheme.Modules.comp_val_app_apply _ _ ⊤ _).trans ?_
  refine (AlgebraicGeometry.Scheme.Modules.comp_val_app_apply _ _ ⊤ _).trans ?_
  refine (congrArg (fun z => (((L.coefficientModuleIso M q).hom).val.app (Opposite.op ⊤)).hom
    ((((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules
          (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q)).inv).val.app (Opposite.op ⊤)).hom z))
    (AlgebraicGeometry.Scheme.Modules.whiskerLeft_val_app_apply _ _ _ ⊤ _)).trans ?_
  refine (congrArg (fun c => (((L.coefficientModuleIso M q).hom).val.app (Opposite.op ⊤)).hom
    ((((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules
          (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q)).inv).val.app (Opposite.op ⊤)).hom
      (((M.toModules ◁ c).val.app (Opposite.op ⊤)).hom (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules P)))) hmor).trans ?_
  exact congrArg (fun z => (((L.coefficientModuleIso M q).hom).val.app (Opposite.op ⊤)).hom z)
    (AlgebraicGeometry.Scheme.Modules.comp_val_app_apply (M.toModules ◁ ((AlgebraicGeometry.Scheme.relativeSpec.structureIso (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).inv ≫
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalProj q ≫
        AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower L.toModules q))
      ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules
          (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q)).inv) ⊤ _).symm

namespace AlgebraicGeometry.Scheme.Modules

variable {T' T X : AlgebraicGeometry.Scheme.{u}} (h : T' ⟶ T) (g : T ⟶ X)

private theorem homEquiv_counit_app {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) (Y : D) : adj.homEquiv (G.obj Y) Y (adj.counit.app Y) = 𝟙 (G.obj Y) := by
  rw [Adjunction.homEquiv_unit]
  exact adj.right_triangle_components Y

/-- Abstract oplax-monoidal bookkeeping: for `F` oplax monoidal, `c : F A ⟶ B`, `e : N ⟶ 𝟙`, and a
unit map `u : F 𝟙 ⟶ 𝟙` satisfying right unitality,
`δ_{A,N} ≫ (c ⊗ (F e ≫ u)) = F (A ◁ e) ≫ F ρ_A ≫ c ≫ ρ_B⁻¹`. -/
private theorem oplax_δ_comp_tensorHom_map_comp_unit {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.OplaxMonoidal] {A N : C} {B : D}
    (c : F.obj A ⟶ B) (e : N ⟶ 𝟙_ C) (u : F.obj (𝟙_ C) ⟶ 𝟙_ D)
    (hu : Functor.OplaxMonoidal.δ F A (𝟙_ C) ≫ (F.obj A ◁ u) ≫ (ρ_ (F.obj A)).hom =
      F.map (ρ_ A).hom) :
    Functor.OplaxMonoidal.δ F A N ≫ (c ⊗ₘ (F.map e ≫ u)) =
      F.map (A ◁ e) ≫ F.map (ρ_ A).hom ≫ c ≫ (ρ_ B).inv := by
  rw [← hu, MonoidalCategory.tensorHom_def', MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Functor.OplaxMonoidal.δ_natural_right_assoc]
  simp only [Category.assoc]
  rw [← MonoidalCategory.rightUnitor_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-- `ψ ≫ (pushforwardComp h g).inv = g_*(h^♯)` (for `g' = h ≫ g`). -/
theorem pushforwardUnitAlong_comp_pushforwardComp_inv :
    pushforwardUnitAlong h g rfl ≫
        (pushforwardComp h g).inv.app (SheafOfModules.unit T'.ringCatSheaf) =
      (pushforward g).map (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) := by
  refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ (fun U => ?_)
  ext x
  rfl

private theorem homEquiv_map {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {A B : C} (f : A ⟶ B) :
    adj.homEquiv A (F.obj B) (F.map f) = f ≫ adj.unit.app B := by
  rw [← Category.comp_id (F.map f), Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_id]

/-- Transpose of `(pullbackUnitIso f).hom` is `f^♯` (Mathlib
`pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`). Private: the same statement exists as
`JetProjectivize.homEquiv_pullbackUnitIso_hom` (which imports this module, so cannot be reused here) and
as `TotalSpaceSectionConstructions.homEquiv_pullbackUnitIso_hom_eq`; its natural home would be
`ModulesPullbackMonoidal.lean` next to `pullback_η`. -/
private theorem homEquiv_pullbackUnitIso_hom {Y Z : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ Z) :
    (pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
  haveI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction f).isRightAdjoint
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit.{u} f.toRingCatSheafHom

theorem pullbackComp_hom_app_comp_pullback_map_pushforwardUnitAlong_comp_counit :
    (pullbackComp h g).hom.app ((pushforward g).obj (SheafOfModules.unit T.ringCatSheaf)) ≫
        (pullback (h ≫ g)).map (pushforwardUnitAlong h g rfl) ≫
        (pullbackPushforwardAdjunction (h ≫ g)).counit.app (SheafOfModules.unit T'.ringCatSheaf) =
      (pullback h).map ((pullbackPushforwardAdjunction g).counit.app
          (SheafOfModules.unit T.ringCatSheaf)) ≫
        (pullbackUnitIso h).hom := by
  refine (((pullbackPushforwardAdjunction g).comp
    (pullbackPushforwardAdjunction h)).homEquiv _ _).injective ?_
  refine (homEquiv_pullbackComp_hom_app_comp h g (B := SheafOfModules.unit T'.ringCatSheaf) _).trans ?_
  refine Eq.trans ?_ (homEquiv_comp_pullback_map_comp h g (A' := SheafOfModules.unit T.ringCatSheaf)
    (B := SheafOfModules.unit T'.ringCatSheaf) _ _).symm
  erw [Adjunction.homEquiv_naturality_left, homEquiv_counit_app, homEquiv_counit_app,
    homEquiv_pullbackUnitIso_hom]
  rw [Category.comp_id, Category.id_comp, pushforwardUnitAlong_comp_pushforwardComp_inv]
  rfl

/-- (★) -/
theorem whiskerLeft_pushforwardUnitAlong_comp_projectionFormulaHom (M : X.Modules) :
    (M ◁ pushforwardUnitAlong h g rfl) ≫
        projectionFormulaHom (h ≫ g) M (SheafOfModules.unit T'.ringCatSheaf) =
      projectionFormulaHom g M (SheafOfModules.unit T.ringCatSheaf) ≫
        (pushforward g).map ((ρ_ ((pullback g).obj M)).hom ≫
          (pullbackPushforwardAdjunction h).unit.app ((pullback g).obj M)) ≫
        (pushforwardComp h g).hom.app ((pullback h).obj ((pullback g).obj M)) ≫
        (pushforward (h ≫ g)).map ((pullbackComp h g).hom.app M ≫
          (ρ_ ((pullback (h ≫ g)).obj M)).inv) := by
  have hθg : projectionFormulaHom g M (SheafOfModules.unit T.ringCatSheaf) =
      (pullbackPushforwardAdjunction g).homEquiv _ _
        (pullbackTensorObjHom g M ((pushforward g).obj (SheafOfModules.unit T.ringCatSheaf)) ≫
          ((pullback g).obj M ◁ (pullbackPushforwardAdjunction g).counit.app
            (SheafOfModules.unit T.ringCatSheaf))) := rfl
  have hθ' : projectionFormulaHom (h ≫ g) M (SheafOfModules.unit T'.ringCatSheaf) =
      (pullbackPushforwardAdjunction (h ≫ g)).homEquiv _ _
        (pullbackTensorObjHom (h ≫ g) M
            ((pushforward (h ≫ g)).obj (SheafOfModules.unit T'.ringCatSheaf)) ≫
          ((pullback (h ≫ g)).obj M ◁ (pullbackPushforwardAdjunction (h ≫ g)).counit.app
            (SheafOfModules.unit T'.ringCatSheaf))) := rfl
  have h1 := homEquiv_pullbackComp_hom_app_comp h g
    (A := M ⊗ (pushforward g).obj (SheafOfModules.unit T.ringCatSheaf))
    ((pullbackComp h g).inv.app _ ≫
      (pullback h).map (pullbackTensorObjHom g M
          ((pushforward g).obj (SheafOfModules.unit T.ringCatSheaf)) ≫
        ((pullback g).obj M ◁ (pullbackPushforwardAdjunction g).counit.app
          (SheafOfModules.unit T.ringCatSheaf))) ≫
      (pullback h).map (ρ_ ((pullback g).obj M)).hom)
  rw [Iso.hom_inv_id_app_assoc, homEquiv_comp_pullback_map_comp, homEquiv_map] at h1
  have key : (projectionFormulaHom g M (SheafOfModules.unit T.ringCatSheaf) ≫
      (pushforward g).map ((ρ_ ((pullback g).obj M)).hom ≫
        (pullbackPushforwardAdjunction h).unit.app ((pullback g).obj M))) ≫
      (pushforwardComp h g).hom.app ((pullback h).obj ((pullback g).obj M)) =
      (pullbackPushforwardAdjunction (h ≫ g)).homEquiv _ _
        ((pullbackComp h g).inv.app _ ≫
          (pullback h).map (pullbackTensorObjHom g M
              ((pushforward g).obj (SheafOfModules.unit T.ringCatSheaf)) ≫
            ((pullback g).obj M ◁ (pullbackPushforwardAdjunction g).counit.app
              (SheafOfModules.unit T.ringCatSheaf))) ≫
          (pullback h).map (ρ_ ((pullback g).obj M)).hom) := by
    rw [hθg]
    refine (congrArg (fun t => t ≫ (pushforwardComp h g).hom.app
      ((pullback h).obj ((pullback g).obj M))) h1).trans ?_
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← Category.assoc, ← Category.assoc, key, ← Adjunction.homEquiv_naturality_right]
  refine ((pullbackPushforwardAdjunction (h ≫ g)).homEquiv _ _).symm.injective ?_
  erw [Equiv.symm_apply_apply]
  rw [Adjunction.homEquiv_naturality_left_symm, hθ']
  erw [Equiv.symm_apply_apply]
  simp only [pullbackTensorObjHom_eq_δ]
  have hT : Functor.OplaxMonoidal.δ (pullback (h ≫ g)) (self := pullbackOplaxMonoidal (h ≫ g)) M
        ((pushforward g).obj (SheafOfModules.unit T.ringCatSheaf)) =
      (pullbackComp h g).inv.app _ ≫
        (pullback h).map (Functor.OplaxMonoidal.δ (pullback g) (self := pullbackOplaxMonoidal g) M
          ((pushforward g).obj (SheafOfModules.unit T.ringCatSheaf))) ≫
        Functor.OplaxMonoidal.δ (pullback h) (self := pullbackOplaxMonoidal h) ((pullback g).obj M)
          ((pullback g).obj ((pushforward g).obj (SheafOfModules.unit T.ringCatSheaf))) ≫
        ((pullbackComp h g).hom.app M ⊗ₘ
          (pullbackComp h g).hom.app ((pushforward g).obj (SheafOfModules.unit T.ringCatSheaf))) := by
    have hT0 := pullbackComp_hom_app_pullbackTensorObjHom h g M
      ((pushforward g).obj (SheafOfModules.unit T.ringCatSheaf))
    simp only [pullbackTensorObjHom_eq_δ] at hT0
    rw [← hT0, Iso.inv_hom_id_app_assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc, ← MonoidalCategory.whiskerLeft_comp, hT]
  simp only [Category.assoc, Functor.map_comp]
  rw [← MonoidalCategory.id_tensorHom ((pullback (h ≫ g)).obj M),
    MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  refine (congrArg (fun t => _ ≫ _ ≫ _ ≫ (_ ⊗ₘ t))
    (pullbackComp_hom_app_comp_pullback_map_pushforwardUnitAlong_comp_counit h g)).trans ?_
  have hru : Functor.OplaxMonoidal.δ (pullback h) (self := pullbackOplaxMonoidal h)
        ((pullback g).obj M) (𝟙_ T.Modules) ≫
        ((pullback h).obj ((pullback g).obj M) ◁ (pullbackUnitIso h).hom) ≫
        (ρ_ ((pullback h).obj ((pullback g).obj M))).hom =
      (pullback h).map (ρ_ ((pullback g).obj M)).hom := by
    rw [← pullback_η]
    exact Functor.OplaxMonoidal.right_unitality_hom _ _
  have hR := @oplax_δ_comp_tensorHom_map_comp_unit _ _ _ _ _ _ (pullback h) (pullbackOplaxMonoidal h)
    ((pullback g).obj M) ((pullback g).obj ((pushforward g).obj (SheafOfModules.unit T.ringCatSheaf)))
    ((pullback (h ≫ g)).obj M) ((pullbackComp h g).hom.app M)
    ((pullbackPushforwardAdjunction g).counit.app (SheafOfModules.unit T.ringCatSheaf))
    (pullbackUnitIso h).hom hru
  refine (congrArg (fun t => _ ≫ _ ≫ t) hR).trans ?_
  rfl


/-- Sections at `⊤` of `g_*F ≫ (pushforwardComp h g).hom ≫ (h ≫ g)_*G`: definitionally `G ∘ F`
(`Γ(X, g_*N) = Γ(T, N)` and `pushforwardComp` is the identity on sections). -/
theorem pushforward_map_comp_pushforwardComp_hom_app_comp_pushforward_map_val_app_top
    {A : T.Modules} {C' D' : T'.Modules} (F : A ⟶ (pushforward h).obj C') (G : C' ⟶ D')
    (x : (A.val.obj (Opposite.op ⊤) : Type u)) :
    ((((pushforward g).map F ≫ (pushforwardComp h g).hom.app C' ≫
        (pushforward (h ≫ g)).map G).val.app (Opposite.op ⊤)).hom x :
        (D'.val.obj (Opposite.op ⊤) : Type u)) =
      (G.val.app (Opposite.op ⊤)).hom ((F.val.app (Opposite.op ⊤)).hom x) := rfl

/-- `pullbackSectionToPushforward` unfolded (definitional). Local copy of
`TotSectionsPolynomial.pullbackSectionToPushforward_eq`, kept private to avoid importing that module here. -/
private theorem pullbackSectionToPushforward_eq' (M : X.Modules) [M.IsLineBundle]
    (P : (((pullback g).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    pullbackSectionToPushforward g M P =
      ((projectionFormulaIso g M (SheafOfModules.unit T.ringCatSheaf)).inv.val.app
        (Opposite.op ⊤)).hom (((ρ_ ((pullback g).obj M)).inv.val.app (Opposite.op ⊤)).hom P) := rfl

/-- `e.hom (e.inv x) = x` on global sections (local copy of `TotSectionsPolynomial.app_top_inv_hom`). -/
private theorem app_top_inv_hom' {Y : AlgebraicGeometry.Scheme.{u}} {A B : Y.Modules} (e : A ≅ B)
    (x : (B.val.obj (Opposite.op ⊤) : Type u)) :
    (e.hom.val.app (Opposite.op ⊤)).hom ((e.inv.val.app (Opposite.op ⊤)).hom x) = x :=
  congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom x) e.inv_hom_id

/-- `e.inv (e.hom x) = x` on global sections (local copy of `TotSectionsPolynomial.app_top_hom_inv`). -/
private theorem app_top_hom_inv' {Y : AlgebraicGeometry.Scheme.{u}} {A B : Y.Modules} (e : A ≅ B)
    (x : (A.val.obj (Opposite.op ⊤) : Type u)) :
    (e.inv.val.app (Opposite.op ⊤)).hom ((e.hom.val.app (Opposite.op ⊤)).hom x) = x :=
  congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom x) e.hom_inv_id

end AlgebraicGeometry.Scheme.Modules

/-- **Leaf A.** Naturality of `Γ(T, g^*M) → Γ(X, M ⊗ g_*O_T)` in the morphism: for
`h : T' → T`, `g : T → X`, `g' = h ≫ g` and a line bundle `M` on `X`, pulling a global section
`P ∈ Γ(T, g^*M)` back along `h` (`sectionPullbackAlong`, then `h^*g^*M ≅ g'^*M` by `pullbackComp`) and
applying `pullbackSectionToPushforward g'` gives `M ◁ ψ` applied to `pullbackSectionToPushforward g P`,
where `ψ = g_*(h^♯) : g_*O_T → g'_*O_{T'}` (`pushforwardUnitAlong`).

Source: Stacks 01E8 (projection formula), naturality of the comparison map in the morphism; used for
Lemma 4.1 of the paper (restricting the expansion of `P_ℓ` from `Tot(L)` to `C̃_(k)(L)` keeps the
coefficients `c_{ℓ,q}` for `q ≤ k`).

---
## Natural-language proof (complete)

Write `θ_g := projectionFormulaHom g M O_T : M ⊗ g_*O_T ⟶ g_*(g^*M ⊗ O_T)` (an isomorphism because
`M` is a line bundle, `projectionFormulaHom_isIso`; `projectionFormulaIso = asIso θ_g`), `ρ` for the
right unitor, `η_h : g^*M ⟶ h_*h^*g^*M` for the unit of `h^* ⊣ h_*` (this is what
`sectionPullbackAlong h` applies on global sections, `AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback`), and
`κ : h^*g^*M ⟶ g'^*M` for `(pullbackComp h g).app M ≫ eqToHom (… e)`.

By definition `pullbackSectionToPushforward g P = θ_g⁻¹ (ρ⁻¹ P)` on global sections, and
`Γ(X, g_*N) = Γ(T, N)` definitionally. So the claim is the global-sections instance of the following
identity of morphisms `M ⊗ g_*O_T ⟶ g'_*(g'^*M ⊗ O_{T'})` in `X.Modules`:

  (★)  `(M ◁ ψ) ≫ θ_{g'} = θ_g ≫ g_*(ρ_{g^*M}) ≫ g_*(η_h) ≫ (pushforwardComp h g).hom ≫ eqToHom(e) ≫ g'_*(κ) ≫ g'_*(ρ⁻¹_{g'^*M})`.

Indeed, apply both sides of (★) to `θ_g⁻¹(ρ⁻¹ P)`: the left side gives `θ_{g'}((M ◁ ψ)(PSP_g P))`, the
right side gives `g'_*(ρ⁻¹)(κ(η_h P))` (using `θ_g ∘ θ_g⁻¹ = id` and `ρ ∘ ρ⁻¹ = id`), and applying
`θ_{g'}⁻¹` yields exactly the statement.

### Step 1: transpose along `g'^* ⊣ g'_*`
Both sides of (★) are maps into `g'_*(g'^*M ⊗ O_{T'})`; by the adjunction `g'^* ⊣ g'_*` it suffices to
compare their transposes `g'^*(M ⊗ g_*O_T) ⟶ g'^*M ⊗ O_{T'}`.

* Left side. `θ_{g'} = T'(δ'_{M, g'_*O} ≫ (g'^*M ◁ ε'_{O_{T'}}))` with `δ'` = `pullbackTensorObjHom g'`
  (oplax monoidal structure of `g'^*`) and `ε'` the counit. By `Adjunction.homEquiv_naturality_left_symm`
  the transpose of `(M ◁ ψ) ≫ θ_{g'}` is `g'^*(M ◁ ψ) ≫ δ'_{M,g'_*O} ≫ (g'^*M ◁ ε'_O)`, and by naturality
  of `δ'` in its second variable this is `δ'_{M, g_*O_T} ≫ (g'^*M ◁ (g'^*ψ ≫ ε'_{O_{T'}}))`.
* Right side. Transposing `θ_g ≫ g_*(F) ≫ comp ≫ eqToHom ≫ g'_*(G)` (with `F = ρ ≫ η_h`,
  `G = κ ≫ ρ⁻¹`): by `homEquiv_naturality_right` the `g'_*(G)` peels off as `… ≫ G`; the adjunction
  `g'^* ⊣ g'_*` is conjugate to the composite adjunction `(g^* then h^*) ⊣ (h_* then g_*)` via
  `pullbackComp`/`pushforwardComp` (Mathlib `AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`),
  so the transpose of `θ_g ≫ g_*(F) ≫ comp.hom` along `g'^* ⊣ g'_*` equals `(pullbackComp h g).inv.app ≫`
  the transpose along the composite adjunction, which is `h^*(transpose_g(θ_g ≫ g_*F)) ≫ ε_h`
  (`Adjunction.comp` unit/counit formulas). Finally `transpose_g(θ_g ≫ g_*F) = transpose_g(θ_g) ≫ F =
  δ_{M,g_*O} ≫ (g^*M ◁ ε_g) ≫ ρ ≫ η_h` (`homEquiv_naturality_right`, `homEquiv_symm_apply` on the
  definition of `projectionFormulaHom`). The triangle identity `h^*(η_h) ≫ ε_h = 𝟙` kills `η_h`.
  Result: `(pullbackComp h g).inv ≫ h^*(δ_{M,g_*O} ≫ (g^*M ◁ ε_g) ≫ ρ_{g^*M}) ≫ κ ≫ ρ⁻¹_{g'^*M}`.

### Step 2: the two transposes agree
Using the compatibility of the oplax structure with composition
(`pullbackComp_hom_app_pullbackTensorObjHom`, `ModulesPullbackCompMonoidal`):
`δ'_{A,B} = (pullbackComp h g).inv ≫ h^*(δ_{A,B}) ≫ δ^h_{g^*A, g^*B} ≫ (κ_A ⊗ κ_B)` (with `κ_A`, `κ_B`
the `pullbackComp` isomorphisms), together with the formula for the counit of the composite
adjunction `ε' = (pullbackComp).inv ≫ h^*(ε_g) ≫ ε_h` (again `conjugateEquiv_pullbackComp_inv`), the
left transpose becomes
`(pullbackComp).inv ≫ h^*(δ_{M,g_*O}) ≫ δ^h ≫ (κ_M ⊗ κ_{g_*O}) ≫ (g'^*M ◁ (g'^*ψ ≫ (pullbackComp).inv ≫ h^*(ε_g) ≫ ε_h))`.
Now `g'^*ψ ≫ (pullbackComp).inv ≫ h^*ε_g ≫ ε_h : g'^*(g_*O_T) ⟶ O_{T'}`, precomposed with `κ_{g_*O}`,
is `h^*(g^*g_*O_T) → h^*O_T → O_{T'}`, namely `h^*(ε_g) ≫ (h^*O_T → O_{T'})` where the last map is
the transpose of `h^♯ = unitToPushforwardObjUnit` (Mathlib
`SheafOfModules.pullbackPushforwardAdjunction_homEquiv_symm_unitToPushforwardObjUnit`,
`pullbackObjUnitToUnit`). The right transpose contains `h^*(ρ_{g^*M}) ≫ κ ≫ ρ⁻¹`; by the (right)
unitality of the oplax structure of `h^*` — `h^*(ρ_A) = δ^h_{A,O_T} ≫ (h^*A ◁ pullbackObjUnitToUnit) ≫ ρ_{h^*A}`
(Mathlib `Functor.OplaxMonoidal.right_unitality` for `(pullback h).oplaxMonoidal`, cf.
`leftAdjointOplaxMonoidal` in `PresheafModulesPushforwardMonoidal.lean`) — the two sides coincide after
cancelling `ρ ≫ ρ⁻¹` and using naturality of `δ^h` in the first variable to move `κ_M` past it. ∎

---
## How the proof is organised in this file
1. `subst e` (so `g' = h ≫ g`, and both transports `eqToHom` are `𝟙`).
2. `pullbackComp_hom_app_comp_pullback_map_pushforwardUnitAlong_comp_counit` (Step 2's identity
   `c_{g_*O} ≫ g'^*ψ ≫ ε' = h^*ε_g ≫ (pullbackUnitIso h).hom`): transpose along the composite adjunction
   with `homEquiv_pullbackComp_hom_app_comp` / `homEquiv_comp_pullback_map_comp`
   (`ModulesPullbackCompMonoidal.lean`) and `homEquiv_pullbackUnitIso_hom`
   (Mathlib `pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`).
3. `whiskerLeft_pushforwardUnitAlong_comp_projectionFormulaHom` is (★): transpose along `g'^* ⊣ g'_*`
   (`homEquiv_naturality_left_symm` / `_right`, `homEquiv_pullbackComp_hom_app_comp`), then
   `pullbackComp_hom_app_pullbackTensorObjHom`, `δ_natural_right`, item 2, and the right unitality of
   the oplax structure (`right_unitality_hom` + `pullback_η`) packaged in the abstract lemma
   `oplax_δ_comp_tensorHom_map_comp_unit`.
4. Sections: `pushforward_map_comp_pushforwardComp_hom_app_comp_pushforward_map_val_app_top` (`rfl`),
   `comp_val_app_apply`, and `e.hom (e.inv x) = x` on global sections; all steps are root-level
   `Eq.trans`/`congrArg` instantiations (no `rw` on the concrete goal: `kabstract` on `≫`-patterns unfolds
   the sheaf structures and times out here). -/
theorem AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_comp
    {T' T X : AlgebraicGeometry.Scheme.{u}} (h : T' ⟶ T) (g : T ⟶ X) {g' : T' ⟶ X}
    (e : h ≫ g = g') (M : X.Modules) [M.IsLineBundle]
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward g' M
      (((((AlgebraicGeometry.Scheme.Modules.pullbackComp h g).app M).hom ≫
        CategoryTheory.eqToHom (congrArg (fun f => (AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
          e)).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong h P)) =
    (((M ◁ AlgebraicGeometry.Scheme.Modules.pushforwardUnitAlong h g e).val.app (Opposite.op ⊤)).hom
      (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward g M P)) := by
  open AlgebraicGeometry.Scheme.Modules in
  subst e
  have hstar := whiskerLeft_pushforwardUnitAlong_comp_projectionFormulaHom h g M
  -- the transported section is `c_M (η_h P)` (definitional: `eqToHom rfl = 𝟙`)
  have hQ : ((((pullbackComp h g).app M).hom ≫
        eqToHom (congrArg (fun f => (pullback f).obj M) (rfl : h ≫ g = h ≫ g))).val.app
          (Opposite.op ⊤)).hom (sectionPullbackAlong h P) =
      (((pullbackComp h g).hom.app M).val.app (Opposite.op ⊤)).hom
        ((((pullbackPushforwardAdjunction h).unit.app ((pullback g).obj M)).val.app
          (Opposite.op ⊤)).hom P) := rfl
  refine (congrArg (pullbackSectionToPushforward (h ≫ g) M) hQ).trans ?_
  refine (pullbackSectionToPushforward_eq' (h ≫ g) M _).trans ?_
  refine Eq.trans ?_ (app_top_hom_inv'
    (projectionFormulaIso (h ≫ g) M (SheafOfModules.unit T'.ringCatSheaf)) _)
  refine congrArg (fun z => (((projectionFormulaIso (h ≫ g) M
    (SheafOfModules.unit T'.ringCatSheaf)).inv.val.app (Opposite.op ⊤)).hom z)) ?_
  refine Eq.trans ?_ (comp_val_app_apply (M ◁ pushforwardUnitAlong h g rfl)
    (projectionFormulaHom (h ≫ g) M (SheafOfModules.unit T'.ringCatSheaf)) ⊤
    (pullbackSectionToPushforward g M P))
  refine Eq.trans ?_ (congrArg (fun t => ((t.val.app (Opposite.op ⊤)).hom
    (pullbackSectionToPushforward g M P) :
      (((pushforward (h ≫ g)).obj ((pullback (h ≫ g)).obj M ⊗
        SheafOfModules.unit T'.ringCatSheaf)).val.obj (Opposite.op ⊤) : Type u))) hstar).symm
  refine Eq.trans ?_ (comp_val_app_apply _ _ ⊤ _).symm
  refine Eq.trans ?_
    (pushforward_map_comp_pushforwardComp_hom_app_comp_pushforward_map_val_app_top h g _ _ _).symm
  have hx : ((projectionFormulaHom g M (SheafOfModules.unit T.ringCatSheaf)).val.app
        (Opposite.op ⊤)).hom (pullbackSectionToPushforward g M P) =
      ((ρ_ ((pullback g).obj M)).inv.val.app (Opposite.op ⊤)).hom P :=
    app_top_inv_hom' (projectionFormulaIso g M (SheafOfModules.unit T.ringCatSheaf)) _
  refine Eq.trans ?_ (congrArg (fun z =>
    ((((pullbackComp h g).hom.app M ≫ (ρ_ ((pullback (h ≫ g)).obj M)).inv).val.app
      (Opposite.op ⊤)).hom
      ((((ρ_ ((pullback g).obj M)).hom ≫
        (pullbackPushforwardAdjunction h).unit.app ((pullback g).obj M)).val.app
          (Opposite.op ⊤)).hom z))) hx).symm
  refine Eq.trans ?_ (comp_val_app_apply ((pullbackComp h g).hom.app M)
    (ρ_ ((pullback (h ≫ g)).obj M)).inv ⊤ _).symm
  refine congrArg (fun z => (((ρ_ ((pullback (h ≫ g)).obj M)).inv.val.app (Opposite.op ⊤)).hom
    ((((pullbackComp h g).hom.app M).val.app (Opposite.op ⊤)).hom z))) ?_
  refine Eq.trans ?_ (comp_val_app_apply (ρ_ ((pullback g).obj M)).hom
    ((pullbackPushforwardAdjunction h).unit.app ((pullback g).obj M)) ⊤ _).symm
  exact (congrArg (fun z => ((((pullbackPushforwardAdjunction h).unit.app
    ((pullback g).obj M)).val.app (Opposite.op ⊤)).hom z))
    (app_top_inv_hom' (ρ_ ((pullback g).obj M)) P)).symm

/-- The section map of Leaf A: pull a global section of `g^*M` back along `h` and identify
`h^*g^*M ≅ (h ≫ g)^*M = g'^*M` (`pullbackComp`, then transport along `hZ`). Kept as a (non-reducible)
definition with all implicit arguments as parameters, so that `restrictToThickening` is literally an
instance of it and Leaf A applies by a one-step unfolding. It must not be an `abbrev`: two instances
whose implicit scheme arguments are spelled differently (`C.toScheme` vs `C.toVariety.carrier`) would then
be unfolded by the unifier before their arguments are compared, which does not terminate in practice. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.restrictSectionAlong
    {T' T X : AlgebraicGeometry.Scheme.{u}} (h : T' ⟶ T) (g : T ⟶ X) {g' : T' ⟶ X} (M : X.Modules)
    (hZ : (AlgebraicGeometry.Scheme.Modules.pullback (h ≫ g)).obj M =
      (AlgebraicGeometry.Scheme.Modules.pullback g').obj M)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    (((AlgebraicGeometry.Scheme.Modules.pullback g').obj M).val.obj (Opposite.op ⊤) : Type u) :=
  ((((AlgebraicGeometry.Scheme.Modules.pullbackComp h g).app M).hom ≫
    CategoryTheory.eqToHom hZ).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong h P)

/-- `pullbackSectionToPushforward_comp` with the transport `eqToHom` taken along an arbitrary proof `hZ`
of the object equation (proof irrelevance), phrased with `restrictSectionAlong`. -/
theorem AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_comp'
    {T' T X : AlgebraicGeometry.Scheme.{u}} (h : T' ⟶ T) (g : T ⟶ X) {g' : T' ⟶ X}
    (e : h ≫ g = g') (M : X.Modules) [M.IsLineBundle]
    (hZ : (AlgebraicGeometry.Scheme.Modules.pullback (h ≫ g)).obj M =
      (AlgebraicGeometry.Scheme.Modules.pullback g').obj M)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward g' M
      (AlgebraicGeometry.Scheme.Modules.restrictSectionAlong h g M hZ P) =
    (((M ◁ AlgebraicGeometry.Scheme.Modules.pushforwardUnitAlong h g e).val.app (Opposite.op ⊤)).hom
      (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward g M P)) :=
  AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_comp h g e M P

end
