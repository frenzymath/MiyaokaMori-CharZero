import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotSectionsPolynomial

/-! # Pullbacks of base morphisms do not raise the ξ-degree

Pulling back a morphism `ζ : A ⟶ B` of line bundles on the base `C` to `Tot(L)` and applying it to a
global section of `p^*A` does not raise the ξ-degree. This is the "naturality of the ξ-expansion in the
coefficient bundle" needed to transport ξ-degree bounds along the canonical isomorphisms
`p^*(M^e ⊗ M) ≅ p^*(M^{e+1})` (`SubstitutedPolynomialDegreeBridge_Canonical`). (Implicit in the paper, which
identifies `p^*A^{⊗d}` with `p^*(A^d)` and reads ξ-coefficients in `H^0(C̃, ρ^*A^{⊗d} ⊗ L^{-q})`.)

Structure of the proof:
* `projectionFormulaIso_inv_naturality_left`: naturality in `M` of `θ_M⁻¹` (from the abstract
  `Adjunction.projFormulaHom_naturality_left`).
* `xiCoefficientMap`: the induced map `ζ_q : A^1 ⊗ L^{-q} ⟶ B^1 ⊗ L^{-q}`.
* `coefficientHom_naturality_left`: `(ζ ▷ p_*O) ≫ coefficientHom_B ≫ cMI_B = coefficientHom_A ≫ cMI_A ≫ ζ_q`
  (whisker exchange + the two `tensorIsoTensorObj` factors cancel; pure monoidal bookkeeping).
* `xiCoefficient_chain_naturality`, `xiCoefficient_pullback_map`: the coefficient formula
  `xiCoefficient L B (p^*ζ Q) q = ζ_q (xiCoefficient L A Q q)` (right-unitor naturality + the above,
  evaluated on global sections; `app_top_comp` and `pushforward_map_app` are `rfl`).
* `xiDegree_pullback_map_le`: `Finset.max_le` + `Finset.le_max` + `map_zero`.

Tooling note: in goals containing `SheafOfModules.unit T.ringCatSheaf`, `rw`/`simp` fail
silently or with "Did not find an occurrence … Application type mismatch: TopCat.Sheaf RingCat … expected
Sheaf (Opens.grothendieckTopology …)", because the motive type-check cannot unfold `TopCat.Sheaf` at reducible
transparency (`backward.isDefEq.respectTransparency`). `set_option
backward.isDefEq.respectTransparency false in` (as Mathlib does in `AlgebraicGeometry/Modules/Sheaf.lean`)
makes `simp` work again; where even that fails, obtain the equation by `congrArg` on the morphism-level
identity and close by `exact` (defeq).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
-- Needed for `rw`/`simp` in goals containing `SheafOfModules.unit T.ringCatSheaf` (see the tooling note above).
set_option backward.isDefEq.respectTransparency false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

/-- **Naturality in `M` of the inverse projection-formula isomorphism.**
For `g : M ⟶ M'` (both line bundles), `f_*(f^*g ▷ N) ≫ θ_{M'}⁻¹ = θ_M⁻¹ ≫ (g ▷ f_*N)`.
Proof: rearrange to `(g ▷ f_*N) ≫ θ_{M'} = θ_M ≫ f_*(f^*g ▷ N)`, which is
`Adjunction.projFormulaHom_naturality_left` for the adjunction `f^* ⊣ f_*` with the oplax structure
`pullbackOplaxMonoidal f` (`projectionFormulaHom_eq_projFormulaHom` is `rfl`). -/
theorem AlgebraicGeometry.Scheme.Modules.projectionFormulaIso_inv_naturality_left
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) {M M' : Y.Modules} [M.IsLineBundle] [M'.IsLineBundle]
    (g : M ⟶ M') (N : X.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pushforward f).map
        ((AlgebraicGeometry.Scheme.Modules.pullback f).map g ▷ N) ≫
        (AlgebraicGeometry.Scheme.Modules.projectionFormulaIso f M' N).inv =
      (AlgebraicGeometry.Scheme.Modules.projectionFormulaIso f M N).inv ≫
        (g ▷ (AlgebraicGeometry.Scheme.Modules.pushforward f).obj N) := by
  rw [Iso.comp_inv_eq, Category.assoc, eq_comm, Iso.inv_comp_eq]
  exact (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).projFormulaHom_naturality_left
    (instF := AlgebraicGeometry.Scheme.Modules.pullbackOplaxMonoidal f) g N

/-- The map induced by `ζ : A ⟶ B` on the coefficient line bundles,
`ζ_q : (A^1 ⊗ L^{-q}) ⟶ (B^1 ⊗ L^{-q})`: conjugate `ζ` by `zpowOneIso`, whisker with `L^{-q}`, and move
between `LineBundle.tensor` and the monoidal `⊗` by `tensorIsoTensorObj`. -/
noncomputable def xiCoefficientMap {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L A B : LineBundle C.toVariety) (ζ : A.toModules ⟶ B.toModules) (q : ℕ) :
    ((A.zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules ⟶
      ((B.zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules :=
  (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (A.zpow 1).toModules
      (L.zpow (-(q : ℤ))).toModules).hom ≫
    ((A.zpowOneIso.hom ≫ ζ ≫ B.zpowOneIso.inv) ▷ (L.zpow (-(q : ℤ))).toModules) ≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (B.zpow 1).toModules
      (L.zpow (-(q : ℤ))).toModules).inv

/-- **Naturality of the coefficient morphism in the coefficient bundle**:
`(ζ ▷ p_*O_Tot) ≫ coefficientHom_B ≫ cMI_B = coefficientHom_A ≫ cMI_A ≫ ζ_q`.
Proof: unfold; the two `tensorIsoTensorObj` factors `(tITO M T_q).inv ≫ (tITO M N_q).hom` cancel
(`T_q = (L^∨)^{⊗q}` and `N_q = moduleNegativePower L q` are definitionally equal, so `Iso.inv_hom_id`
applies by `exact`, not by `rw`); what remains is the whisker exchange law written with `tensorHom`:
both sides are `((ζ ≫ zpowOneIso_B⁻¹) ⊗ₘ (σ_q ≫ zpowNegIso⁻¹)) ≫ (tITO B^1 L^{-q}).inv`. -/
theorem coefficientHom_naturality_left {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L A B : LineBundle C.toVariety) (ζ : A.toModules ⟶ B.toModules) (q : ℕ) :
    (ζ ▷ (AlgebraicGeometry.Scheme.Modules.pushforward
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)) ≫
      AlgebraicGeometry.Scheme.totalSpace.coefficientHom L.toModules B.toModules q ≫
      (L.coefficientModuleIso B q).hom =
    AlgebraicGeometry.Scheme.totalSpace.coefficientHom L.toModules A.toModules q ≫
      (L.coefficientModuleIso A q).hom ≫ xiCoefficientMap L A B ζ q := by
  have hc : ∀ M : C.toScheme.Modules,
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M
          (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q)).inv ≫
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M
          (AlgebraicGeometry.Scheme.Modules.moduleNegativePower L.toModules q)).hom = 𝟙 _ :=
    fun M => Iso.inv_hom_id _
  unfold AlgebraicGeometry.Scheme.totalSpace.coefficientHom LineBundle.coefficientModuleIso xiCoefficientMap
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hc,
    MonoidalCategory.tensorIso_hom, ← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]

/-- Naturality in `M` of the whole coefficient chain
`p_*(p^*M ⊗ O_Tot) ⟶ M ⊗ p_*O_Tot ⟶ coefficientLineModule ⟶ M^1 ⊗ L^{-q}` (projection formula inverse,
then `coefficientHom_naturality_left`). -/
theorem xiCoefficient_chain_naturality {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L A B : LineBundle C.toVariety) (ζ : A.toModules ⟶ B.toModules) (q : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map ζ ▷
          SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf) ≫
      (AlgebraicGeometry.Scheme.Modules.projectionFormulaIso (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
        B.toModules (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)).inv ≫
      AlgebraicGeometry.Scheme.totalSpace.coefficientHom L.toModules B.toModules q ≫
      (L.coefficientModuleIso B q).hom =
    (AlgebraicGeometry.Scheme.Modules.projectionFormulaIso (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
        A.toModules (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)).inv ≫
      AlgebraicGeometry.Scheme.totalSpace.coefficientHom L.toModules A.toModules q ≫
      (L.coefficientModuleIso A q).hom ≫ xiCoefficientMap L A B ζ q := by
  rw [← Category.assoc, AlgebraicGeometry.Scheme.Modules.projectionFormulaIso_inv_naturality_left,
    Category.assoc, coefficientHom_naturality_left]

/-- **ξ-coefficients are natural in the coefficient bundle**:
`xiCoefficient L B (p^*ζ Q) q = ζ_q (xiCoefficient L A Q q)`.
Proof: `xiCoefficient = cMI ∘ coefficientHom ∘ θ⁻¹ ∘ ρ⁻¹` on global sections. The right unitor is natural
(`rightUnitor_inv_naturality`: `p^*ζ ≫ ρ⁻¹ = ρ⁻¹ ≫ (p^*ζ ▷ O)`), and `((p^*ζ ▷ O).val.app ⊤)` is
definitionally `(p_*(p^*ζ ▷ O)).val.app ⊤` (`pushforward_map_app` is `rfl`); then apply
`xiCoefficient_chain_naturality` on global sections (`app_top_comp` is `rfl`). -/
theorem xiCoefficient_pullback_map {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L A B : LineBundle C.toVariety) (ζ : A.toModules ⟶ B.toModules)
    (Q : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        A.toModules).val.obj (Opposite.op ⊤) : Type u)) (q : ℕ) :
    xiCoefficient L B (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map ζ).app ⊤ Q) q =
      ((xiCoefficientMap L A B ζ q).val.app (Opposite.op ⊤)).hom (xiCoefficient L A Q q) := by
  have hρ : ((ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj B.toModules)).inv.val.app
          (Opposite.op ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map ζ).val.app (Opposite.op ⊤)).hom Q) =
      (((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map ζ ▷
          SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf).val.app
            (Opposite.op ⊤)).hom
        (((ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj A.toModules)).inv.val.app
            (Opposite.op ⊤)).hom Q) := by
    exact congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom Q)
      (MonoidalCategory.rightUnitor_inv_naturality ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map ζ))
  have h := congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom
      (((ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj A.toModules)).inv.val.app
          (Opposite.op ⊤)).hom Q))
    (xiCoefficient_chain_naturality L A B ζ q)
  unfold xiCoefficient AlgebraicGeometry.Scheme.totalSpace.coefficient
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward
  refine (congrArg (fun y => (((L.coefficientModuleIso B q).hom.val.app (Opposite.op ⊤)).hom
    (((AlgebraicGeometry.Scheme.totalSpace.coefficientHom L.toModules B.toModules q).val.app
      (Opposite.op ⊤)).hom
      (((AlgebraicGeometry.Scheme.Modules.projectionFormulaIso
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom B.toModules
        (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)).inv.val.app
          (Opposite.op ⊤)).hom y)))) hρ).trans ?_
  exact h

/-- **ξ-degree is not raised by the pullback of a base morphism.**

Proof: `xiDegree = max` of the (finite) support of the ξ-coefficients. By `Finset.max_le` it suffices that
every `q` with `xiCoefficient L B (p^*ζ Q) q ≠ 0` satisfies `(q : WithBot ℕ) ≤ xiDegree L A Q`; by
`Finset.le_max` it suffices that `xiCoefficient L A Q q ≠ 0`, and indeed if it were `0` then by
`xiCoefficient_pullback_map` the coefficient of `p^*ζ Q` would be `ζ_q 0 = 0` (`map_zero`).
(The `⊥` case, `Q = 0`, is covered: the support of `p^*ζ Q` is then empty.)

Note: for an *isomorphism* `ζ` the statement is also a special case of
`xiDegree_pullbackIso_hom_app_le`; this lemma is kept separate because it needs no integrality argument. -/
theorem xiDegree_pullback_map_le {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L A B : LineBundle C.toVariety) (ζ : A.toModules ⟶ B.toModules)
    (Q : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        A.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    xiDegree L B (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map ζ).app ⊤ Q) ≤ xiDegree L A Q := by
  unfold xiDegree
  apply Finset.max_le
  intro q hq
  apply Finset.le_max
  rw [Set.Finite.mem_toFinset] at hq ⊢
  intro h0
  apply hq
  rw [xiCoefficient_pullback_map, h0, map_zero]

end
