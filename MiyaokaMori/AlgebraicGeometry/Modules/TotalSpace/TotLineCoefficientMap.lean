import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesMonoidalZero
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesProjectionFormulaHom
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecStructureIso
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedAlgebraTotalProjection
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymPowLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle

/-! # The ξ-coefficient maps on the total space of a line bundle

The `q`-th ξ-coefficient `Γ(Tot, p^*M) → Γ(X, M ⊗ (L^∨)^{⊗q})` of a global section of `p^*M` on
`Tot(L) = Spec_X Sym(L^∨)`, and the monomials `c ↦ c·ξ^q` in the other direction; for a general affine
morphism, `Γ(T, g^*M) ↔ Γ(X, M ⊗ g_*O_T)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/- Notation: `p : Tot(L) → X`, `S = Sym(L^∨)`, `Tot(L) = Spec_X (⊕_m S_m)`, `T_q = moduleTensorPower (L^∨) q = (L^∨)^{⊗q}`.
   The coefficient module is `coefficientLineModule M L q = Modules.tensor M T_q`. -/

/- Comparison of the pieces `S_q → T_q` (`L^∨` a line bundle): `Sym^q →` monoidal tensor power `→` tensor power. -/

noncomputable def AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (q : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L)).part q ⟶
      AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L) q :=
  AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow (AlgebraicGeometry.Scheme.Modules.dual L) q ≫
    (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual L) q).hom

/- The other direction `T_q → S_q`: tensor power `→` monoidal tensor power `→` quotient map to `Sym^q` (the dual of a
   line bundle is a line bundle, hence quasi-coherent, so `symGradedAlgebra` is in the quasi-coherent branch). -/

noncomputable def AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (q : ℕ) :
    AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L) q ⟶
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L)).part q :=
  (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual L) q).inv ≫ by
    have hW : (AlgebraicGeometry.Scheme.Modules.dual L).IsQuasicoherent := inferInstance
    unfold AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
    rw [dif_pos hW]
    exact AlgebraicGeometry.Scheme.Modules.symPowπ (AlgebraicGeometry.Scheme.Modules.dual L) q

/- The module morphism of the `q`-th coefficient `M ⊗ p_*O_Tot → M ⊗ T_q → Modules.tensor M T_q`:
   `p_*O_Tot ≅ ⊕ S_m` (the inverse of `relativeSpec.structureIso`), the `q`-th graded projection, `S_q → T_q`. -/

noncomputable def AlgebraicGeometry.Scheme.totalSpace.coefficientHom {X : AlgebraicGeometry.Scheme.{u}}
    (L M : X.Modules) [L.IsLineBundle] (q : ℕ) :
    M ⊗ (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L).hom).obj
        (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf) ⟶
      AlgebraicGeometry.Scheme.Modules.coefficientLineModule M L q :=
  (M ◁ ((AlgebraicGeometry.Scheme.relativeSpec.structureIso
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L)).total).inv ≫
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L)).totalProj q ≫
      AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower L q)) ≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M
      (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L) q)).inv

/- The other direction (monomials) `Modules.tensor M T_q → M ⊗ p_*O_Tot`: `T_q → S_q`, the `q`-th graded inclusion,
   the structure map `⊕ S_m → p_*O_Tot`. -/

noncomputable def AlgebraicGeometry.Scheme.totalSpace.monomialHom {X : AlgebraicGeometry.Scheme.{u}}
    (L M : X.Modules) [L.IsLineBundle] (q : ℕ) :
    AlgebraicGeometry.Scheme.Modules.coefficientLineModule M L q ⟶
      M ⊗ (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L).hom).obj
        (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf) :=
  (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M
      (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L) q)).hom ≫
    (M ◁ (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L q ≫
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L)).totalIncl q ≫
      AlgebraicGeometry.Scheme.relativeSpec.structureHom
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L)).total))

/- For a general affine morphism `g : T → X`: `Γ(T, g^*M) → Γ(X, M ⊗ g_*O_T)`,
   `P ↦ P ⊗ 1 ∈ Γ(T, g^*M ⊗ O_T) = Γ(X, g_*(g^*M ⊗ O_T))`, then the inverse of the projection formula
   isomorphism (`M` a line bundle). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward {T X : AlgebraicGeometry.Scheme.{u}}
    (g : T ⟶ X) (M : X.Modules) [M.IsLineBundle]
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    ((M ⊗ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit T.ringCatSheaf)).val.obj (Opposite.op ⊤) : Type u) :=
  ((AlgebraicGeometry.Scheme.Modules.projectionFormulaIso g M (SheafOfModules.unit T.ringCatSheaf)).inv.val.app
      (Opposite.op ⊤)).hom
    (show (((AlgebraicGeometry.Scheme.Modules.pushforward g).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M ⊗ SheafOfModules.unit T.ringCatSheaf)).val.obj
          (Opposite.op ⊤) : Type u) from
      ((ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)).inv.val.app (Opposite.op ⊤)).hom P)

/- The other direction `Γ(X, M ⊗ g_*O_T) → Γ(T, g^*M)`: the projection formula comparison morphism (forward
   direction, no line bundle hypothesis needed), then remove `⊗ O_T`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback {T X : AlgebraicGeometry.Scheme.{u}}
    (g : T ⟶ X) (M : X.Modules)
    (s : ((M ⊗ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit T.ringCatSheaf)).val.obj (Opposite.op ⊤) : Type u)) :
    (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).val.obj (Opposite.op ⊤) : Type u) :=
  ((ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)).hom.val.app (Opposite.op ⊤)).hom
    (show (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M ⊗
        SheafOfModules.unit T.ringCatSheaf).val.obj (Opposite.op ⊤) : Type u) from
      ((AlgebraicGeometry.Scheme.Modules.projectionFormulaHom g M (SheafOfModules.unit T.ringCatSheaf)).val.app
        (Opposite.op ⊤)).hom s)

/- The `q`-th ξ-coefficient `∈ Γ(X, M ⊗ (L^∨)^{⊗q})` of a global section of `p^*M` on `Tot(L)`. -/

noncomputable def AlgebraicGeometry.Scheme.totalSpace.coefficient {X : AlgebraicGeometry.Scheme.{u}}
    (L M : X.Modules) [L.IsLineBundle] [M.IsLineBundle] (q : ℕ)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).obj M).val.obj
      (Opposite.op ⊤) : Type u)) :
    ((AlgebraicGeometry.Scheme.Modules.coefficientLineModule M L q).val.obj (Opposite.op ⊤) : Type u) :=
  ((AlgebraicGeometry.Scheme.totalSpace.coefficientHom L M q).val.app (Opposite.op ⊤)).hom
    (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward
      (AlgebraicGeometry.Scheme.totalSpace L).hom M P)

/- The monomial `c·ξ^q ∈ Γ(Tot(L), p^*M)`, `c ∈ Γ(X, M ⊗ (L^∨)^{⊗q})`. -/

noncomputable def AlgebraicGeometry.Scheme.totalSpace.monomial {X : AlgebraicGeometry.Scheme.{u}}
    (L M : X.Modules) [L.IsLineBundle] (q : ℕ)
    (c : ((AlgebraicGeometry.Scheme.Modules.coefficientLineModule M L q).val.obj (Opposite.op ⊤) : Type u)) :
    (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L).hom).obj M).val.obj
      (Opposite.op ⊤) : Type u) :=
  AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback (AlgebraicGeometry.Scheme.totalSpace L).hom M
    (((AlgebraicGeometry.Scheme.totalSpace.monomialHom L M q).val.app (Opposite.op ⊤)).hom c)


/-- **Θ_q ≫ Θ'_q = 𝟙**: `tensorPowerToSymPart L q ≫ symPartToTensorPower L q = 𝟙` (step 4 of the proof of
`coefficient_monomial`). Both morphisms are the quasi-coherent branch of `symGradedAlgebra (dual L)`
(`dual L` is a line bundle, hence quasi-coherent); after `generalize`/`subst` of
`symGradedAlgebra = symGradedAlgebraOfQC` this is `symPowπ ≫ inv symPowπ = 𝟙` (`IsIso.hom_inv_id`).
Same content as `tensorPowerToSymPart_symPartToMonoidalPow` (`JetWeightComponentEqCoefficient`,
downstream) followed by `powIso.hom`; proved here directly because that module imports this one. -/
theorem AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart_comp_symPartToTensorPower
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle] (q : ℕ) :
    AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L q ≫
      AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower L q = 𝟙 _ := by
  have hq : (AlgebraicGeometry.Scheme.Modules.dual L).IsQuasicoherent := inferInstance
  unfold AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart
    AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow
  rw [Category.assoc, Iso.inv_comp_eq, Category.comp_id, ← Category.assoc]
  refine (congrArg (fun t => t ≫ (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
    (AlgebraicGeometry.Scheme.Modules.dual L) q).hom) ?_).trans (Category.id_comp _)
  generalize_proofs _ _ pf3 pf4 pf5 pf6
  have hS : AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L) =
      AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC (AlgebraicGeometry.Scheme.Modules.dual L) hq := by
    delta AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
    exact dif_pos hq
  change (pf4 pf3).mpr (AlgebraicGeometry.Scheme.Modules.symPowπ (AlgebraicGeometry.Scheme.Modules.dual L) q) ≫
    (pf5 pf3).mpr (@CategoryTheory.inv _ _ _ _
      (AlgebraicGeometry.Scheme.Modules.symPowπ (AlgebraicGeometry.Scheme.Modules.dual L) q) (pf6 pf3)) = 𝟙 _
  generalize AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L) = S
    at hS pf4 pf5 ⊢
  subst hS
  exact CategoryTheory.IsIso.hom_inv_id
    (AlgebraicGeometry.Scheme.Modules.symPowπ (AlgebraicGeometry.Scheme.Modules.dual L) q)

/-- Variable-level bridge: `(τ.hom ≫ (Q ◁ u)) ≫ (Q ◁ v) ≫ τ'.inv = 0` when `u ≫ v = 0`
(`whiskerLeft_comp` + `whiskerLeft_zeroMorphism`). Stated on variables because `rw [whiskerLeft_comp]` fails on the
concrete terms containing `ringCatSheaf` (instance-transparency mismatch). -/
theorem AlgebraicGeometry.Scheme.Modules.whiskerLeft_conj_zero {X : AlgebraicGeometry.Scheme.{u}}
    {P P' Q R S W : X.Modules} (τ : P ≅ Q ⊗ R) (τ' : P' ≅ Q ⊗ S)
    (u : R ⟶ W) (v : W ⟶ S) (h : u ≫ v = 0) :
    (τ.hom ≫ (Q ◁ u)) ≫ (Q ◁ v) ≫ τ'.inv = 0 := by
  rw [Category.assoc, ← Category.assoc (Q ◁ u), ← MonoidalCategory.whiskerLeft_comp, h,
    AlgebraicGeometry.Scheme.Modules.whiskerLeft_zeroMorphism, zero_comp, comp_zero]

/-- Variable-level bridge: `(τ.hom ≫ (Q ◁ u)) ≫ (Q ◁ v) ≫ τ.inv = 𝟙` when `u ≫ v = 𝟙`
(`whiskerLeft_comp` + `whiskerLeft_id` + `Iso.hom_inv_id`). -/
theorem AlgebraicGeometry.Scheme.Modules.whiskerLeft_conj_id {X : AlgebraicGeometry.Scheme.{u}}
    {P Q R W : X.Modules} (τ : P ≅ Q ⊗ R) (u : R ⟶ W) (v : W ⟶ R) (h : u ≫ v = 𝟙 R) :
    (τ.hom ≫ (Q ◁ u)) ≫ (Q ◁ v) ≫ τ.inv = 𝟙 P := by
  rw [Category.assoc, ← Category.assoc (Q ◁ u), ← MonoidalCategory.whiskerLeft_comp, h,
    MonoidalCategory.whiskerLeft_id, Category.id_comp, Iso.hom_inv_id]

/-- **`monomialHom q ≫ coefficientHom q' = 0` for `q' ≠ q`** (steps 2–3 of the proof of `coefficient_monomial`):
`σ ≫ σIso.inv = 𝟙`, then `ι_q ≫ π_{q'} = 0` (`Sigma.ι_desc`, `dif_neg`), then `M ◁ 0 = 0`. -/
theorem AlgebraicGeometry.Scheme.totalSpace.monomialHom_coefficientHom_of_ne {X : AlgebraicGeometry.Scheme.{u}}
    (L M : X.Modules) [L.IsLineBundle] {q q' : ℕ} (h : q' ≠ q) :
    AlgebraicGeometry.Scheme.totalSpace.monomialHom L M q ≫
      AlgebraicGeometry.Scheme.totalSpace.coefficientHom L M q' = 0 := by
  unfold AlgebraicGeometry.Scheme.totalSpace.monomialHom AlgebraicGeometry.Scheme.totalSpace.coefficientHom
  set S := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L) with hSdef
  have h0 : S.totalIncl q ≫ S.totalProj q' = 0 :=
    (Sigma.ι_desc (fun m => if h : m = q' then CategoryTheory.eqToHom (congrArg S.part h) else 0) q).trans
      (dif_neg (Ne.symm h))
  have hσ : AlgebraicGeometry.Scheme.relativeSpec.structureHom S.total ≫
      (AlgebraicGeometry.Scheme.relativeSpec.structureIso S.total).inv = 𝟙 _ :=
    (AlgebraicGeometry.Scheme.relativeSpec.structureIso S.total).hom_inv_id
  have hmid : (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L q ≫ S.totalIncl q ≫
      AlgebraicGeometry.Scheme.relativeSpec.structureHom S.total) ≫
      ((AlgebraicGeometry.Scheme.relativeSpec.structureIso S.total).inv ≫ S.totalProj q' ≫
        AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower L q') = 0 := by
    simp only [Category.assoc]
    rw [reassoc_of% hσ, reassoc_of% h0, zero_comp, comp_zero]
  exact AlgebraicGeometry.Scheme.Modules.whiskerLeft_conj_zero _ _ _ _ hmid

/-- **`monomialHom q ≫ coefficientHom q = 𝟙`** (steps 2–5 of the proof of `coefficient_monomial`):
`σ ≫ σIso.inv = 𝟙`, `ι_q ≫ π_q = 𝟙` (`totalIncl_totalProj`), `Θ_q ≫ Θ'_q = 𝟙`
(`tensorPowerToSymPart_comp_symPartToTensorPower`), then `τ.hom ≫ (M ◁ 𝟙) ≫ τ.inv = 𝟙`. -/
theorem AlgebraicGeometry.Scheme.totalSpace.monomialHom_coefficientHom {X : AlgebraicGeometry.Scheme.{u}}
    (L M : X.Modules) [L.IsLineBundle] (q : ℕ) :
    AlgebraicGeometry.Scheme.totalSpace.monomialHom L M q ≫
      AlgebraicGeometry.Scheme.totalSpace.coefficientHom L M q = 𝟙 _ := by
  unfold AlgebraicGeometry.Scheme.totalSpace.monomialHom AlgebraicGeometry.Scheme.totalSpace.coefficientHom
  set S := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L) with hSdef
  have hσ : AlgebraicGeometry.Scheme.relativeSpec.structureHom S.total ≫
      (AlgebraicGeometry.Scheme.relativeSpec.structureIso S.total).inv = 𝟙 _ :=
    (AlgebraicGeometry.Scheme.relativeSpec.structureIso S.total).hom_inv_id
  have hmid : (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L q ≫ S.totalIncl q ≫
      AlgebraicGeometry.Scheme.relativeSpec.structureHom S.total) ≫
      ((AlgebraicGeometry.Scheme.relativeSpec.structureIso S.total).inv ≫ S.totalProj q ≫
        AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower L q) = 𝟙 _ := by
    simp only [Category.assoc]
    rw [reassoc_of% hσ, reassoc_of% (AlgebraicGeometry.Scheme.GradedQCAlgebra.totalIncl_totalProj S q)]
    exact AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart_comp_symPartToTensorPower L q
  exact AlgebraicGeometry.Scheme.Modules.whiskerLeft_conj_id _ _ _ hmid

/-- **`pullbackSectionToPushforward ∘ pushforwardSectionToPullback = id`** on global sections (step 1 of the proof
of `coefficient_monomial`): `ρ_{g^*M}` and `projectionFormulaIso` cancel by `Iso.hom_inv_id`
(only the direction `θIso.hom ≫ θIso.inv = 𝟙` is used). -/
theorem AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_comp_pushforwardSectionToPullback
    {T X : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X) (M : X.Modules) [M.IsLineBundle]
    (s : ((M ⊗ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit T.ringCatSheaf)).val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward g M
      (AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback g M s) = s := by
  unfold AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward
    AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback
  have hρ := congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom)
    (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)).hom_inv_id
  have hθ := congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom)
    (AlgebraicGeometry.Scheme.Modules.projectionFormulaIso g M (SheafOfModules.unit T.ringCatSheaf)).hom_inv_id
  have hρ' := congrArg (fun f => f (((AlgebraicGeometry.Scheme.Modules.projectionFormulaHom g M
    (SheafOfModules.unit T.ringCatSheaf)).val.app (Opposite.op ⊤)).hom s)) hρ
  have hθ' := congrArg (fun f => f s) hθ
  exact (congrArg _ hρ').trans hθ'

/- The `q'`-th coefficient of a monomial: `c` itself for `q' = q`, otherwise `0` (consequences of the projection
   formula isomorphism and of `p_*O_Tot ≅ ⊕ S_m`). -/

/-- **The `q`-th ξ-coefficient of `c·ξ^q` is `c`.**

In the paper: the finite expansion `P_ℓ^{(k)} = ρ^*f_ℓ + Σ_{q=1}^k c_{ℓ,q} ξ^q` with
`c_{ℓ,q} ∈ H^0(C̃, ρ^*A ⊗ L^{-q})`; "coefficients" and "monomials" are inverse to each other, which is exactly
the relation fixed by this statement and the next one.

Proof (both statements together, differing only in the last step).

1. *The two section-level maps are inverse and can be cancelled.*
   `pushforwardSectionToPullback g M s = (ρ_{g^*M}).hom.app ⊤ (θ.app ⊤ s)` and
   `pullbackSectionToPushforward g M P = θIso.inv.app ⊤ ((ρ_{g^*M}).inv.app ⊤ P)`, where
   `θ = projectionFormulaHom g M (O_T)` and `θIso = projectionFormulaIso = asIso θ`. Hence
   `pullbackSectionToPushforward ∘ pushforwardSectionToPullback = id` (`Iso.hom_inv_id` on `⊤`-sections, twice;
   only the direction `θIso.inv ∘ θIso.hom = 𝟙` is used). Therefore
   `coefficient L M q' (monomial L M q c) = (coefficientHom L M q').app ⊤ ((monomialHom L M q).app ⊤ c)`, and both
   statements reduce to the equation of module morphisms
   `monomialHom L M q ≫ coefficientHom L M q' = if q' = q then 𝟙 else 0`.
2. *Unfold the two morphisms.* `monomialHom L M q = τ.hom ≫ (M ◁ (Θ_q ≫ ι_q ≫ σ))` and
   `coefficientHom L M q' = (M ◁ (σIso.inv ≫ π_{q'} ≫ Θ'_{q'})) ≫ τ'.inv`, where `τ`, `τ'` are
   `Modules.tensorIsoTensorObj M (moduleTensorPower (dual L) q)` at `q`, `q'`; `σ = relativeSpec.structureHom (Sym(L^∨)).total`
   and `σIso = asIso σ` (an isomorphism, Stacks 01LQ(2)); `ι_q = GradedQCAlgebra.totalIncl q`,
   `π_{q'} = GradedQCAlgebra.totalProj q'`; `Θ_q = totalSpace.tensorPowerToSymPart L q`,
   `Θ'_{q'} = totalSpace.symPartToTensorPower L q'`. By `σ ≫ σIso.inv = 𝟙` the middle cancels:
   `monomialHom ≫ coefficientHom = τ.hom ≫ (M ◁ (Θ_q ≫ ι_q ≫ π_{q'} ≫ Θ'_{q'})) ≫ τ'.inv`.
3. *Orthogonality of the grading.* `totalProj q'` is by definition `Sigma.desc (fun m => if h : m = q' then eqToHom _ else 0)`
   and `totalIncl q` is `Sigma.ι _ q`, so by `Sigma.ι_desc`,
   `ι_q ≫ π_{q'} = if h : q = q' then eqToHom (congrArg _ h) else 0`.
   * `q' ≠ q` (next theorem): this piece is `0`, `M ◁ 0 = 0` (`whiskerLeft_zero`), the whole composite is `0`, and on
     sections `c` goes to `0`.
   * `q' = q` (this theorem): this piece is `𝟙` (`GradedQCAlgebra.totalIncl_totalProj`), leaving
     `τ.hom ≫ (M ◁ (Θ_q ≫ Θ'_q)) ≫ τ.inv`.
4. *`Θ_q ≫ Θ'_q = 𝟙`* (`tensorPowerToSymPart_comp_symPartToTensorPower`): by definition
   `Θ'_q = symPartToMonoidalPow (dual L) q ≫ powIso.hom` and `Θ_q = powIso.inv ≫ symPowπ` (quasi-coherent branch),
   with `powIso = monoidalPowIsoTensorPower (dual L) q`; after `generalize`/`subst` of
   `symGradedAlgebra = symGradedAlgebraOfQC` this is `symPowπ ≫ inv symPowπ = 𝟙`.
5. *Conclusion.* `τ.hom ≫ (M ◁ 𝟙) ≫ τ.inv = τ.hom ≫ τ.inv = 𝟙` (`whiskerLeft_id`, `Iso.hom_inv_id`); taking
   `⊤`-sections gives `coefficient L M q (monomial L M q c) = c`. ∎

Statement check: `coefficient` needs `[M.IsLineBundle]` (the projection formula isomorphism is proved for line
bundles), `monomial` only `[L.IsLineBundle]`; both instances are present here. Edge case `q = 0`: `ι_0 ≫ π_0 = 𝟙` as
usual, and `Θ_0`, `Θ'_0` are isomorphisms of the unit object.

Assembled from `pullbackSectionToPushforward_comp_pushforwardSectionToPullback` (step 1) and
`monomialHom_coefficientHom` / `monomialHom_coefficientHom_of_ne` (steps 2–5). -/
theorem AlgebraicGeometry.Scheme.totalSpace.coefficient_monomial {X : AlgebraicGeometry.Scheme.{u}}
    (L M : X.Modules) [L.IsLineBundle] [M.IsLineBundle] (q : ℕ)
    (c : ((AlgebraicGeometry.Scheme.Modules.coefficientLineModule M L q).val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.totalSpace.coefficient L M q
      (AlgebraicGeometry.Scheme.totalSpace.monomial L M q c) = c := by
  unfold AlgebraicGeometry.Scheme.totalSpace.coefficient AlgebraicGeometry.Scheme.totalSpace.monomial
  refine (congrArg (fun z => ((AlgebraicGeometry.Scheme.totalSpace.coefficientHom L M q).val.app
      (Opposite.op ⊤)).hom z)
    (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_comp_pushforwardSectionToPullback
      (AlgebraicGeometry.Scheme.totalSpace L).hom M _)).trans ?_
  exact congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom c)
    (AlgebraicGeometry.Scheme.totalSpace.monomialHom_coefficientHom L M q)

/-- **The `q'`-th ξ-coefficient of `c·ξ^q` is `0` for `q' ≠ q`.**

Proof: steps 1–3 of the docstring of `coefficient_monomial`; this statement ends at step 3:
`ι_q ≫ π_{q'} = 0` (the `dif_neg` branch of `Sigma.ι_desc`, `q ≠ q'`), `M ◁ 0 = 0` (`whiskerLeft_zero`), the
composite is `0`, and taking `⊤`-sections gives the claim. Step 4 is not needed here. -/
theorem AlgebraicGeometry.Scheme.totalSpace.coefficient_monomial_of_ne {X : AlgebraicGeometry.Scheme.{u}}
    (L M : X.Modules) [L.IsLineBundle] [M.IsLineBundle] {q q' : ℕ} (h : q' ≠ q)
    (c : ((AlgebraicGeometry.Scheme.Modules.coefficientLineModule M L q).val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.totalSpace.coefficient L M q'
      (AlgebraicGeometry.Scheme.totalSpace.monomial L M q c) = 0 := by
  unfold AlgebraicGeometry.Scheme.totalSpace.coefficient AlgebraicGeometry.Scheme.totalSpace.monomial
  refine (congrArg (fun z => ((AlgebraicGeometry.Scheme.totalSpace.coefficientHom L M q').val.app
      (Opposite.op ⊤)).hom z)
    (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_comp_pushforwardSectionToPullback
      (AlgebraicGeometry.Scheme.totalSpace L).hom M _)).trans ?_
  exact congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom c)
    (AlgebraicGeometry.Scheme.totalSpace.monomialHom_coefficientHom_of_ne L M h)

end
