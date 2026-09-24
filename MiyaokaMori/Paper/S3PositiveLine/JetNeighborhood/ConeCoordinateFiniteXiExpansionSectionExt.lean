import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ThickeningSectionsTruncated

/-! # A section on the jet neighbourhood is determined by its `ξ`-coefficients

A global section of `p_κ^*M` on the thickening `C̃_(κ)(L)` is uniquely determined by its `κ + 1` `ξ`-coefficients
(`xiCoefficientThickening`, `q ≤ κ`); we also prove the additivity of `xiCoefficientThickening` with respect to
sums and finite sums.

This is the usable form of the injectivity of the direct-sum decomposition
`π_{L*}O_{C̃_(k)(L)} = ⊕_{q≤k} L^{-q}` used in the expansion (4.1) of
Lemma 4.1 of the paper: we prove directly that "all coefficients agree ⇒ the sections
agree".
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

/-- `xiCoefficientThickening` is additive: for `q ≤ κ` it is the composite on `⊤` of three morphisms of sheaves of
modules (inverse right unitor, inverse projection-formula isomorphism, coefficient chain), each of which is
additive (`map_add`); for `q > κ` both sides are `0`. -/
theorem xiCoefficientThickening_add {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (κ q : ℕ)
    (P Q : (((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
      M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    xiCoefficientThickening L M κ q (P + Q)
      = xiCoefficientThickening L M κ q P + xiCoefficientThickening L M κ q Q := by
  unfold xiCoefficientThickening
  split_ifs with h
  · simp only [AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward]
    let a := ((AlgebraicGeometry.Scheme.Modules.projectionFormulaIso
      (jetNeighborhood.proj L κ) M.toModules
      (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf)).inv.val.app
        (Opposite.op ⊤)).hom
    let b := ((MonoidalCategoryStruct.rightUnitor
      ((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
        M.toModules)).inv.val.app (Opposite.op ⊤)).hom
    let c := ((CategoryTheory.MonoidalCategoryStruct.whiskerLeft M.toModules
        ((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
          CategoryTheory.Limits.biproduct.π
            (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
            ⟨q, Nat.lt_succ_of_le h⟩ ≫
          (truncatedJetAlgebra.pieceIso L q).hom ≫
          (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q).hom) ≫
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules
          (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q)).inv ≫
        (L.coefficientModuleIso M q).hom).val.app (Opposite.op ⊤)).hom
    change c (a (b (P + Q))) = c (a (b P)) + c (a (b Q))
    have hb : b (P + Q) = b P + b Q := b.map_add P Q
    have ha : a (b P + b Q) = a (b P) + a (b Q) := a.map_add _ _
    have hc : c (a (b P) + a (b Q)) = c (a (b P)) + c (a (b Q)) := c.map_add _ _
    rw [hb, ha, hc]
  · simp

/-- `xiCoefficientThickening` is additive on finite sums (`xiCoefficientThickening_add` packaged as an `AddMonoidHom`,
then `map_sum`). -/
theorem xiCoefficientThickening_sum {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (κ q : ℕ)
    {ι : Type} (s : Finset ι)
    (P : ι → (((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
      M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    xiCoefficientThickening L M κ q (∑ i ∈ s, P i)
      = ∑ i ∈ s, xiCoefficientThickening L M κ q (P i) :=
  map_sum (AddMonoidHom.mk' (xiCoefficientThickening L M κ q)
    (xiCoefficientThickening_add L M κ q)) P s

/-- A composite of morphisms acts on global sections as the composite of the maps (`rfl`; gives `rw`/`simp` a
syntactic shape). -/
private theorem sections_comp_apply {X : AlgebraicGeometry.Scheme.{u}} {A B D : X.Modules}
    (f : A ⟶ B) (g : B ⟶ D) (x : (A.val.obj (Opposite.op ⊤) : Type u)) :
    ((f ≫ g).val.app (Opposite.op ⊤)).hom x
      = (g.val.app (Opposite.op ⊤)).hom ((f.val.app (Opposite.op ⊤)).hom x) := rfl

/-- An isomorphism of sheaves of modules is injective on global sections (use `e.inv` and `hom_inv_id`). -/
private theorem iso_sections_injective {X : AlgebraicGeometry.Scheme.{u}} {A B : X.Modules}
    (e : A ≅ B) {x y : (A.val.obj (Opposite.op ⊤) : Type u)}
    (h : (e.hom.val.app (Opposite.op ⊤)).hom x = (e.hom.val.app (Opposite.op ⊤)).hom y) :
    x = y := by
  have key : ∀ z : (A.val.obj (Opposite.op ⊤) : Type u),
      (e.inv.val.app (Opposite.op ⊤)).hom ((e.hom.val.app (Opposite.op ⊤)).hom z) = z := by
    intro z
    rw [← ModuleCat.comp_apply]
    change ((e.hom ≫ e.inv).val.app (Opposite.op ⊤)).hom z = z
    have hh := congrArg (fun f => (f.val.app (Opposite.op ⊤)).hom z) e.hom_inv_id
    rw [hh]
    exact ModuleCat.id_apply _ _
  rw [← key x, ← key y, h]

/-- **A global section of `M ⊗ ⨁ N` is determined by its components `M ◁ π_i`**.

Proof: `M ⊗ -` preserves colimits (`tensorLeft_preservesColimitsOfSize`), hence binary biproducts and zero
(Mathlib `preservesBinaryBiproducts_of_preservesBinaryCoproducts`, `preservesZeroMorphisms_of_preserves_initial_object`),
so it is additive (`Functor.additive_of_preservesBinaryBiproducts`). Applying `tensorLeft M` to
`biproduct.total : ∑ i, π_i ≫ ι_i = 𝟙` (`Functor.map_sum`, `whiskerLeft_comp`, `whiskerLeft_id`) gives
`𝟙 = ∑ i, (M ◁ π_i) ≫ (M ◁ ι_i)`; "take the action on a section `x` over `⊤`" is an additive group homomorphism
(addition in `SheafOfModules` is defined pointwise through `.val`), so `x = ∑ i, (M ◁ ι_i)((M ◁ π_i) x)` and the two
sides agree termwise. For an empty index set the biproduct is the zero object and both sides are `0`. -/
theorem AlgebraicGeometry.Scheme.Modules.whiskerLeft_biproduct_sections_ext
    {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) {ι : Type} [Fintype ι] (N : ι → X.Modules)
    {z w : ((M ⊗ ⨁ N).val.obj (Opposite.op ⊤) : Type u)}
    (h : ∀ i, ((M ◁ biproduct.π N i).val.app (Opposite.op ⊤)).hom z
      = ((M ◁ biproduct.π N i).val.app (Opposite.op ⊤)).hom w) : z = w := by
  have : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft M) :=
    preservesColimitsOfSize_shrink _
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (MonoidalCategory.tensorLeft M)
  have : (MonoidalCategory.tensorLeft M).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have htot : (𝟙 (M ⊗ ⨁ N) : M ⊗ ⨁ N ⟶ M ⊗ ⨁ N)
      = ∑ i, (M ◁ biproduct.π N i) ≫ (M ◁ biproduct.ι N i) := by
    have h1 := congrArg (fun f => (MonoidalCategory.tensorLeft M).map f) (biproduct.total (f := N))
    simp only [Functor.map_sum] at h1
    have h2 : M ◁ (𝟙 (⨁ N)) = ∑ i, M ◁ (biproduct.π N i ≫ biproduct.ι N i) := h1.symm
    simp only [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_id] at h2
    exact h2
  have key : ∀ x : ((M ⊗ ⨁ N).val.obj (Opposite.op ⊤) : Type u),
      x = ∑ i, ((M ◁ biproduct.ι N i).val.app (Opposite.op ⊤)).hom
        (((M ◁ biproduct.π N i).val.app (Opposite.op ⊤)).hom x) := by
    intro x
    let ex : (M ⊗ ⨁ N ⟶ M ⊗ ⨁ N) →+ ((M ⊗ ⨁ N).val.obj (Opposite.op ⊤) : Type u) :=
      { toFun := fun f => (f.val.app (Opposite.op ⊤)).hom x
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have h1 := congrArg ex htot
    rw [map_sum] at h1
    exact h1
  rw [key z, key w]
  exact Finset.sum_congr rfl (fun i _ => congrArg _ (h i))

/-- **The projection-formula section maps are mutually inverse**:
`pushforwardSectionToPullback ∘ pullbackSectionToPushforward = id` (using only `projectionFormulaIso.inv_hom_id`
and the `inv_hom_id` of the right unitor; `projectionFormulaIso = asIso projectionFormulaHom`, so `.hom` is
`projectionFormulaHom`). -/
theorem AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback_pullbackSectionToPushforward_sectionExt
    {T X : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X) (M : X.Modules) [M.IsLineBundle]
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback g M
      (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward g M P) = P := by
  unfold AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward
  have h1 : ∀ y, ((AlgebraicGeometry.Scheme.Modules.projectionFormulaHom g M
      (SheafOfModules.unit T.ringCatSheaf)).val.app (Opposite.op ⊤)).hom
        (((AlgebraicGeometry.Scheme.Modules.projectionFormulaIso g M
          (SheafOfModules.unit T.ringCatSheaf)).inv.val.app (Opposite.op ⊤)).hom y) = y := by
    intro y
    rw [← ModuleCat.comp_apply]
    change (((AlgebraicGeometry.Scheme.Modules.projectionFormulaIso g M
      (SheafOfModules.unit T.ringCatSheaf)).inv ≫
      (AlgebraicGeometry.Scheme.Modules.projectionFormulaIso g M
        (SheafOfModules.unit T.ringCatSheaf)).hom).val.app (Opposite.op ⊤)).hom y = y
    have hh := congrArg (fun f => (f.val.app (Opposite.op ⊤)).hom y)
      (AlgebraicGeometry.Scheme.Modules.projectionFormulaIso g M
        (SheafOfModules.unit T.ringCatSheaf)).inv_hom_id
    rw [hh]
    exact ModuleCat.id_apply _ _
  have h2 : ∀ y, ((ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)).hom.val.app
      (Opposite.op ⊤)).hom (((ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)).inv.val.app
        (Opposite.op ⊤)).hom y) = y := by
    intro y
    rw [← ModuleCat.comp_apply]
    change (((ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)).inv ≫
      (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)).hom).val.app (Opposite.op ⊤)).hom y = y
    have hh := congrArg (fun f => (f.val.app (Opposite.op ⊤)).hom y)
      (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)).inv_hom_id
    rw [hh]
    exact ModuleCat.id_apply _ _
  rw [h1, h2]

/-- Variable-level splitting of the chain (avoids `rw` mismatches from different spellings of the concrete objects:
`(truncatedJetAlgebra L κ).carrier` and `⨁ piece` agree only after unfolding non-reducible definitions):
`(M ◁ (s ≫ π ≫ a ≫ b)) ≫ t` on sections is `t' ∘ (M ◁ π) ∘ (M ◁ s)` with `t' = (M ◁ (a ≫ b)) ≫ t`. -/
private theorem whiskerLeft_chain_split {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)
    {A B D E F G : X.Modules} (s : A ⟶ B) (π : B ⟶ D) (a : D ⟶ E) (b : E ⟶ F) (t : M ⊗ F ⟶ G)
    (x : ((M ⊗ A).val.obj (Opposite.op ⊤) : Type u)) :
    (((M ◁ (s ≫ π ≫ a ≫ b)) ≫ t).val.app (Opposite.op ⊤)).hom x
      = (((M ◁ (a ≫ b)) ≫ t).val.app (Opposite.op ⊤)).hom
          (((M ◁ π).val.app (Opposite.op ⊤)).hom (((M ◁ s).val.app (Opposite.op ⊤)).hom x)) := by
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc, sections_comp_apply]

/-- **A section on the thickening is determined by its `ξ`-coefficients**: if `P, Q ∈ Γ(C̃_(κ)(L), p_κ^*M)` have the
same coefficients `xiCoefficientThickening L M κ q` for all `q ≤ κ`, then `P = Q`.

Source: §3 of the paper (`C̃_(κ)(L) = Spec ⊕_{q≤κ} L^{-q}`) and Lemma 4.1.

Proof:
1. `pullbackSectionToPushforward p_κ M : Γ(C̃_(κ), p_κ^*M) → Γ(C̃, M ⊗ p_{κ*}O)` is injective, because
   `pushforwardSectionToPullback` is a left inverse (`pushforwardSectionToPullback_pullbackSectionToPushforward_sectionExt`).
2. `M ◁ structureIso⁻¹ : M ⊗ p_{κ*}O ≅ M ⊗ ⨁_{q≤κ} piece_q` is an isomorphism, hence injective on sections.
3. A section of `M ⊗ ⨁ piece` is determined by its components `M ◁ π_q` (`whiskerLeft_biproduct_sections_ext`).
4. For each `q ≤ κ`, `xiCoefficientThickening L M κ q` is by definition
   `(M ◁ (σ⁻¹ ≫ π_q ≫ pieceIso_q ≫ powIso_q)) ≫ τ_q⁻¹ ≫ coef_q` applied on `⊤` to `pullbackSectionToPushforward P`;
   split it with `whiskerLeft_comp` into `(M ◁ σ⁻¹)`, `(M ◁ π_q)` and the final isomorphism
   `e_q = (M ◁ (pieceIso_q ≫ powIso_q)) ≫ τ_q⁻¹ ≫ coef_q`; equal coefficients imply (by injectivity of `e_q`) equal
   `q`-th components.
Edge case: for `κ = 0` there is a single coefficient `q = 0` and the biproduct has one term; the argument is
unchanged. -/
theorem jetNeighborhood_section_ext {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (κ : ℕ)
    (P Q : (((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
      M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (h : ∀ q : ℕ, q ≤ κ →
      xiCoefficientThickening L M κ q P = xiCoefficientThickening L M κ q Q) :
    P = Q := by
  -- Step 1: reduce to equality of the images in Γ(C̃, M ⊗ p_*O)
  suffices hPQ : AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward
      (jetNeighborhood.proj L κ) M.toModules P
      = AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward
        (jetNeighborhood.proj L κ) M.toModules Q by
    rw [← AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback_pullbackSectionToPushforward_sectionExt
      (jetNeighborhood.proj L κ) M.toModules P, hPQ,
      AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback_pullbackSectionToPushforward_sectionExt]
  -- Step 2: remove the isomorphism M ◁ structureIso⁻¹ and reduce to sections of M ⊗ ⨁ piece
  apply iso_sections_injective (MonoidalCategory.whiskerLeftIso M.toModules
    (AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).symm)
  -- Step 3: compare componentwise
  apply AlgebraicGeometry.Scheme.Modules.whiskerLeft_biproduct_sections_ext M.toModules
    (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
  intro i
  have hle : (i : ℕ) ≤ κ := Nat.le_of_lt_succ i.2
  have hi := h i hle
  unfold xiCoefficientThickening at hi
  rw [dif_pos hle, dif_pos hle] at hi
  have hs₁ := whiskerLeft_chain_split M.toModules
    (AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv
    (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
      ⟨(i : ℕ), Nat.lt_succ_of_le hle⟩)
    (truncatedJetAlgebra.pieceIso L i).hom
    (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules) i).hom
    ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules
      (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) i)).inv ≫
      (L.coefficientModuleIso M i).hom)
    (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward (jetNeighborhood.proj L κ)
      M.toModules P)
  have hs₂ := whiskerLeft_chain_split M.toModules
    (AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv
    (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
      ⟨(i : ℕ), Nat.lt_succ_of_le hle⟩)
    (truncatedJetAlgebra.pieceIso L i).hom
    (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules) i).hom
    ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules
      (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) i)).inv ≫
      (L.coefficientModuleIso M i).hom)
    (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward (jetNeighborhood.proj L κ)
      M.toModules Q)
  exact iso_sections_injective
    (MonoidalCategory.whiskerLeftIso M.toModules
        (truncatedJetAlgebra.pieceIso L i ≪≫
          AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules) i) ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules
        (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) i)).symm ≪≫
      L.coefficientModuleIso M i) (hs₁.symm.trans (hi.trans hs₂))

end
