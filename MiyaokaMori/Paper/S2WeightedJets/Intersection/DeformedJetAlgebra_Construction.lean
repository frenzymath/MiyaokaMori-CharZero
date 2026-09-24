import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOver
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundle
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.RestrictToLambda
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.PushforwardQcAlgebraMap
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.TruncatedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ic
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebra_IrrelevantPow
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackUnitMul
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullbackId

/-! # The extended Rees deformation: construction and the fibre at `λ = 1`

Content: `mulCoordPow` (multiplication by `λ^e`) and its monoidal lemmas; `irrelevantPow` quasi-coherence;
the Rees pieces `R_j = Im(⊕_e λ^e·π^*I^{(j-e)}_j → π^*S_j)`, closure under multiplication and unit (`monoLift`),
the graded QC algebra `reesDeformation`, `deformedJetAlgebra := (jetGradedAlgebra …).1.reesDeformation`,
the inclusion morphism `inclHom : R ⟶ π^*S`, and the `λ = 1` fibre `reesDeformation_restrictToLambda_one`.
The two other properties of the deformation (`reesDeformation_isLocallyWeightedPolynomial` and
`deformedJetAlgebra_restrictToLambda_zero`) live in `DeformedJetAlgebraLocallyWeightedPolynomial` and
`DeformedJetAlgebraFiberAtZero`; `DeformedJetAlgebra` assembles `deformedJetAlgebra_spec`.

Source: Lemma 2.3 of the paper ("removing the nonlinear terms"); Stacks 052P.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory


/- `irrelevantPow` (the pieces of the powers of the irrelevant ideal), `irrelevantPow_zero` and the multiplicativity
   `irrelevantPow_mul_condition` live in the upstream module `DeformedJetAlgebra_IrrelevantPow`. -/

/-- Multiplication on a module sheaf `M` by the `e`-th power of the coordinate `λ ∈ Γ(𝔸¹_X, O)`:
`M ≅ O ⊗ M --(λ^e·)⊗1--> O ⊗ M ≅ M` (the multiplication on `O` is `Modules.unitMul`; the monoidal unit is by
definition the structure sheaf). -/

noncomputable def AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow {X : AlgebraicGeometry.Scheme.{u}} (e : ℕ)
    (M : (AlgebraicGeometry.Scheme.affineLineOver X).Modules) : M ⟶ M :=
  (λ_ M).inv ≫
    ((show 𝟙_ (AlgebraicGeometry.Scheme.affineLineOver X).Modules ⟶
          𝟙_ (AlgebraicGeometry.Scheme.affineLineOver X).Modules from
        AlgebraicGeometry.Scheme.Modules.unitMul
          ((AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1)) :
            Γ(AlgebraicGeometry.Scheme.affineLineOver X, ⊤)) ^ e)) ▷ M) ≫
    (λ_ M).hom

/- The data of `reesDeformation`: the `j`-th piece is the image `Im(g_j)`, and multiplication and unit are those of
   `π^*S` restricted to the images via `Abelian.monoLift`. The intermediate data and each proof obligation are stated
   separately below; the definition only refers to them. -/

/-- `g_j : ⊕_{e=0}^{j} π^*I^{(j-e)}_j --Σ λ^e·π^*(incl)--> π^*S_j`. -/

noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (j : ℕ) :
    CategoryTheory.Limits.biproduct
        (fun e : Fin (j + 1) =>
          (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).obj (S.irrelevantPow (j - e.1) j).1) ⟶
      (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part j :=
  CategoryTheory.Limits.biproduct.desc fun e =>
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).map (S.irrelevantPow (j - e.1) j).2 ≫
      AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e.1 ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part j)

/-- The `j`-th piece `R_j := Im(g_j) ⊆ π^*S_j`. -/

noncomputable abbrev AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (j : ℕ) :
    (AlgebraicGeometry.Scheme.affineLineOver X).Modules :=
  CategoryTheory.Limits.image (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen S j)

noncomputable abbrev AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (j : ℕ) :
    AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S j ⟶ (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part j :=
  CategoryTheory.Limits.image.ι (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen S j)

/-- Multiplication by `λ^0 = 1` is the identity (`unitMul_one`). -/
theorem AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow_zero {X : AlgebraicGeometry.Scheme.{u}}
    (M : (AlgebraicGeometry.Scheme.affineLineOver X).Modules) :
    AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow 0 M = CategoryTheory.CategoryStruct.id M := by
  have h : ∀ f : 𝟙_ (AlgebraicGeometry.Scheme.affineLineOver X).Modules ⟶
      𝟙_ (AlgebraicGeometry.Scheme.affineLineOver X).Modules,
      f = CategoryTheory.CategoryStruct.id _ →
        (λ_ M).inv ≫ (f ▷ M) ≫ (λ_ M).hom = CategoryTheory.CategoryStruct.id M := by
    rintro f rfl
    rw [CategoryTheory.MonoidalCategory.id_whiskerRight, Category.id_comp, Iso.inv_hom_id]
  apply h
  dsimp only
  rw [pow_zero]
  exact AlgebraicGeometry.Scheme.Modules.unitMul_one

/-- The value of `unitHomEquiv (unitMul a)` on `U` is the restriction of `a` (definition of `unitMul` and
`Equiv.apply_symm_apply`). -/
theorem AlgebraicGeometry.Scheme.Modules.unitHomEquiv_unitMul_val {X : AlgebraicGeometry.Scheme.{u}} (a : Γ(X, ⊤))
    (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    (SheafOfModules.unitHomEquiv _ (AlgebraicGeometry.Scheme.Modules.unitMul a)).val U =
      (X.presheaf.map (CategoryTheory.homOfLE (le_top : U.unop ≤ ⊤)).op).hom a := by
  unfold AlgebraicGeometry.Scheme.Modules.unitMul
  rw [Equiv.apply_symm_apply]
  rfl

/-- Composition of multiplications by global functions: `unitMul a ≫ unitMul b = unitMul (a * b)` (on sections,
`x ↦ (x·a)·b = x·(ab)`). Proof: compare the families of sections through the injective `unitHomEquiv`: on `U` the
left side is `(unitMul b)_U (res a) = res a • (unitMul b)_U 1 = res a • res b` (`O`-linearity and
`unitHomEquiv_unitMul_val`), the right side is `res (a * b)` (`map_mul`). -/
theorem AlgebraicGeometry.Scheme.Modules.unitMul_mul {X : AlgebraicGeometry.Scheme.{u}} (a b : Γ(X, ⊤)) :
    AlgebraicGeometry.Scheme.Modules.unitMul a ≫ AlgebraicGeometry.Scheme.Modules.unitMul b =
      AlgebraicGeometry.Scheme.Modules.unitMul (a * b) := by
  apply (SheafOfModules.unitHomEquiv _).injective
  rw [SheafOfModules.unitHomEquiv_comp_apply]
  ext U
  show ((AlgebraicGeometry.Scheme.Modules.unitMul b).val.app U).hom
      ((SheafOfModules.unitHomEquiv _ (AlgebraicGeometry.Scheme.Modules.unitMul a)).val U) = _
  rw [AlgebraicGeometry.Scheme.Modules.unitHomEquiv_unitMul_val,
    AlgebraicGeometry.Scheme.Modules.unitHomEquiv_unitMul_val]
  have hb := AlgebraicGeometry.Scheme.Modules.unitHomEquiv_unitMul_val b U
  rw [SheafOfModules.unitHomEquiv_apply_coe] at hb
  let ra : X.ringCatSheaf.obj.obj U := (X.presheaf.map (CategoryTheory.homOfLE (le_top : U.unop ≤ ⊤)).op).hom a
  let rb : X.ringCatSheaf.obj.obj U := (X.presheaf.map (CategoryTheory.homOfLE (le_top : U.unop ≤ ⊤)).op).hom b
  have hb' : ((AlgebraicGeometry.Scheme.Modules.unitMul b).val.app U).hom (1 : X.ringCatSheaf.obj.obj U) = rb := hb
  have h1 : ((AlgebraicGeometry.Scheme.Modules.unitMul b).val.app U).hom
      (ra • (1 : X.ringCatSheaf.obj.obj U)) =
      ra • ((AlgebraicGeometry.Scheme.Modules.unitMul b).val.app U).hom (1 : X.ringCatSheaf.obj.obj U) :=
    _root_.map_smul _ _ _
  have h2 : ra • (1 : X.ringCatSheaf.obj.obj U) = ra := mul_one ra
  change ((AlgebraicGeometry.Scheme.Modules.unitMul b).val.app U).hom ra = _
  rw [← h2, h1, hb']
  show ra * rb = (X.presheaf.map (CategoryTheory.homOfLE (le_top : U.unop ≤ ⊤)).op).hom (a * b)
  rw [map_mul]
  rfl

/-- Multiplication by `λ^e` commutes with every morphism (morphisms of module sheaves are `O`-linear; pure monoidal
category theory: naturality of the left unitor and `whisker_exchange`). -/
theorem AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow_naturality {X : AlgebraicGeometry.Scheme.{u}} (e : ℕ)
    {M N : (AlgebraicGeometry.Scheme.affineLineOver X).Modules} (φ : M ⟶ N) :
    AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e M ≫ φ = φ ≫ AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e N := by
  unfold AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow
  rw [Category.assoc, Category.assoc, ← CategoryTheory.MonoidalCategory.leftUnitor_naturality,
    ← CategoryTheory.MonoidalCategory.whisker_exchange_assoc,
    ← CategoryTheory.MonoidalCategory.leftUnitor_inv_naturality_assoc]

/-- `mulCoordPow e M ▷ N = mulCoordPow e (M ⊗ N)` (compatibility of the left unitor with the associator,
`leftUnitor_tensor`). -/
theorem AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow_whiskerRight {X : AlgebraicGeometry.Scheme.{u}} (e : ℕ)
    (M N : (AlgebraicGeometry.Scheme.affineLineOver X).Modules) :
    AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e M ▷ N = AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e (M ⊗ N) := by
  have h : ∀ f : 𝟙_ (AlgebraicGeometry.Scheme.affineLineOver X).Modules ⟶
      𝟙_ (AlgebraicGeometry.Scheme.affineLineOver X).Modules,
      ((λ_ M).inv ≫ (f ▷ M) ≫ (λ_ M).hom) ▷ N =
        (λ_ (M ⊗ N)).inv ≫ (f ▷ (M ⊗ N)) ≫ (λ_ (M ⊗ N)).hom := by
    intro f
    rw [CategoryTheory.MonoidalCategory.comp_whiskerRight, CategoryTheory.MonoidalCategory.comp_whiskerRight,
      CategoryTheory.MonoidalCategory.leftUnitor_tensor_inv, CategoryTheory.MonoidalCategory.leftUnitor_tensor_hom,
      Category.assoc, CategoryTheory.MonoidalCategory.associator_inv_naturality_left_assoc,
      Iso.hom_inv_id_assoc]
  exact h _

/-- `M ◁ mulCoordPow e N = mulCoordPow e (M ⊗ N)` (reduce to `mulCoordPow_whiskerRight` via the braiding `β` and
naturality). -/
theorem AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow_whiskerLeft {X : AlgebraicGeometry.Scheme.{u}} (e : ℕ)
    (M N : (AlgebraicGeometry.Scheme.affineLineOver X).Modules) :
    M ◁ AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e N = AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e (M ⊗ N) := by
  have h := CategoryTheory.BraidedCategory.braiding_naturality_right M (AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e N)
  rw [AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow_whiskerRight, ← AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow_naturality] at h
  exact (cancel_mono (β_ M N).hom).1 h

/-- `λ^{e+e'} = λ^e · λ^{e'}`: `pow_add` and `unitMul_mul`. -/
theorem AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow_add {X : AlgebraicGeometry.Scheme.{u}} (e e' : ℕ)
    (M : (AlgebraicGeometry.Scheme.affineLineOver X).Modules) :
    AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow (e + e') M = AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e M ≫ AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e' M := by
  have h : ∀ f g : 𝟙_ (AlgebraicGeometry.Scheme.affineLineOver X).Modules ⟶
      𝟙_ (AlgebraicGeometry.Scheme.affineLineOver X).Modules,
      (λ_ M).inv ≫ (f ▷ M) ≫ (λ_ M).hom ≫ (λ_ M).inv ≫ (g ▷ M) ≫ (λ_ M).hom =
        (λ_ M).inv ≫ ((f ≫ g) ▷ M) ≫ (λ_ M).hom := by
    intro f g
    rw [Iso.hom_inv_id_assoc, CategoryTheory.MonoidalCategory.comp_whiskerRight, Category.assoc]
  unfold AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow
  rw [Category.assoc, Category.assoc, h]
  dsimp only
  rw [pow_add]
  exact congrArg (fun q => (λ_ M).inv ≫ (q ▷ M) ≫ (λ_ M).hom)
    (AlgebraicGeometry.Scheme.Modules.unitMul_mul _ _).symm

/-- `incl` commutes with reindexing by `eqToHom` (`incl` is a natural family over `ℕ`). -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.eqToHom_comp_incl {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) {a b : ℕ} (h : a = b) :
    eqToHom (congrArg (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S) h) ≫ AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S b =
      AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S a ≫
        eqToHom (congrArg (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part h) := by
  subst h
  simp

/-- The image of a morphism of quasi-coherent sheaves is quasi-coherent: `Abelian.image f = ker(coker.π f)`, isomorphic
to `Limits.image f` (Mathlib `Abelian.imageIsoImage`); kernels and cokernels of quasi-coherent sheaves are
quasi-coherent by Stacks 01IC (`isQuasicoherent_kernel`). -/
theorem AlgebraicGeometry.Scheme.Modules.isQuasicoherent_image {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (CategoryTheory.Limits.image f).IsQuasicoherent :=
  haveI := (AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel f).2
  have h := ObjectProperty.prop_of_iso (P := SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (CategoryTheory.Abelian.imageIsoImage f)
    (AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel (CategoryTheory.Limits.cokernel.π f)).1
  h

/-- `S_+^{(p)}_j` is quasi-coherent: by induction on `p`; the piece for `p + 1` is the image of a tensor product of
finite biproducts, so use `isQuasicoherent_tensorObj`, `isQuasicoherent_biproduct` (Stacks 01BF) and
`isQuasicoherent_image`. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.irrelevantPow_isQuasicoherent {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (p j : ℕ) : (S.irrelevantPow p j).1.IsQuasicoherent := by
  induction p generalizing j with
  | zero => exact S.quasicoherent j
  | succ p ih =>
    have hsum : ∀ a : Fin j,
        (S.part (a.1 + 1) ⊗ (S.irrelevantPow p (j - (a.1 + 1))).1).IsQuasicoherent := fun a =>
      have := ih (j - (a.1 + 1))
      have := S.quasicoherent (a.1 + 1)
      AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorObj _ _
    have := AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biproduct _ hsum
    have := S.quasicoherent j
    exact AlgebraicGeometry.Scheme.Modules.isQuasicoherent_image _

/-- The image of a morphism of quasi-coherent sheaves is quasi-coherent (Stacks 01LA): `R_j = Im(g_j)`, whose source is
a finite biproduct (`isQuasicoherent_biproduct`) of pullbacks (`isQuasicoherent_pullback`) and whose target is
`π^*S_j`. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part_isQuasicoherent {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (j : ℕ) :
    (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S j).IsQuasicoherent := by
  have hsum : ∀ e : Fin (j + 1),
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).obj
        (S.irrelevantPow (j - e.1) j).1).IsQuasicoherent := fun e =>
    have := AlgebraicGeometry.Scheme.GradedQCAlgebra.irrelevantPow_isQuasicoherent S (j - e.1) j
    inferInstance
  have := AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biproduct _ hsum
  have := (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).quasicoherent j
  exact AlgebraicGeometry.Scheme.Modules.isQuasicoherent_image (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen S j)

/-- `μ_e ⊗ₘ μ_{e'} = μ_{e+e'}` on the tensor product (`mulCoordPow_whiskerRight/Left/add`). -/
theorem AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow_tensorHom {X : AlgebraicGeometry.Scheme.{u}} (e e' : ℕ)
    (M N : (AlgebraicGeometry.Scheme.affineLineOver X).Modules) :
    (AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e M ⊗ₘ AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e' N) =
      AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow (e + e') (M ⊗ N) := by
  rw [CategoryTheory.MonoidalCategory.tensorHom_def, AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow_whiskerRight,
    AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow_whiskerLeft, AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow_add]

/-- A morphism out of `(⨁ F) ⊗ (⨁ G)` is determined by its composites with `biproduct.ι F j ⊗ₘ biproduct.ι G k`
(`biproduct_whiskerRight_hom_ext` then `biproduct_whiskerLeft_hom_ext`, DeformedJetAlgebra_WhiskerAdd). -/
theorem AlgebraicGeometry.Scheme.Modules.biproduct_tensor_biproduct_hom_ext {X : AlgebraicGeometry.Scheme.{u}}
    {J K : Type} [Fintype J] [Fintype K] (F : J → X.Modules) (G : K → X.Modules) {Z : X.Modules}
    (g h : CategoryTheory.Limits.biproduct F ⊗ CategoryTheory.Limits.biproduct G ⟶ Z)
    (w : ∀ j k, (CategoryTheory.Limits.biproduct.ι F j ⊗ₘ CategoryTheory.Limits.biproduct.ι G k) ≫ g =
      (CategoryTheory.Limits.biproduct.ι F j ⊗ₘ CategoryTheory.Limits.biproduct.ι G k) ≫ h) : g = h := by
  apply AlgebraicGeometry.Scheme.Modules.biproduct_whiskerRight_hom_ext F (CategoryTheory.Limits.biproduct G)
  intro j
  apply AlgebraicGeometry.Scheme.Modules.biproduct_whiskerLeft_hom_ext (F j) G
  intro k
  rw [← Category.assoc, ← Category.assoc, ← CategoryTheory.MonoidalCategory.tensorHom_def', w j k]

/-- `π^*f` regarded as a morphism into the piece `(S.pullback π).part n` (which is `π^*S_n` by definition).
Reducible alias: it only fixes the *type* so that composites with `mulCoordPow e ((S.pullback π).part n)` are
syntactically well-typed and `rw` can match them. -/
abbrev AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.pullMap {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) {A : X.Modules} {n : ℕ} (f : A ⟶ S.part n) :
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).obj A ⟶
      (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part n :=
  (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).map f

/-- `f : A ⟶ π^*S_n` lands in `R_n = Im(gen S n)`: its composite with the cokernel projection of `incl S n` vanishes. -/
def AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.LandsInPart {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) {A : (AlgebraicGeometry.Scheme.affineLineOver X).Modules} {n : ℕ}
    (f : A ⟶ (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part n) : Prop :=
  f ≫ CategoryTheory.Limits.cokernel.π (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S n) = 0

theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.landsInPart_comp {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) {A B : (AlgebraicGeometry.Scheme.affineLineOver X).Modules} {n : ℕ}
    {f : B ⟶ (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part n} (g : A ⟶ B)
    (h : AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.LandsInPart S f) :
    AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.LandsInPart S (g ≫ f) := by
  unfold AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.LandsInPart at *
  rw [Category.assoc, h, comp_zero]

theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.landsInPart_comp_comp {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) {A B C : (AlgebraicGeometry.Scheme.affineLineOver X).Modules} {n : ℕ}
    {f : C ⟶ (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part n} (g : A ⟶ B) (h : B ⟶ C)
    (hf : AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.LandsInPart S (h ≫ f)) :
    AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.LandsInPart S ((g ≫ h) ≫ f) := by
  unfold AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.LandsInPart at *
  rw [Category.assoc] at hf
  rw [Category.assoc, Category.assoc, hf, comp_zero]

/-- `gen S n` itself lands in `R_n` (`image.fac` + `cokernel.condition`). -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen_comp_cokernel_π {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (n : ℕ) :
    AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen S n ≫
      CategoryTheory.Limits.cokernel.π (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S n) = 0 := by
  calc AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen S n ≫
        CategoryTheory.Limits.cokernel.π (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S n) =
      (CategoryTheory.Limits.factorThruImage (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen S n) ≫
        AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S n) ≫
        CategoryTheory.Limits.cokernel.π (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S n) := by
          rw [CategoryTheory.Limits.image.fac]
    _ = 0 := by rw [Category.assoc, CategoryTheory.Limits.cokernel.condition, comp_zero]

/-- The `e`-th component of `gen S n` is `λ^e · π^*(I^{(n-e)}_n → S_n)` (`biproduct.ι_desc`). -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.ι_gen {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (n : ℕ) (e : Fin (n + 1)) :
    CategoryTheory.Limits.biproduct.ι _ e ≫ AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen S n =
      AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.pullMap S (S.irrelevantPow (n - e.1) n).2 ≫
        AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e.1 ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part n) := by
  unfold AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen
  exact CategoryTheory.Limits.biproduct.ι_desc _ e

/-- Each component `π^*I^{(n-e)}_n --λ^e--> π^*S_n` of `gen S n` lands in `R_n`. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.landsInPart_gen_component {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (n : ℕ) (e : Fin (n + 1)) :
    AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.LandsInPart S
      (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.pullMap S (S.irrelevantPow (n - e.1) n).2 ≫
        AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e.1 ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part n)) := by
  have h : AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.LandsInPart S
      (CategoryTheory.Limits.biproduct.ι _ e ≫ AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen S n) :=
    AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.landsInPart_comp S _
      (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen_comp_cokernel_π S n)
  rw [AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.ι_gen] at h
  exact h

/-- Transport in the first index of `irrelevantPow`. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.landsInPart_transport {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) {n p p' e : ℕ} (h : p' = p)
    (hp : AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.LandsInPart S
      (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.pullMap S (S.irrelevantPow p' n).2 ≫
        AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part n))) :
    AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.LandsInPart S
      (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.pullMap S (S.irrelevantPow p n).2 ≫
        AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part n)) := by
  subst h; exact hp

/-- If `φ : A ⟶ S_n` lands in `I^{(p)}_n` (`p ≤ n`), then `λ^{n-p}·π^*φ` lands in `R_n`. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.landsInPart_of_landsIn {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) {A : X.Modules} {n : ℕ} (φ : A ⟶ S.part n) (p : ℕ) (hp : p ≤ n) (h : S.LandsIn φ p) :
    AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.LandsInPart S
      (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.pullMap S φ ≫
        AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow (n - p) ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part n)) := by
  obtain ⟨ψ, rfl⟩ := (S.landsIn_iff_exists φ p).1 h
  have hc := AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.landsInPart_gen_component S n ⟨n - p, by omega⟩
  have hc' := AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.landsInPart_transport S
    (p := p) (p' := n - (n - p)) (e := n - p) (by omega) hc
  have hmap : AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.pullMap S (ψ ≫ (S.irrelevantPow p n).2) =
      (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).map ψ ≫
        AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.pullMap S (S.irrelevantPow p n).2 :=
    Functor.map_comp _ _ _
  rw [hmap]
  exact AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.landsInPart_comp_comp S _ _ hc'

/-- L1: the two λ-powers move to the right of the multiplication (`tensorHom_comp_tensorHom`, `mulCoordPow_tensorHom`,
`mulCoordPow_naturality`). -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.tensor_mulCoordPow_comp_mul {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) {A B : (AlgebraicGeometry.Scheme.affineLineOver X).Modules} {j k : ℕ}
    (u : A ⟶ (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part j)
    (v : B ⟶ (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part k) (e e' : ℕ) :
    ((u ≫ AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part j)) ⊗ₘ
        (v ≫ AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e' ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part k))) ≫
      (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).mul j k =
    (u ⊗ₘ v) ≫ (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).mul j k ≫
      AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow (e + e') ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part (j + k)) := by
  rw [← CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc,
    AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow_tensorHom,
    AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow_naturality]

/-- L2: multiplication of `π^*S` on pulled-back morphisms (`GradedQCAlgebra.pullback` + `LaxMonoidal.μ_natural`). -/
@[reassoc]
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.tensor_pullMap_comp_mul {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) {A B : X.Modules} {j k : ℕ} (f : A ⟶ S.part j) (g : B ⟶ S.part k) :
    (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.pullMap S f ⊗ₘ AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.pullMap S g) ≫
        (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).mul j k =
      CategoryTheory.Functor.LaxMonoidal.μ (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)) A B ≫
        AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.pullMap S ((f ⊗ₘ g) ≫ S.mul j k) := by
  show ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).map f ⊗ₘ
      (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).map g) ≫
    (CategoryTheory.Functor.LaxMonoidal.μ (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)) (S.part j) (S.part k) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).map (S.mul j k)) =
    CategoryTheory.Functor.LaxMonoidal.μ (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)) A B ≫
      (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).map ((f ⊗ₘ g) ≫ S.mul j k)
  rw [← Category.assoc, CategoryTheory.Functor.LaxMonoidal.μ_natural, Category.assoc, ← Functor.map_comp]

/-- The `(e, e')` component of `(gen S j ⊗ₘ gen S k) ≫ T.mul j k` lands in `R_{j+k}`. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.landsInPart_gen_tensor_gen_component {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (j k : ℕ) (e : Fin (j + 1)) (e' : Fin (k + 1)) :
    AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.LandsInPart S
      (((CategoryTheory.Limits.biproduct.ι _ e ≫ AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen S j) ⊗ₘ
          (CategoryTheory.Limits.biproduct.ι _ e' ≫ AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen S k)) ≫
        (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).mul j k) := by
  rw [AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.ι_gen,
    AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.ι_gen,
    AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.tensor_mulCoordPow_comp_mul,
    AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.tensor_pullMap_comp_mul_assoc]
  have hidx : e.1 + e'.1 = (j + k) - ((j - e.1) + (k - e'.1)) := by have := e.2; have := e'.2; omega
  rw [hidx]
  exact AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.landsInPart_comp S _
    (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.landsInPart_of_landsIn S _ _
      (by have := e.2; have := e'.2; omega) (S.landsIn_tensor_mul _ (S.landsIn_self _ _) (S.landsIn_self _ _)))

/-- The images are closed under multiplication: `λ^e · I^{(j-e)}_j` times `λ^{e'} · I^{(k-e')}_k` lands in
`λ^{e+e'} · I^{(j+k-e-e')}_{j+k}` (multiplicativity `I^{(a)} · I^{(b)} ⊆ I^{(a+b)}` of the powers of the irrelevant
ideal). Source: Stacks 052P.
Proof. Write `P = Modules.pullback toBase`, `T = S.pullback toBase`, `μ_e = mulCoordPow e`,
`ι_p := (S.irrelevantPow p _).2`, `π := cokernel.π (incl S (j+k))`.
1. `incl j = image.ι (gen j)`; `factorThruImage (gen j) ⊗ₘ factorThruImage (gen k)` is an epimorphism
   (`Modules.epi_tensorHom`) and `(fti j ⊗ₘ fti k) ≫ (incl j ⊗ₘ incl k) = gen j ⊗ₘ gen k`
   (`tensorHom_comp_tensorHom` and `image.fac`), so it suffices that `(gen j ⊗ₘ gen k) ≫ T.mul j k ≫ π = 0`.
2. `biproduct_tensor_biproduct_hom_ext` reduces to the components `(e, e')` (`landsInPart_gen_tensor_gen_component`):
   `((P.map ι_{j-e} ≫ μ_e) ⊗ₘ (P.map ι_{k-e'} ≫ μ_{e'})) ≫ T.mul j k`.
3. `tensor_mulCoordPow_comp_mul` (`tensorHom_comp_tensorHom`, `mulCoordPow_tensorHom`, `mulCoordPow_naturality`):
   this equals `(P.map ι_{j-e} ⊗ₘ P.map ι_{k-e'}) ≫ T.mul j k ≫ μ_{e+e'}`.
4. `tensor_pullMap_comp_mul` (`T.mul j k = LaxMonoidal.μ P _ _ ≫ P.map (S.mul j k)` and `LaxMonoidal.μ_natural`):
   this equals `μ P ≫ P.map ((ι_{j-e} ⊗ₘ ι_{k-e'}) ≫ S.mul j k) ≫ μ_{e+e'}`.
5. `landsIn_tensor_mul` (`irrelevantPow_mul_condition`): `(ι_{j-e} ⊗ₘ ι_{k-e'}) ≫ S.mul j k` lands in
   `I^{((j-e)+(k-e'))}_{j+k}`; `landsInPart_of_landsIn` (with `e ≤ j`, `e' ≤ k`, so `e+e' = (j+k)-((j-e)+(k-e'))`)
   sends `λ^{e+e'} · π^*(it)` into `R_{j+k}`, as the `(e+e')`-th component of `gen (j+k)` composed with `monoLift`. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.mul_condition {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (j k : ℕ) :
    ((AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S j ⊗ₘ AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S k) ≫ (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).mul j k) ≫
      CategoryTheory.Limits.cokernel.π (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S (j + k)) = 0 := by
  have he : Epi (CategoryTheory.Limits.factorThruImage (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen S j) ⊗ₘ
      CategoryTheory.Limits.factorThruImage (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen S k)) :=
    AlgebraicGeometry.Scheme.Modules.epi_tensorHom _ _ inferInstance inferInstance
  apply (cancel_epi (CategoryTheory.Limits.factorThruImage (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen S j) ⊗ₘ
      CategoryTheory.Limits.factorThruImage (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen S k))).1
  rw [comp_zero, ← Category.assoc, ← Category.assoc, CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom,
    CategoryTheory.Limits.image.fac, CategoryTheory.Limits.image.fac]
  apply AlgebraicGeometry.Scheme.Modules.biproduct_tensor_biproduct_hom_ext _ _ _ 0
  intro e e'
  rw [comp_zero, ← Category.assoc, ← Category.assoc, CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom]
  exact AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.landsInPart_gen_tensor_gen_component S j k e e'

/-- `1 ∈ R_0`: the `e = 0` component `π^*I^{(0)}_0 = π^*S_0` contains the unit. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.one_condition {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) :
    (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).one ≫ CategoryTheory.Limits.cokernel.π (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S 0) = 0 := by
  let F : Fin (0 + 1) → (AlgebraicGeometry.Scheme.affineLineOver X).Modules := fun e =>
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).obj
      (S.irrelevantPow (0 - e.1) 0).1
  have hfac : CategoryTheory.Limits.biproduct.ι F ⟨0, Nat.zero_lt_one⟩ ≫
      AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen S 0 =
      CategoryTheory.CategoryStruct.id ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part 0) := by
    unfold AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen
    rw [CategoryTheory.Limits.biproduct.ι_desc]
    change (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).map
        (CategoryTheory.CategoryStruct.id (S.part 0)) ≫
      AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow 0 _ = _
    rw [CategoryTheory.Functor.map_id, AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow_zero,
      Category.id_comp]
    rfl
  have hsplit : IsSplitEpi (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen S 0) :=
    IsSplitEpi.mk'
      { section_ := (CategoryTheory.Limits.biproduct.ι F ⟨0, Nat.zero_lt_one⟩ :
          (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part 0 ⟶
            CategoryTheory.Limits.biproduct F)
        id := hfac }
  have : Epi (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S 0) :=
    epi_of_epi_fac (CategoryTheory.Limits.image.fac (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.gen S 0))
  rw [CategoryTheory.Limits.cokernel.π_of_epi, comp_zero]

noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.mulHom {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (j k : ℕ) :
    AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S j ⊗ AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S k ⟶ AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S (j + k) :=
  CategoryTheory.Abelian.monoLift (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S (j + k))
    ((AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S j ⊗ₘ AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S k) ≫ (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).mul j k) (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.mul_condition S j k)

noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.oneHom {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) :
    𝟙_ (AlgebraicGeometry.Scheme.affineLineOver X).Modules ⟶ AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S 0 :=
  CategoryTheory.Abelian.monoLift (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S 0) (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).one (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.one_condition S)

/-- The three algebra axioms: `incl` is a monomorphism, so after composing both sides with `incl` and using
`monoLift_comp` they reduce to the corresponding axioms of `π^*S` (`S.pullback π`). -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.one_mul {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) :
    (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.oneHom S ▷ AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S m) ≫ AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.mulHom S 0 m =
      (λ_ (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S m)).hom ≫ eqToHom (congrArg (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S) (Nat.zero_add m).symm) := by
  apply (cancel_mono
    (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S (0 + m))).1
  unfold AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.oneHom
    AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.mulHom
  simp only [Category.assoc, CategoryTheory.Abelian.monoLift_comp]
  rw [CategoryTheory.MonoidalCategory.whiskerRight_comp_tensorHom_assoc
    (CategoryTheory.Abelian.monoLift
      (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S 0)
      (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).one
      (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.one_condition S))
    (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S 0)
    (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S m)
    ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).mul 0 m)]
  rw [CategoryTheory.Abelian.monoLift_comp]
  calc
    ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).one ⊗ₘ
          AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S m) ≫
        (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).mul 0 m =
      ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).one ▷
          AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S m) ≫
        ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part 0 ◁
          AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S m) ≫
        (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).mul 0 m := by
          exact CategoryTheory.MonoidalCategory.tensorHom_def_assoc
            (C := (AlgebraicGeometry.Scheme.affineLineOver X).Modules)
            (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).one
            (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S m)
            ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).mul 0 m)
    _ = (CategoryTheory.MonoidalCategoryStruct.whiskerLeft
          (𝟙_ (AlgebraicGeometry.Scheme.affineLineOver X).Modules)
          (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S m)) ≫
        ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).one ▷
          (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part m) ≫
        (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).mul 0 m := by
          exact (CategoryTheory.MonoidalCategory.whisker_exchange_assoc
            (C := (AlgebraicGeometry.Scheme.affineLineOver X).Modules)
            (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).one
            (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S m)
            ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).mul 0 m)).symm
    _ = (CategoryTheory.MonoidalCategoryStruct.whiskerLeft
          (𝟙_ (AlgebraicGeometry.Scheme.affineLineOver X).Modules)
          (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S m)) ≫
        (λ_ ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part m)).hom ≫
        eqToHom (congrArg (fun j =>
          (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part j)
          (Nat.zero_add m).symm) := by
          exact congrArg
            (fun q =>
              (CategoryTheory.MonoidalCategoryStruct.whiskerLeft
                (𝟙_ (AlgebraicGeometry.Scheme.affineLineOver X).Modules)
                (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S m)) ≫ q)
            ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).one_mul m)
    _ = (λ_ (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S m)).hom ≫
        AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S m ≫
        eqToHom (congrArg (fun j =>
          (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part j)
          (Nat.zero_add m).symm) := by
          rw [← Category.assoc]
          rw [CategoryTheory.MonoidalCategory.leftUnitor_naturality]
          rw [Category.assoc]
    _ = (λ_ (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S m)).hom ≫
        eqToHom (congrArg (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S)
          (Nat.zero_add m).symm) ≫
        AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S (0 + m) := by
          have hcast :
              eqToHom (congrArg (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S)
                (Nat.zero_add m).symm) ≫
                AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S (0 + m) =
              AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S m ≫
                eqToHom (congrArg (fun j =>
                  (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part j)
                  (Nat.zero_add m).symm) := by
            simpa using
              (CategoryTheory.eqToHom_naturality
                (fun j => AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S j)
                (Nat.zero_add m).symm)
          exact congrArg
            (fun q =>
              (λ_ (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S m)).hom ≫ q)
            hcast.symm

theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.mul_assoc {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m n p : ℕ) :
    (α_ (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S m) (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S n) (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S p)).hom ≫
        (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S m ◁ AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.mulHom S n p) ≫ AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.mulHom S m (n + p) =
      (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.mulHom S m n ▷ AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S p) ≫ AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.mulHom S (m + n) p ≫
        eqToHom (congrArg (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S) (Nat.add_assoc m n p)) := by
  apply (cancel_mono (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S (m + (n + p)))).1
  simp only [Category.assoc]
  rw [AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.eqToHom_comp_incl S (Nat.add_assoc m n p)]
  unfold AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.mulHom
  simp only [Category.assoc, CategoryTheory.Abelian.monoLift_comp,
    CategoryTheory.Abelian.monoLift_comp_assoc]
  rw [CategoryTheory.MonoidalCategory.whiskerLeft_comp_tensorHom_assoc,
    CategoryTheory.MonoidalCategory.whiskerRight_comp_tensorHom_assoc,
    CategoryTheory.Abelian.monoLift_comp, CategoryTheory.Abelian.monoLift_comp,
    ← CategoryTheory.MonoidalCategory.tensorHom_comp_whiskerLeft_assoc,
    ← CategoryTheory.MonoidalCategory.tensorHom_comp_whiskerRight_assoc,
    ← CategoryTheory.MonoidalCategory.associator_naturality_assoc,
    (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).mul_assoc m n p]

theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.mul_comm {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m n : ℕ) :
    (β_ (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S m) (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S n)).hom ≫ AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.mulHom S n m =
      AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.mulHom S m n ≫ eqToHom (congrArg (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S) (Nat.add_comm m n)) := by
  apply (cancel_mono (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S (n + m))).1
  simp only [Category.assoc]
  rw [AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.eqToHom_comp_incl S (Nat.add_comm m n)]
  unfold AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.mulHom
  simp only [Category.assoc, CategoryTheory.Abelian.monoLift_comp,
    CategoryTheory.Abelian.monoLift_comp_assoc]
  rw [← CategoryTheory.BraidedCategory.braiding_naturality_assoc,
    (S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).mul_comm m n]

/-- The extended Rees deformation (normalized in `λ`): the graded algebra on `𝔸¹_X` whose `j`-th piece is
`R_j := Im(⊕_{e=0}^{j} π^*I^{(j-e)}_j --Σ λ^e·π^*(incl)--> π^*S_j) = Σ_e λ^e·π^*I^{(j-e)}_j ⊆ π^*S_j` (`π = toBase`).
Locally, for `S = O[x_{i,q}]` (`x_{i,q}` of weight `q`), `R = O[λ][y_{i,q}]` with `y_{i,q} = λ^{q-1} x_{i,q}`: the fiber
at `λ = 1` is `S` and the fiber at `λ = 0` is `gr_{S_+} S`. Multiplication and unit are those of `π^*S` restricted to
the images (`Abelian.monoLift`). -/

noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) :
    (AlgebraicGeometry.Scheme.affineLineOver X).GradedQCAlgebra where
  part := AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S
  quasicoherent := AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part_isQuasicoherent S
  mul := AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.mulHom S
  one := AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.oneHom S
  one_mul := AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.one_mul S
  mul_assoc := AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.mul_assoc S
  mul_comm := AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.mul_comm S

/-- The graded algebra family of the first deformation: the extended Rees deformation of the jet graded algebra (a
construction, independent of any choice). -/

noncomputable def deformedJetAlgebra {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) (r : ℕ) :
    (AlgebraicGeometry.Scheme.affineLineOver C.toScheme).GradedQCAlgebra :=
  (jetGradedAlgebra (k := k) Z sec hs r).1.reesDeformation


/-- Along `λ = 1`, every power `λ^e` pulls back to `1`. -/
theorem AlgebraicGeometry.Scheme.affineLineOver.sectionAt_one_appTop_coord_pow {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (e : ℕ) :
    (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X (1 : k)).appTop
        ((AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1)) :
          Γ(AlgebraicGeometry.Scheme.affineLineOver X, ⊤)) ^ e) = 1 := by
  refine (map_pow ((AlgebraicGeometry.Scheme.affineLineOver.sectionAt X (1 : k)).appTop).hom
    (AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1)) :
      Γ(AlgebraicGeometry.Scheme.affineLineOver X, ⊤)) e).trans ?_
  have h : (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X (1 : k)).appTop
      (AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1))) =
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv (1 : k)) :=
    AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord _ _ _
  refine (congrArg (· ^ e) h).trans ?_
  simp only [map_one, one_pow]

/-- **Key input for the fibre at `λ = 1`**: the pullback along `s = sectionAt X 1` of multiplication by `λ^e` is
the identity (`s^♯ λ = 1`; `pullback_map_unitScalar` + `unitMul_one`). -/
theorem AlgebraicGeometry.Scheme.affineLineOver.pullback_sectionAt_one_map_mulCoordPow {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (e : ℕ)
    (M : (AlgebraicGeometry.Scheme.affineLineOver X).Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X (1 : k))).map
        (AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow e M) = 𝟙 _ := by
  have h := AlgebraicGeometry.Scheme.Modules.pullback_map_unitScalar
    (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X (1 : k))
    ((AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1)) :
      Γ(AlgebraicGeometry.Scheme.affineLineOver X, ⊤)) ^ e) M
  have key : ∀ f : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules, f = 𝟙 _ →
      (λ_ ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X (1 : k))).obj M)).inv ≫
        (f ▷ (AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X (1 : k))).obj M) ≫
        (λ_ ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X (1 : k))).obj M)).hom = 𝟙 _ := by
    rintro f rfl
    rw [CategoryTheory.MonoidalCategory.id_whiskerRight, Category.id_comp, Iso.inv_hom_id]
  refine h.trans (key _ ?_)
  dsimp only
  exact (congrArg AlgebraicGeometry.Scheme.Modules.unitMul
    (AlgebraicGeometry.Scheme.affineLineOver.sectionAt_one_appTop_coord_pow X e)).trans
    AlgebraicGeometry.Scheme.Modules.unitMul_one

/-- The inclusions `incl S j : R_j → π^*S_j` form a morphism of graded QC algebras `R ⟶ S.pullback π`
(compatibility with `mul`/`one` is `Abelian.monoLift_comp`). -/
noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.inclHom {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) :
    S.reesDeformation ⟶ S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X) where
  app := AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S
  map_mul m n := CategoryTheory.Abelian.monoLift_comp
    (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S (m + n)) _ _
  map_one := CategoryTheory.Abelian.monoLift_comp
    (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S 0) _ _

/-- `λ^j · π^*S_j ⊆ R_j`: multiplication by `λ^j` on `π^*S_j` lands in the `j`-th Rees piece (it is the `e = j`
component of `gen S j`, since `I^{(0)}_j = S_j`). -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.landsInPart_mulCoordPow_self
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (j : ℕ) :
    AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.LandsInPart S
      (AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow j
        ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part j)) := by
  have hc : AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.LandsInPart S
      (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.pullMap S (S.irrelevantPow (j - j) j).2 ≫
        AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow j
          ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part j)) :=
    AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.landsInPart_gen_component S j
      ⟨j, Nat.lt_succ_self j⟩
  have ht := AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.landsInPart_transport S (Nat.sub_self j) hc
  have hid : AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.pullMap S (S.irrelevantPow 0 j).2 =
      𝟙 ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part j) :=
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).map_id
      (S.part j)
  unfold AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.LandsInPart at ht ⊢
  have e1 := congrArg (fun q => (q ≫ AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow j
      ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part j)) ≫
    CategoryTheory.Limits.cokernel.π (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S j)) hid
  have e2 : (𝟙 ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part j) ≫
        AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow j
          ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part j)) ≫
      CategoryTheory.Limits.cokernel.π (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S j) =
      AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow j
          ((S.pullback (AlgebraicGeometry.Scheme.affineLineOver.toBase X)).part j) ≫
        CategoryTheory.Limits.cokernel.π (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S j) := by
    rw [Category.id_comp]
  exact e2.symm.trans (e1.symm.trans ht)

/-- **The fibre of the Rees deformation at `λ = 1` is `S` itself.** Source: Lemma 2.3 of the paper
(at `λ = 1` the rescaled coordinates are the original ones); Stacks 052P (extended Rees algebra:
`R[λ⁻¹] = S[λ, λ⁻¹]`).

Proof, by a purely categorical argument:
let `s := sectionAt X 1`, `π := toBase X`, so `s ≫ π = 𝟙 X` (`AffineSpace.homOfVector_over`) and `s^♯ λ = 1`
(`AffineSpace.homOfVector_appTop_coord`). The inclusions `incl S j : R_j → π^*S_j` form a morphism of graded QC algebras
`inclHom S : R ⟶ S.pullback π` (`Abelian.monoLift_comp`). For each `j`, multiplication by `λ^j` on `π^*S_j` lands in
`R_j` (`landsInPart_mulCoordPow_self`: it is the `e = j` component of `gen S j`, `I^{(0)}_j = S_j`), giving
`t_j : π^*S_j → R_j` with `t_j ≫ incl = mulCoordPow j` and, by `cancel_mono` + `mulCoordPow_naturality`,
`incl ≫ t_j = mulCoordPow j` on `R_j`. Since `s^*` is a strong monoidal functor and `s^♯ λ^j = 1`,
`s^*(mulCoordPow j M) = 𝟙` for every `M` (`pullback_sectionAt_one_map_mulCoordPow`, from `pullback_map_unitScalar`),
so `s^*(incl S j)` is an isomorphism with inverse `s^*t_j`; a componentwise isomorphism of graded QC algebras is an
isomorphism (`isIso_of_isIso_app`). Finally `R.pullback s ≅ (S.pullback π).pullback s ≅ S.pullback (s ≫ π) =
S.pullback (𝟙 X) ≅ S` (`pullbackMap`, `pullbackComp`, `eqToIso`, `GradedQCAlgebra.pullbackId`). -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation_restrictToLambda_one {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (S : X.GradedQCAlgebra) :
    Nonempty (S.reesDeformation.restrictToLambda (1 : k) ≅ S) := by
  let s : X ⟶ AlgebraicGeometry.Scheme.affineLineOver X :=
    AlgebraicGeometry.Scheme.affineLineOver.sectionAt X (1 : k)
  let π : AlgebraicGeometry.Scheme.affineLineOver X ⟶ X := AlgebraicGeometry.Scheme.affineLineOver.toBase X
  have hsπ : s ≫ π = 𝟙 X := AlgebraicGeometry.AffineSpace.homOfVector_over _ _
  let φ := AlgebraicGeometry.Scheme.GradedQCAlgebra.pullbackMap
    (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.inclHom S) s
  have hiso : ∀ m, IsIso (φ.app m) := by
    intro m
    let t := CategoryTheory.Abelian.monoLift (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S m)
      (AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow m ((S.pullback π).part m))
      (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.landsInPart_mulCoordPow_self S m)
    have ht : t ≫ AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S m =
        AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow m ((S.pullback π).part m) :=
      CategoryTheory.Abelian.monoLift_comp _ _ _
    have h1 : AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S m ≫ t =
        AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow m
          (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.part S m) := by
      apply (cancel_mono (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S m)).1
      rw [Category.assoc, ht, AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow_naturality]
    refine ⟨⟨(AlgebraicGeometry.Scheme.Modules.pullback s).map t, ?_, ?_⟩⟩
    · change (AlgebraicGeometry.Scheme.Modules.pullback s).map
          (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S m) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback s).map t = 𝟙 _
      rw [← Functor.map_comp, h1,
        AlgebraicGeometry.Scheme.affineLineOver.pullback_sectionAt_one_map_mulCoordPow]
    · change (AlgebraicGeometry.Scheme.Modules.pullback s).map t ≫
        (AlgebraicGeometry.Scheme.Modules.pullback s).map
          (AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S m) = 𝟙 _
      rw [← Functor.map_comp, ht,
        AlgebraicGeometry.Scheme.affineLineOver.pullback_sectionAt_one_map_mulCoordPow]
  have hφ : IsIso φ := @AlgebraicGeometry.Scheme.GradedQCAlgebra.isIso_of_isIso_app _ _ _ φ hiso
  exact ⟨@asIso _ _ _ _ φ hφ ≪≫ (AlgebraicGeometry.Scheme.GradedQCAlgebra.pullbackComp S s π).symm ≪≫
    eqToIso (congrArg S.pullback hsπ) ≪≫ AlgebraicGeometry.Scheme.GradedQCAlgebra.pullbackId S⟩

end
