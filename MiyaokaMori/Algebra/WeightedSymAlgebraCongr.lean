import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.GradedQCAlgebraIsoMk
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQcAlgebraCategory
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymGradedAlgebraCongr
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualFunctor

/-! # The weighted symmetric algebra is functorial in isomorphisms

A family of termwise isomorphisms `V_q ≅ V'_q` (`q < r`) of locally free sheaves of finite type gives
an isomorphism of weighted symmetric algebras `weightedSymAlgebra V ≅ weightedSymAlgebra V'`.

Proof:
1. Duality is a (contravariant) functor: `V_q ≅ V'_q` gives `W_q := V_q^∨ ≅ V'_q^∨ =: W'_q`
   (`AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso`; `Modules.dual` is `AlgebraicGeometry.Scheme.Modules.moduleSheafDual` by definition;
   `dualMapIso`).
2. `Sym` is a functor: `W ≅ W'` gives an isomorphism of graded algebras
   `symGradedAlgebra W ≅ symGradedAlgebra W'` (`symGradedAlgebra_congr`: both sides of the `dite` fall
   into the same branch; the true branch is assembled from `symPowMapIso` and `symPowMul_symPowMap`).
3. `weightedSymTensor r W d = ⊗_q Sym^{d_q} W_q` is defined recursively in `r`; take the tensor
   product of the graded-piece isomorphisms of step 2 factor by factor (`weightedSymTensorIso`); it is
   compatible with `weightedSymTensorMul` (`tensorμ_natural` and `map_mul` of each factor) and with
   `weightedSymTensorOne` (`map_one` of each factor).
4. `part m = ⨁_{d ∈ D_m} T_d`: `biproduct.mapIso`; `mulHom` and `oneHom` are composites of the
   morphisms of step 3 with `biproduct.π`/`ι`, compared termwise (`biproduct.ι_map`,
   `biproduct.map_π`), giving an isomorphism of `GradedQCAlgebra`s (`GradedQCAlgebra.isoMk`; the
   inverse compatibilities are automatic).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

section general
variable {C : Type*} [Category C] [MonoidalCategory C]

/- Lemma at the level of variables: in `mulHom` the intermediate objects of
   `weightedSymTensorMul ≫ biproduct.ι` are only definitionally equal (`d + d'` versus `(d.add d').1`),
   so `simp`/`rw` cannot reassociate there; the comparison of one summand is abstracted into variable
   form and applied with `exact`. -/
private theorem aux_summand {A₁ A₂ A₁' A₂' Z Z' P₁ P₂ P₁' P₂' Q Q' : C}
    (π₁ : P₁ ⟶ A₁) (π₂ : P₂ ⟶ A₂) (μ : A₁ ⊗ A₂ ⟶ Z) (ι : Z ⟶ Q) (mapQ : Q ⟶ Q')
    (mapP₁ : P₁ ⟶ P₁') (mapP₂ : P₂ ⟶ P₂') (π₁' : P₁' ⟶ A₁') (π₂' : P₂' ⟶ A₂')
    (μ' : A₁' ⊗ A₂' ⟶ Z') (ι' : Z' ⟶ Q') (i₁ : A₁ ⟶ A₁') (i₂ : A₂ ⟶ A₂') (iZ : Z ⟶ Z')
    (hι : ι ≫ mapQ = iZ ≫ ι') (hμ : μ ≫ iZ = (i₁ ⊗ₘ i₂) ≫ μ')
    (h₁ : π₁ ≫ i₁ = mapP₁ ≫ π₁') (h₂ : π₂ ≫ i₂ = mapP₂ ≫ π₂') :
    ((π₁ ⊗ₘ π₂) ≫ (μ ≫ ι)) ≫ mapQ = (mapP₁ ⊗ₘ mapP₂) ≫ (π₁' ⊗ₘ π₂') ≫ μ' ≫ ι' := by
  rw [Category.assoc, Category.assoc, hι, ← Category.assoc μ, hμ, Category.assoc, ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, h₁, h₂, ← MonoidalCategory.tensorHom_comp_tensorHom,
    Category.assoc]

end general

section general'
variable {C : Type*} [Category C]

private theorem aux_one {U Z Z' Q Q' : C} (o : U ⟶ Z) (ι : Z ⟶ Q) (mapQ : Q ⟶ Q') (iZ : Z ⟶ Z')
    (ι' : Z' ⟶ Q') (o' : U ⟶ Z') (hι : ι ≫ mapQ = iZ ≫ ι') (ho : o ≫ iZ = o') :
    (o ≫ ι) ≫ mapQ = o' ≫ ι' := by
  rw [Category.assoc, hι, ← Category.assoc, ho]

end general'

namespace AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The dual of an isomorphism (contravariant): `Modules.dual` is `moduleSheafDual` by definition, so
the dual functor applies directly. -/
def Modules.dualMapIso {V W : X.Modules} (e : V ≅ W) : Modules.dual W ≅ Modules.dual V :=
  AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso e

/-- The factorwise isomorphism `⊗_q Sym^{d q}(W q) ≅ ⊗_q Sym^{d q}(W' q)` induced by a family of graded
algebra isomorphisms `φ_q : Sym(W q) ≅ Sym(W' q)`. -/
def weightedSymTensorIso : (r : ℕ) → (W W' : Fin r → X.Modules) →
    (∀ q, Modules.symGradedAlgebra (W q) ≅ Modules.symGradedAlgebra (W' q)) → (d : Fin r → ℕ) →
    (weightedSymTensor r W d ≅ weightedSymTensor r W' d)
  | 0, _, _, _, _ => Iso.refl _
  | r + 1, W, W', φ, d =>
      MonoidalCategory.tensorIso (GradedQCAlgebra.partIso (φ 0) (d 0))
        (weightedSymTensorIso r (Fin.tail W) (Fin.tail W') (fun q => φ q.succ) (Fin.tail d))

theorem weightedSymTensorIso_zero_hom (W W' : Fin 0 → X.Modules)
    (φ : ∀ q, Modules.symGradedAlgebra (W q) ≅ Modules.symGradedAlgebra (W' q)) (d : Fin 0 → ℕ) :
    (weightedSymTensorIso 0 W W' φ d).hom = 𝟙 _ := rfl

theorem weightedSymTensorIso_succ_hom (r : ℕ) (W W' : Fin (r + 1) → X.Modules)
    (φ : ∀ q, Modules.symGradedAlgebra (W q) ≅ Modules.symGradedAlgebra (W' q)) (d : Fin (r + 1) → ℕ) :
    (weightedSymTensorIso (r + 1) W W' φ d).hom =
      (φ 0).hom.app (d 0) ⊗ₘ
        (weightedSymTensorIso r (Fin.tail W) (Fin.tail W') (fun q => φ q.succ) (Fin.tail d)).hom := rfl

/-- The factorwise isomorphism is compatible with `weightedSymTensorMul`. -/
theorem weightedSymTensorMul_iso : ∀ (r : ℕ) (W W' : Fin r → X.Modules)
    (φ : ∀ q, Modules.symGradedAlgebra (W q) ≅ Modules.symGradedAlgebra (W' q)) (d d' : Fin r → ℕ),
    weightedSymTensorMul r W d d' ≫ (weightedSymTensorIso r W W' φ (d + d')).hom =
      ((weightedSymTensorIso r W W' φ d).hom ⊗ₘ (weightedSymTensorIso r W W' φ d').hom) ≫
        weightedSymTensorMul r W' d d'
  | 0, _, _, _, _, _ => by
    show (λ_ (𝟙_ X.Modules)).hom ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ (λ_ (𝟙_ X.Modules)).hom
    rw [Category.comp_id, MonoidalCategory.id_tensorHom_id, Category.id_comp]
  | r + 1, W, W', φ, d, d' => by
    show (MonoidalCategory.tensorμ _ _ _ _ ≫
        ((Modules.symGradedAlgebra (W 0)).mul (d 0) (d' 0) ⊗ₘ
          weightedSymTensorMul r (Fin.tail W) (Fin.tail d) (Fin.tail d'))) ≫
        ((φ 0).hom.app (d 0 + d' 0) ⊗ₘ
          (weightedSymTensorIso r (Fin.tail W) (Fin.tail W') (fun q => φ q.succ)
            (Fin.tail d + Fin.tail d')).hom) =
      (((φ 0).hom.app (d 0) ⊗ₘ
          (weightedSymTensorIso r (Fin.tail W) (Fin.tail W') (fun q => φ q.succ) (Fin.tail d)).hom) ⊗ₘ
        ((φ 0).hom.app (d' 0) ⊗ₘ
          (weightedSymTensorIso r (Fin.tail W) (Fin.tail W') (fun q => φ q.succ) (Fin.tail d')).hom)) ≫
      (MonoidalCategory.tensorμ _ _ _ _ ≫
        ((Modules.symGradedAlgebra (W' 0)).mul (d 0) (d' 0) ⊗ₘ
          weightedSymTensorMul r (Fin.tail W') (Fin.tail d) (Fin.tail d')))
    rw [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, (φ 0).hom.map_mul,
      weightedSymTensorMul_iso r (Fin.tail W) (Fin.tail W') (fun q => φ q.succ) (Fin.tail d) (Fin.tail d'),
      ← MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorμ_natural_assoc]

/-- The factorwise isomorphism is compatible with `weightedSymTensorOne`. -/
theorem weightedSymTensorOne_iso : ∀ (r : ℕ) (W W' : Fin r → X.Modules)
    (φ : ∀ q, Modules.symGradedAlgebra (W q) ≅ Modules.symGradedAlgebra (W' q)),
    weightedSymTensorOne r W ≫ (weightedSymTensorIso r W W' φ 0).hom = weightedSymTensorOne r W'
  | 0, _, _, _ => by
    show 𝟙 (𝟙_ X.Modules) ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id]
  | r + 1, W, W', φ => by
    show ((λ_ (𝟙_ X.Modules)).inv ≫
        ((Modules.symGradedAlgebra (W 0)).one ⊗ₘ weightedSymTensorOne r (Fin.tail W))) ≫
        ((φ 0).hom.app 0 ⊗ₘ
          (weightedSymTensorIso r (Fin.tail W) (Fin.tail W') (fun q => φ q.succ) 0).hom) =
      (λ_ (𝟙_ X.Modules)).inv ≫
        ((Modules.symGradedAlgebra (W' 0)).one ⊗ₘ weightedSymTensorOne r (Fin.tail W'))
    rw [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, (φ 0).hom.map_one,
      weightedSymTensorOne_iso r (Fin.tail W) (Fin.tail W') (fun q => φ q.succ)]

namespace weightedSymAlgebra

variable {r : ℕ} (V V' : Fin r → X.Modules)
  (φ : ∀ q, Modules.symGradedAlgebra (Modules.dual (V q)) ≅ Modules.symGradedAlgebra (Modules.dual (V' q)))

/-- The isomorphism of graded pieces `part V m ≅ part V' m` (termwise on the biproduct). -/
def partIso (m : ℕ) : part V m ≅ part V' m :=
  biproduct.mapIso fun d : weightedSymIndex r m =>
    weightedSymTensorIso r (gen V) (gen V') φ (fun q => (d.1 q : ℕ))

theorem mulHom_iso (m n : ℕ) :
    mulHom V m n ≫ (partIso V V' φ (m + n)).hom =
      ((partIso V V' φ m).hom ⊗ₘ (partIso V V' φ n).hom) ≫ mulHom V' m n := by
  simp only [mulHom, partIso, biproduct.mapIso_hom, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact aux_summand _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (biproduct.ι_map (fun b : weightedSymIndex r (m + n) =>
      (weightedSymTensorIso r (gen V) (gen V') φ fun q => (b.1 q : ℕ)).hom) (p.1.add p.2))
    (weightedSymTensorMul_iso r (gen V) (gen V') φ (fun q => (p.1.1 q : ℕ)) (fun q => (p.2.1 q : ℕ)))
    (biproduct.map_π (fun b : weightedSymIndex r m =>
      (weightedSymTensorIso r (gen V) (gen V') φ fun q => (b.1 q : ℕ)).hom) p.1).symm
    (biproduct.map_π (fun b : weightedSymIndex r n =>
      (weightedSymTensorIso r (gen V) (gen V') φ fun q => (b.1 q : ℕ)).hom) p.2).symm

theorem oneHom_iso : oneHom V ≫ (partIso V V' φ 0).hom = oneHom V' := by
  exact aux_one _ _ _ _ _ _
    (biproduct.ι_map (fun b : weightedSymIndex r 0 =>
      (weightedSymTensorIso r (gen V) (gen V') φ fun q => (b.1 q : ℕ)).hom)
      (⟨0, by simp⟩ : weightedSymIndex r 0))
    (weightedSymTensorOne_iso r (gen V) (gen V') φ)

end weightedSymAlgebra

/-- The isomorphism of weighted symmetric algebras assembled from a family of graded algebra
isomorphisms `Sym(V_q^∨) ≅ Sym(V'_q^∨)`. -/
def weightedSymAlgebraIso {r : ℕ} (V V' : Fin r → X.Modules)
    [∀ q, (V q).IsLocallyFree] [∀ q, (V q).IsFiniteType]
    [∀ q, (V' q).IsLocallyFree] [∀ q, (V' q).IsFiniteType]
    (φ : ∀ q, Modules.symGradedAlgebra (Modules.dual (V q)) ≅
      Modules.symGradedAlgebra (Modules.dual (V' q))) :
    weightedSymAlgebra V ≅ weightedSymAlgebra V' :=
  GradedQCAlgebra.isoMk (fun m => weightedSymAlgebra.partIso V V' φ m)
    (weightedSymAlgebra.mulHom_iso V V' φ) (weightedSymAlgebra.oneHom_iso V V' φ)

end AlgebraicGeometry.Scheme

theorem AlgebraicGeometry.Scheme.weightedSymAlgebra_congr {X : AlgebraicGeometry.Scheme.{u}}
    {r : ℕ} (V V' : Fin r → X.Modules)
    [∀ q, (V q).IsLocallyFree] [∀ q, (V q).IsFiniteType]
    [∀ q, (V' q).IsLocallyFree] [∀ q, (V' q).IsFiniteType]
    (e : ∀ q, Nonempty (V q ≅ V' q)) :
    Nonempty (AlgebraicGeometry.Scheme.weightedSymAlgebra V ≅
      AlgebraicGeometry.Scheme.weightedSymAlgebra V') :=
  ⟨AlgebraicGeometry.Scheme.weightedSymAlgebraIso V V' fun q =>
    AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_congr
      (AlgebraicGeometry.Scheme.Modules.dualMapIso (e q).some).symm⟩

end
