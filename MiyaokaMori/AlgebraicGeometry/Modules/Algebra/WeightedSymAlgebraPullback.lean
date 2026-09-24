import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.SheafDualLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualPullbackCommute
import MiyaokaMori.AlgebraicGeometry.Proj.GradedQCAlgebraIsoMk
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackRank
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymGradedAlgebraCongr
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01b6
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.Stacks01ci

/-! # The weighted symmetric algebra commutes with pullback

The weighted symmetric algebra commutes with pullback: `g^*(weightedSymAlgebra V) ≅ weightedSymAlgebra (g^* V)`
as graded quasi-coherent algebras (§2 of the paper; independent of the local structure of the weighted
symmetric algebra). Sources: Stacks 01CI (Sym commutes with
pullback), Stacks 01CD (pullback is strong monoidal, `Modules.pullbackMonoidal`), Stacks 01CK/01CL
(dual of a finite locally free module commutes with pullback, `Modules.dual_pullback`), left adjoints preserve
finite biproducts (`Modules.pullback g ⊣ pushforward`, `Functor.mapBiproduct`).

## Route

Write `F := g^*`, `W_q := V_q^∨`, `W'_q := (g^* V_q)^∨`. The only input is a family of **graded-algebra**
isomorphisms `ψ_q : (Sym W_q).pullback g ≅ Sym W'_q`; no canonical maps are needed, because every
compatibility below is a consequence of `ψ_q.map_mul`/`map_one` together with the (strong) monoidal structure
`μ, ε` of `F` (`Functor.Monoidal`, `Functor.LaxBraided`).

1. `pullbackWeightedSymTensorIso`: `F (⊗_q Sym^{d_q} W_q) ≅ ⊗_q Sym^{d_q} W'_q`, by induction on `r`:
   `r = 0` is `η : F(𝟙_) ≅ 𝟙_`; `r + 1` is `δ : F(A ⊗ B) ≅ F A ⊗ F B` followed by `ψ_0.app (d 0) ⊗ IH`.
2. `pullbackWeightedSymTensorMul_iso`: compatibility with `weightedSymTensorMul` in the lax-monoidal sense
   `μ ≫ F(mul) ≫ iso = (iso ⊗ iso) ≫ mul'`. `r = 0` is `Functor.Monoidal.map_leftUnitor`; `r + 1` uses the
   braided coherence `tensorμ_comp_μ_tensorHom_μ_comp_μ` (Mathlib), `μ_natural`, `tensorμ_natural`,
   `ψ_0.hom.map_mul` and the induction hypothesis. `pullbackWeightedSymTensorOne_iso` likewise, with
   `map_leftUnitor_inv` and `map_one`.
3. `weightedSymAlgebra.pullbackPartIso`: `F(⨁_d T_d) ≅ ⨁_d F T_d ≅ ⨁_d T'_d` (`Functor.mapBiproduct`, which
   exists because `F` is a left adjoint; `biproduct.mapIso`).
4. `pullbackMulHom_iso` / `pullbackOneHom_iso`: `F` is additive (`Adjunction.left_adjoint_additive`), so
   `F(∑_{a,b} (π_a ⊗ π_b) ≫ mul_{a,b} ≫ ι_{a+b})` is the corresponding sum, and each summand is transported
   by 2 and the `π`/`ι` lemmas for `mapBiproduct`. Then `GradedQCAlgebra.isoMk` assembles the iso
   (`weightedSymAlgebraPullbackIso`).
5. `weightedSymAlgebra_pullback`: take `ψ_q := (01CI iso) ≪≫ symGradedAlgebra_congr (dual_pullback g V_q).symm`,
   where `V_q^∨` is quasi-coherent because it is locally free (`isLocallyFree_dual'`).
The input `Modules.symGradedAlgebra_pullback` is Stacks 01CI.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

section general
variable {C : Type*} [Category C] [MonoidalCategory C] {D : Type*} [Category D] [MonoidalCategory D]
  (F : C ⥤ D) [F.LaxMonoidal]

/-- One summand of `mulHom`, transported through a lax monoidal functor (variable form, because the
intermediate objects `T_{a+b}` and `T_{(a.add b)}` are only definitionally equal). -/
private theorem wsaPullback_aux_summand {A₁ A₂ Z P₁ P₂ Q : C} {A₁' A₂' Z' P₁' P₂' Q' : D}
    (π₁ : P₁ ⟶ A₁) (π₂ : P₂ ⟶ A₂) (m : A₁ ⊗ A₂ ⟶ Z) (ι : Z ⟶ Q)
    (e₁ : F.obj A₁ ⟶ A₁') (e₂ : F.obj A₂ ⟶ A₂') (eZ : F.obj Z ⟶ Z') (eP₁ : F.obj P₁ ⟶ P₁')
    (eP₂ : F.obj P₂ ⟶ P₂') (eQ : F.obj Q ⟶ Q')
    (π₁' : P₁' ⟶ A₁') (π₂' : P₂' ⟶ A₂') (m' : A₁' ⊗ A₂' ⟶ Z') (ι' : Z' ⟶ Q')
    (hπ₁ : F.map π₁ ≫ e₁ = eP₁ ≫ π₁') (hπ₂ : F.map π₂ ≫ e₂ = eP₂ ≫ π₂')
    (hm : Functor.LaxMonoidal.μ F A₁ A₂ ≫ F.map m ≫ eZ = (e₁ ⊗ₘ e₂) ≫ m')
    (hι : F.map ι ≫ eQ = eZ ≫ ι') :
    (Functor.LaxMonoidal.μ F P₁ P₂ ≫ F.map ((π₁ ⊗ₘ π₂) ≫ m ≫ ι)) ≫ eQ =
      (eP₁ ⊗ₘ eP₂) ≫ (π₁' ⊗ₘ π₂') ≫ m' ≫ ι' := by
  rw [F.map_comp, F.map_comp, ← Functor.LaxMonoidal.μ_natural_assoc]
  simp only [Category.assoc]
  rw [hι, reassoc_of% hm, ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, hπ₁, hπ₂,
    ← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]

private theorem wsaPullback_aux_one {Z Q : C} {Z' Q' : D} (o : 𝟙_ C ⟶ Z) (ι : Z ⟶ Q)
    (eZ : F.obj Z ⟶ Z') (eQ : F.obj Q ⟶ Q') (ι' : Z' ⟶ Q') (o' : 𝟙_ D ⟶ Z')
    (hι : F.map ι ≫ eQ = eZ ≫ ι')
    (ho : Functor.LaxMonoidal.ε F ≫ F.map o ≫ eZ = o') :
    (Functor.LaxMonoidal.ε F ≫ F.map (o ≫ ι)) ≫ eQ = o' ≫ ι' := by
  rw [F.map_comp]
  simp only [Category.assoc]
  rw [hι, ← ho]
  simp only [Category.assoc]

end general

section mapBiproduct
variable {C : Type*} [Category C] {D : Type*} [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] {J : Type*} (f : J → C) [HasBiproduct f]
  [PreservesBiproduct f F]

private theorem wsaPullback_mapBiproduct_hom_π (j : J) :
    (F.mapBiproduct f).hom ≫ biproduct.π (F.obj ∘ f) j = F.map (biproduct.π f j) := by
  rw [Functor.mapBiproduct_hom]
  exact biproduct.lift_π _ _

private theorem wsaPullback_map_ι_mapBiproduct_hom (j : J) :
    F.map (biproduct.ι f j) ≫ (F.mapBiproduct f).hom = biproduct.ι (F.obj ∘ f) j := by
  rw [← biproduct.ι_desc (fun j => F.map (biproduct.ι f j)) j, ← Functor.mapBiproduct_inv,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end mapBiproduct

namespace AlgebraicGeometry.Scheme

open CategoryTheory.MonoidalCategory

variable {X X' : AlgebraicGeometry.Scheme.{u}} (g : X' ⟶ X)

/-- `e.app m` for a graded-algebra iso `e : S.pullback g ≅ T`, **typed** as an iso out of
`g^*(S.part m)`. This is definitionally `GradedQCAlgebra.partIso e m`, but `rw`/`simp` compare types
syntactically (`(S.pullback g).part m` vs `(pullback g).obj (S.part m)`), so the compatibilities below are
restated through this wrapper. -/
def GradedQCAlgebra.pullbackIsoApp {S : X.GradedQCAlgebra} {T : X'.GradedQCAlgebra}
    (e : S.pullback g ≅ T) (m : ℕ) : (Modules.pullback g).obj (S.part m) ≅ T.part m :=
  GradedQCAlgebra.partIso e m

theorem GradedQCAlgebra.pullbackIsoApp_hom {S : X.GradedQCAlgebra} {T : X'.GradedQCAlgebra}
    (e : S.pullback g ≅ T) (m : ℕ) : (GradedQCAlgebra.pullbackIsoApp g e m).hom = e.hom.app m := rfl

/-- `map_mul` of `e.hom`, in the lax-monoidal form `μ ≫ g^*(mul) ≫ e = (e ⊗ e) ≫ mul'`. -/
theorem GradedQCAlgebra.pullbackIsoApp_map_mul {S : X.GradedQCAlgebra} {T : X'.GradedQCAlgebra}
    (e : S.pullback g ≅ T) (m n : ℕ) :
    (Functor.LaxMonoidal.μ (Modules.pullback g) (S.part m) (S.part n) ≫
        (Modules.pullback g).map (S.mul m n)) ≫ (GradedQCAlgebra.pullbackIsoApp g e (m + n)).hom =
      ((GradedQCAlgebra.pullbackIsoApp g e m).hom ⊗ₘ (GradedQCAlgebra.pullbackIsoApp g e n).hom) ≫
        T.mul m n :=
  e.hom.map_mul m n

/-- `map_one` of `e.hom`, in the lax-monoidal form `ε ≫ g^*(one) ≫ e = one'`. -/
theorem GradedQCAlgebra.pullbackIsoApp_map_one {S : X.GradedQCAlgebra} {T : X'.GradedQCAlgebra}
    (e : S.pullback g ≅ T) :
    (Functor.LaxMonoidal.ε (Modules.pullback g) ≫ (Modules.pullback g).map S.one) ≫
        (GradedQCAlgebra.pullbackIsoApp g e 0).hom = T.one :=
  e.hom.map_one

/-- `g^*(⊗_q Sym^{d q}(W q)) ≅ ⊗_q Sym^{d q}(W' q)`, given graded-algebra isos
`ψ_q : (Sym (W q)).pullback g ≅ Sym (W' q)`. Step 1 of the route. -/
def pullbackWeightedSymTensorIso : (r : ℕ) → (W : Fin r → X.Modules) → (W' : Fin r → X'.Modules) →
    (∀ q, (Modules.symGradedAlgebra (W q)).pullback g ≅ Modules.symGradedAlgebra (W' q)) →
    (d : Fin r → ℕ) →
    ((Modules.pullback g).obj (weightedSymTensor r W d) ≅ weightedSymTensor r W' d)
  | 0, _, _, _, _ => (Functor.Monoidal.εIso (Modules.pullback g)).symm
  | r + 1, W, W', ψ, d =>
      (Functor.Monoidal.μIso (Modules.pullback g) _ _).symm ≪≫
        tensorIso (GradedQCAlgebra.pullbackIsoApp g (ψ 0) (d 0))
          (pullbackWeightedSymTensorIso r (Fin.tail W) (Fin.tail W') (fun q => ψ q.succ) (Fin.tail d))

theorem pullbackWeightedSymTensorIso_zero_hom (W : Fin 0 → X.Modules) (W' : Fin 0 → X'.Modules)
    (ψ : ∀ q, (Modules.symGradedAlgebra (W q)).pullback g ≅ Modules.symGradedAlgebra (W' q))
    (d : Fin 0 → ℕ) :
    (pullbackWeightedSymTensorIso g 0 W W' ψ d).hom = (Functor.Monoidal.εIso (Modules.pullback g)).inv := rfl

theorem pullbackWeightedSymTensorIso_succ_hom (r : ℕ) (W : Fin (r + 1) → X.Modules)
    (W' : Fin (r + 1) → X'.Modules)
    (ψ : ∀ q, (Modules.symGradedAlgebra (W q)).pullback g ≅ Modules.symGradedAlgebra (W' q))
    (d : Fin (r + 1) → ℕ) :
    (pullbackWeightedSymTensorIso g (r + 1) W W' ψ d).hom =
      (Functor.Monoidal.μIso (Modules.pullback g) ((Modules.symGradedAlgebra (W 0)).part (d 0))
          (weightedSymTensor r (Fin.tail W) (Fin.tail d))).inv ≫
        ((GradedQCAlgebra.pullbackIsoApp g (ψ 0) (d 0)).hom ⊗ₘ
          (pullbackWeightedSymTensorIso g r (Fin.tail W) (Fin.tail W') (fun q => ψ q.succ)
            (Fin.tail d)).hom) := rfl

/-- Step 2: compatibility of `pullbackWeightedSymTensorIso` with `weightedSymTensorMul`. -/
theorem pullbackWeightedSymTensorMul_iso : ∀ (r : ℕ) (W : Fin r → X.Modules) (W' : Fin r → X'.Modules)
    (ψ : ∀ q, (Modules.symGradedAlgebra (W q)).pullback g ≅ Modules.symGradedAlgebra (W' q))
    (d d' : Fin r → ℕ),
    (Functor.LaxMonoidal.μ (Modules.pullback g) (weightedSymTensor r W d) (weightedSymTensor r W d') ≫
        (Modules.pullback g).map (weightedSymTensorMul r W d d')) ≫
        (pullbackWeightedSymTensorIso g r W W' ψ (d + d')).hom =
      ((pullbackWeightedSymTensorIso g r W W' ψ d).hom ⊗ₘ
          (pullbackWeightedSymTensorIso g r W W' ψ d').hom) ≫
        weightedSymTensorMul r W' d d'
  | 0, _, _, _, _, _ => by
    show (Functor.LaxMonoidal.μ (Modules.pullback g) (𝟙_ X.Modules) (𝟙_ X.Modules) ≫
        (Modules.pullback g).map (λ_ (𝟙_ X.Modules)).hom) ≫ (Functor.Monoidal.εIso (Modules.pullback g)).inv =
      ((Functor.Monoidal.εIso (Modules.pullback g)).inv ⊗ₘ (Functor.Monoidal.εIso (Modules.pullback g)).inv) ≫
        (λ_ (𝟙_ X'.Modules)).hom
    simp only [Functor.Monoidal.εIso_inv]
    rw [Functor.Monoidal.map_leftUnitor, Functor.Monoidal.μ_δ_assoc, Category.assoc,
      ← leftUnitor_naturality, ← tensorHom_def_assoc]
  | r + 1, W, W', ψ, d, d' => by
    have hψ := GradedQCAlgebra.pullbackIsoApp_map_mul g (ψ 0) (d 0) (d' 0)
    have hIH := pullbackWeightedSymTensorMul_iso r (Fin.tail W) (Fin.tail W') (fun q => ψ q.succ)
      (Fin.tail d) (Fin.tail d')
    simp only [Category.assoc] at hψ hIH
    rw [pullbackWeightedSymTensorIso_succ_hom, pullbackWeightedSymTensorIso_succ_hom,
      pullbackWeightedSymTensorIso_succ_hom]
    show (Functor.LaxMonoidal.μ (Modules.pullback g)
          ((Modules.symGradedAlgebra (W 0)).part (d 0) ⊗ weightedSymTensor r (Fin.tail W) (Fin.tail d))
          ((Modules.symGradedAlgebra (W 0)).part (d' 0) ⊗ weightedSymTensor r (Fin.tail W) (Fin.tail d')) ≫
        (Modules.pullback g).map (tensorμ _ _ _ _ ≫
          ((Modules.symGradedAlgebra (W 0)).mul (d 0) (d' 0) ⊗ₘ
            weightedSymTensorMul r (Fin.tail W) (Fin.tail d) (Fin.tail d')))) ≫
        ((Functor.Monoidal.μIso (Modules.pullback g) ((Modules.symGradedAlgebra (W 0)).part (d 0 + d' 0))
            (weightedSymTensor r (Fin.tail W) (Fin.tail d + Fin.tail d'))).inv ≫
          ((GradedQCAlgebra.pullbackIsoApp g (ψ 0) (d 0 + d' 0)).hom ⊗ₘ
            (pullbackWeightedSymTensorIso g r (Fin.tail W) (Fin.tail W') (fun q => ψ q.succ)
              (Fin.tail d + Fin.tail d')).hom)) =
      (((Functor.Monoidal.μIso (Modules.pullback g) ((Modules.symGradedAlgebra (W 0)).part (d 0))
            (weightedSymTensor r (Fin.tail W) (Fin.tail d))).inv ≫
          ((GradedQCAlgebra.pullbackIsoApp g (ψ 0) (d 0)).hom ⊗ₘ
            (pullbackWeightedSymTensorIso g r (Fin.tail W) (Fin.tail W') (fun q => ψ q.succ)
              (Fin.tail d)).hom)) ⊗ₘ
        ((Functor.Monoidal.μIso (Modules.pullback g) ((Modules.symGradedAlgebra (W 0)).part (d' 0))
            (weightedSymTensor r (Fin.tail W) (Fin.tail d'))).inv ≫
          ((GradedQCAlgebra.pullbackIsoApp g (ψ 0) (d' 0)).hom ⊗ₘ
            (pullbackWeightedSymTensorIso g r (Fin.tail W) (Fin.tail W') (fun q => ψ q.succ)
              (Fin.tail d')).hom))) ≫
        (tensorμ _ _ _ _ ≫
          ((Modules.symGradedAlgebra (W' 0)).mul (d 0) (d' 0) ⊗ₘ
            weightedSymTensorMul r (Fin.tail W') (Fin.tail d) (Fin.tail d')))
    simp only [Functor.Monoidal.μIso_inv]
    rw [← cancel_epi (Functor.LaxMonoidal.μ (Modules.pullback g) _ _ ⊗ₘ
      Functor.LaxMonoidal.μ (Modules.pullback g) _ _)]
    conv_rhs => rw [← Category.assoc, tensorHom_comp_tensorHom, Functor.Monoidal.μ_δ_assoc,
      Functor.Monoidal.μ_δ_assoc]
    rw [(Modules.pullback g).map_comp]
    simp only [Category.assoc]
    rw [← tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc, ← Functor.LaxMonoidal.μ_natural_assoc,
      Functor.Monoidal.μ_δ_assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, hψ, hIH,
      ← tensorHom_comp_tensorHom, ← tensorμ_natural_assoc]

/-- Step 2: compatibility of `pullbackWeightedSymTensorIso` with `weightedSymTensorOne`. -/
theorem pullbackWeightedSymTensorOne_iso : ∀ (r : ℕ) (W : Fin r → X.Modules) (W' : Fin r → X'.Modules)
    (ψ : ∀ q, (Modules.symGradedAlgebra (W q)).pullback g ≅ Modules.symGradedAlgebra (W' q)),
    (Functor.LaxMonoidal.ε (Modules.pullback g) ≫ (Modules.pullback g).map (weightedSymTensorOne r W)) ≫
        (pullbackWeightedSymTensorIso g r W W' ψ 0).hom =
      weightedSymTensorOne r W'
  | 0, _, _, _ => by
    show (Functor.LaxMonoidal.ε (Modules.pullback g) ≫ (Modules.pullback g).map (𝟙 (𝟙_ X.Modules))) ≫
        (Functor.Monoidal.εIso (Modules.pullback g)).inv = 𝟙 _
    simp only [Functor.Monoidal.εIso_inv]
    rw [CategoryTheory.Functor.map_id, Category.comp_id, Functor.Monoidal.ε_η]
  | r + 1, W, W', ψ => by
    have hψ := GradedQCAlgebra.pullbackIsoApp_map_one g (ψ 0)
    have hIH := pullbackWeightedSymTensorOne_iso r (Fin.tail W) (Fin.tail W') (fun q => ψ q.succ)
    simp only [Category.assoc] at hψ hIH
    rw [pullbackWeightedSymTensorIso_succ_hom]
    show (Functor.LaxMonoidal.ε (Modules.pullback g) ≫
        (Modules.pullback g).map ((λ_ (𝟙_ X.Modules)).inv ≫
          ((Modules.symGradedAlgebra (W 0)).one ⊗ₘ weightedSymTensorOne r (Fin.tail W)))) ≫
        ((Functor.Monoidal.μIso (Modules.pullback g) ((Modules.symGradedAlgebra (W 0)).part 0)
            (weightedSymTensor r (Fin.tail W) 0)).inv ≫
          ((GradedQCAlgebra.pullbackIsoApp g (ψ 0) 0).hom ⊗ₘ
            (pullbackWeightedSymTensorIso g r (Fin.tail W) (Fin.tail W') (fun q => ψ q.succ) 0).hom)) =
      (λ_ (𝟙_ X'.Modules)).inv ≫
        ((Modules.symGradedAlgebra (W' 0)).one ⊗ₘ weightedSymTensorOne r (Fin.tail W'))
    simp only [Functor.Monoidal.μIso_inv]
    rw [(Modules.pullback g).map_comp, Functor.Monoidal.map_leftUnitor_inv]
    simp only [Category.assoc]
    rw [← Functor.LaxMonoidal.μ_natural_assoc, Functor.Monoidal.μ_δ_assoc, tensorHom_comp_tensorHom,
      leftUnitor_inv_naturality_assoc, ← tensorHom_def'_assoc, tensorHom_comp_tensorHom, hψ, hIH]

namespace weightedSymAlgebra

variable {r : ℕ} (V : Fin r → X.Modules) (V' : Fin r → X'.Modules)
  (ψ : ∀ q, (Modules.symGradedAlgebra (Modules.dual (V q))).pullback g ≅
    Modules.symGradedAlgebra (Modules.dual (V' q)))

/-- Step 3: `g^*(part V m) ≅ part V' m` (pullback preserves finite biproducts, then termwise). -/
def pullbackPartIso (m : ℕ) : (Modules.pullback g).obj (part V m) ≅ part V' m :=
  (Modules.pullback g).mapBiproduct (fun d : weightedSymIndex r m => term V d) ≪≫
    biproduct.mapIso fun d : weightedSymIndex r m =>
      pullbackWeightedSymTensorIso g r (gen V) (gen V') ψ (fun q => (d.1 q : ℕ))

theorem pullbackPartIso_hom (m : ℕ) :
    (pullbackPartIso g V V' ψ m).hom =
      ((Modules.pullback g).mapBiproduct (fun d : weightedSymIndex r m => term V d)).hom ≫
        biproduct.map fun d : weightedSymIndex r m =>
          (pullbackWeightedSymTensorIso g r (gen V) (gen V') ψ (fun q => (d.1 q : ℕ))).hom := by
  rw [pullbackPartIso, Iso.trans_hom, biproduct.mapIso_hom]

theorem map_π_pullbackPartIso {m : ℕ} (d : weightedSymIndex r m) :
    (Modules.pullback g).map (biproduct.π (fun d => term V d) d) ≫
        (pullbackWeightedSymTensorIso g r (gen V) (gen V') ψ (fun q => (d.1 q : ℕ))).hom =
      (pullbackPartIso g V V' ψ m).hom ≫ biproduct.π (fun d => term V' d) d := by
  rw [pullbackPartIso_hom, Category.assoc, biproduct.map_π, ← Category.assoc,
    wsaPullback_mapBiproduct_hom_π]

theorem map_ι_pullbackPartIso {m : ℕ} (d : weightedSymIndex r m) :
    (Modules.pullback g).map (biproduct.ι (fun d => term V d) d) ≫ (pullbackPartIso g V V' ψ m).hom =
      (pullbackWeightedSymTensorIso g r (gen V) (gen V') ψ (fun q => (d.1 q : ℕ))).hom ≫
        biproduct.ι (fun d => term V' d) d := by
  rw [pullbackPartIso_hom, ← Category.assoc, wsaPullback_map_ι_mapBiproduct_hom, biproduct.ι_map]

/-- Step 4: compatibility with the multiplication. -/
theorem pullbackMulHom_iso (m n : ℕ) :
    (Functor.LaxMonoidal.μ (Modules.pullback g) (part V m) (part V n) ≫
        (Modules.pullback g).map (mulHom V m n)) ≫ (pullbackPartIso g V V' ψ (m + n)).hom =
      ((pullbackPartIso g V V' ψ m).hom ⊗ₘ (pullbackPartIso g V V' ψ n).hom) ≫ mulHom V' m n := by
  have : (Modules.pullback g).Additive :=
    (Modules.pullbackPushforwardAdjunction g).left_adjoint_additive
  simp only [mulHom, CategoryTheory.Functor.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact wsaPullback_aux_summand (Modules.pullback g) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (map_π_pullbackPartIso g V V' ψ p.1) (map_π_pullbackPartIso g V V' ψ p.2)
    (pullbackWeightedSymTensorMul_iso g r (gen V) (gen V') ψ (fun q => (p.1.1 q : ℕ))
      (fun q => (p.2.1 q : ℕ)))
    (map_ι_pullbackPartIso g V V' ψ (p.1.add p.2))

/-- Step 4: compatibility with the unit. -/
theorem pullbackOneHom_iso :
    (Functor.LaxMonoidal.ε (Modules.pullback g) ≫ (Modules.pullback g).map (oneHom V)) ≫
        (pullbackPartIso g V V' ψ 0).hom = oneHom V' :=
  wsaPullback_aux_one (Modules.pullback g) _ _ _ _ _ _
    (map_ι_pullbackPartIso g V V' ψ (⟨0, by simp⟩ : weightedSymIndex r 0))
    (pullbackWeightedSymTensorOne_iso g r (gen V) (gen V') ψ)

end weightedSymAlgebra

/-- The graded-algebra iso `g^*(weightedSymAlgebra V) ≅ weightedSymAlgebra V'` assembled from a family of
graded-algebra isos `ψ_q : (Sym V_q^∨).pullback g ≅ Sym V'_q^∨`. -/
def weightedSymAlgebraPullbackIso {r : ℕ} (V : Fin r → X.Modules) (V' : Fin r → X'.Modules)
    [∀ q, (V q).IsLocallyFree] [∀ q, (V q).IsFiniteType]
    [∀ q, (V' q).IsLocallyFree] [∀ q, (V' q).IsFiniteType]
    (ψ : ∀ q, (Modules.symGradedAlgebra (Modules.dual (V q))).pullback g ≅
      Modules.symGradedAlgebra (Modules.dual (V' q))) :
    (weightedSymAlgebra V).pullback g ≅ weightedSymAlgebra V' :=
  GradedQCAlgebra.isoMk (fun m => weightedSymAlgebra.pullbackPartIso g V V' ψ m)
    (weightedSymAlgebra.pullbackMulHom_iso g V V' ψ) (weightedSymAlgebra.pullbackOneHom_iso g V V' ψ)

end AlgebraicGeometry.Scheme

/-- **Weighted Sym commutes with pullback.** See the module docstring for the route; the proof is
`weightedSymAlgebraPullbackIso` applied to `ψ_q := (Sym commutes with pullback, Stacks 01CI) ≪≫
Sym(dual commutes with pullback, `Modules.dual_pullback`)`. -/
theorem AlgebraicGeometry.Scheme.weightedSymAlgebra_pullback
    {X X' : AlgebraicGeometry.Scheme.{u}} {r : ℕ} (V : Fin r → X.Modules)
    [∀ q, (V q).IsLocallyFree] [∀ q, (V q).IsFiniteType] (g : X' ⟶ X) :
    haveI := fun q => (AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback g (V q)).1
    haveI := fun q => AlgebraicGeometry.Scheme.Modules.isFiniteType_pullback g (V q)
    Nonempty ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).pullback g ≅
      AlgebraicGeometry.Scheme.weightedSymAlgebra
        (fun q => (AlgebraicGeometry.Scheme.Modules.pullback g).obj (V q))) := by
  have := fun q => (AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback g (V q)).1
  have := fun q => AlgebraicGeometry.Scheme.Modules.isFiniteType_pullback g (V q)
  refine ⟨AlgebraicGeometry.Scheme.weightedSymAlgebraPullbackIso g V _ fun q => ?_⟩
  haveI : (AlgebraicGeometry.Scheme.Modules.dual (V q)).IsLocallyFree :=
    AlgebraicGeometry.Scheme.Modules.isLocallyFree_dual' (V q)
  haveI : (AlgebraicGeometry.Scheme.Modules.dual (V q)).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocallyFree _
  exact (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_pullback g
      (AlgebraicGeometry.Scheme.Modules.dual (V q))).some ≪≫
    AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_congr
      (AlgebraicGeometry.Scheme.Modules.dual_pullback g (V q)).some.symm

end
