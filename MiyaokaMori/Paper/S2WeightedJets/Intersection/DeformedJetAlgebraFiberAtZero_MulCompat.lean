import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraFiberAtZero_PartIso

/-! # The fibre `T = s₀^*R` at `λ = 0` on generators, and the multiplicativity of `ε_j = partIsoGr S j`

Write `F := s₀^*` (`s₀ = sectionAt X 0`), `P := π^*` (`π = toBase X`), `η := pullbackToBaseCompPullbackSectionAtIso 0 :
P ⋙ F ≅ 𝟭`, `R := S.reesDeformation` (pieces `R_j = Im (gen S j) ⊆ π^*S_j`), `T := R.restrictToLambda 0 = R.pullback s₀`
(pieces `T_j = F(R_j)`, multiplication `μ_F ≫ F(R.mul)`), and `ε_j := partIsoGr S j : T_j ≅ ⊕_{p ≤ j} I^{(p)}_j/I^{(p+1)}_j`.
This module provides, for `p ≤ j`:

* §A `ε_j` **on the generators of `R_j`** (`map_ι_factorThruImage_gen_comp_partIsoGr_hom`): unwinding the five factors of
  `partIsoGr`, `F(ι_e ≫ factorThruImage (gen S j)) ≫ ε_j = η_{I^{(j-e)}_j} ≫ cokernel.π (stepHom (j-e) j) ≫ ι_{p = j-e}`.
* §B **`η` is monoidal** (`tensorHom_inv_app_comp_μ_comp_map_μ`): `(η⁻¹_A ⊗ η⁻¹_B) ≫ μ_F ≫ F(μ_P) = η⁻¹_{A⊗B}`, from
  `μ_pullbackComp_hom`, the transport along `s₀ ≫ π = 𝟙` and `μ_pullbackId`.
* §C the **Rees generators** `reesGen S j p := λ^{j-p}·π^*(I^{(p)}_j) ⟶ R_j` (the slot `e = j - p` of `gen S j`, indexed by
  `p`), and their multiplicativity (`tensor_reesGen_comp_mulHom`): `(g_{j,p} ⊗ g_{j',p'}) ≫ R.mul = μ_P ≫ π^*m ≫ g_{j+j',p+p'}`
  for any lift `m : I^{(p)}_j ⊗ I^{(p')}_{j'} ⟶ I^{(p+p')}_{j+j'}` of `(incl ⊗ incl) ≫ S.mul` (e.g. `irrelevantPowMul`) —
  `λ^{j-p}·λ^{j'-p'} = λ^{(j+j')-(p+p')}`.
* §D the **fibre generators** `fiberGen S j p := η⁻¹ ≫ F(g_{j,p}) : I^{(p)}_j ⟶ T_j`, with
  `fiberGen_comp_partIsoGr'_hom : fiberGen S j p ≫ ε_j = cokernel.π (stepHom p j) ≫ ι_p` (so `fiberGen` is
  `cokernel.π ≫ grSummandIncl`, `π_comp_ι_comp_partIsoGr'_inv`) and `tensor_fiberGen_comp_μ_comp_map_mulHom :
  (fiberGen j p ⊗ fiberGen j' p') ≫ T.mul = m ≫ fiberGen (j+j') (p+p')`. These two identities give
  `tensor_π_comp_tensor_ι_partIsoGr'_inv_comp_mul_π_same` / `tensor_ι_partIsoGr'_inv_comp_mul_π_ne`, which are
  `grSummandIncl_tensor_comp_mul_π_same` / `_ne` of `DeformedJetAlgebraFiberAtZero_Generators` up to definitional
  unfolding (the statement "`s₀^*R ≅ gr_{S_+}(S)` as graded algebras", Stacks 052P).

**Spelling convention.** `T_j = (S.reesDeformation.restrictToLambda 0).part j` unfolds to `F(reesDeformation.part S j)` and
`T.mul j j'` to `μ_F ≫ F(mulHom S j j')`, but only up to unfolding `restrictToLambda`/`GradedQCAlgebra.pullback`/
`reesDeformation` (not at reducible transparency). Every statement in this module is written in the unfolded ("image")
spelling — `partIsoGr'` is `partIsoGr` with that source — because a `rw` chain mixing the two spellings fails on its
implicit arguments; the bridge to the `T` spelling is a single `exact` in `DeformedJetAlgebraFiberAtZero_Generators`.

Source: Stacks 052P; Lemma 2.3 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- `μ` is compatible with the transport `eqToHom (congrArg pullback h)` along an equality of morphisms. -/
theorem μ_comp_eqToHom_congrArg_pullback_app {X Y : AlgebraicGeometry.Scheme.{u}} {f f' : X ⟶ Y} (h : f = f')
    (A B : Y.Modules) :
    CategoryTheory.Functor.LaxMonoidal.μ (pullback f) A B ≫ (eqToHom (congrArg Modules.pullback h)).app (A ⊗ B) =
      ((eqToHom (congrArg Modules.pullback h)).app A ⊗ₘ (eqToHom (congrArg Modules.pullback h)).app B) ≫
        CategoryTheory.Functor.LaxMonoidal.μ (pullback f') A B := by
  subst h
  simp only [eqToHom_refl, NatTrans.id_app, Category.comp_id, CategoryTheory.MonoidalCategory.id_tensorHom_id,
    Category.id_comp]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

namespace reesDeformation

variable {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]

/-! ## §A `partIsoGr` on the generators of `R_j` -/

theorem π_comp_cokernelMapSyzygyIsoCokernelMapKernelι_inv (j : ℕ) :
    CategoryTheory.Limits.cokernel.π
        ((Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (CategoryTheory.Limits.kernel.ι (gen S j))) ≫
      (cokernelMapSyzygyIsoCokernelMapKernelι S j).inv =
    CategoryTheory.Limits.cokernel.π ((Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (syzygy S j)) :=
  CategoryTheory.Limits.cokernel.π_desc _ _ _

theorem π_comp_cokernelPullbackSyzygyIso_hom (j : ℕ) :
    CategoryTheory.Limits.cokernel.π ((Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (syzygy S j)) ≫
      (cokernelPullbackSyzygyIso S j).hom =
    (pullbackSectionAtBiproductIso (X := X) (0 : k) (fun e : Fin (j + 1) => (S.irrelevantPow (j - e.1) j).1)).hom ≫
      CategoryTheory.Limits.cokernel.π
        (CategoryTheory.Limits.biproduct.map fun e : Fin (j + 1) => irrelevantPow.stepHom S (j - e.1) j) := by
  unfold cokernelPullbackSyzygyIso
  rw [CategoryTheory.Limits.cokernel.mapIso_hom]
  exact CategoryTheory.Limits.cokernel.π_desc _ _ _

@[reassoc]
theorem ι_comp_biproductCokernelStepHomReindexIso_hom (j : ℕ) (e : Fin (j + 1)) :
    CategoryTheory.Limits.biproduct.ι
        (fun e : Fin (j + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S (j - e.1) j)) e ≫
      (biproductCokernelStepHomReindexIso S j).hom =
    eqToHom (congrArg (fun m => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S m j))
        (show j - e.1 = (Fin.rev e).1 by rw [Fin.val_rev]; omega)) ≫
      CategoryTheory.Limits.biproduct.ι
        (fun p : Fin (j + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p.1 j)) (Fin.rev e) := by
  unfold biproductCokernelStepHomReindexIso
  rw [Iso.trans_hom, ← Category.assoc, CategoryTheory.Limits.biproduct.mapIso_hom,
    CategoryTheory.Limits.biproduct.ι_map, Category.assoc, CategoryTheory.Limits.biproduct.reindex_hom,
    CategoryTheory.Limits.biproduct.ι_desc, eqToIso.hom]
  rfl

@[reassoc]
theorem π_comp_cokernelBiproductMapIso_hom (j : ℕ) :
    CategoryTheory.Limits.cokernel.π (CategoryTheory.Limits.biproduct.map fun e : Fin (j + 1) => irrelevantPow.stepHom S (j - e.1) j) ≫
      (CategoryTheory.Limits.cokernelBiproductMapIso fun e : Fin (j + 1) => irrelevantPow.stepHom S (j - e.1) j).hom =
    CategoryTheory.Limits.biproduct.map fun e : Fin (j + 1) =>
      CategoryTheory.Limits.cokernel.π (irrelevantPow.stepHom S (j - e.1) j) :=
  CategoryTheory.Limits.cokernel.π_desc _ _ _

/-- **`partIsoGr` in the "image" spelling**: the same five factors as `partIsoGr S j`, but with source written as
`s₀^*(Im (gen S j))` (= `s₀^*(reesDeformation.part S j)`) instead of `(S.reesDeformation.restrictToLambda 0).part j`.
The two are definitionally equal (`partIsoGr_eq_partIsoGr'`); all rewriting in this module is done in this spelling
(mixing the two spellings inside one `rw` chain fails at reducible transparency), and the two spellings are
bridged only at the top level by `exact`. -/
noncomputable def partIsoGr' (j : ℕ) :
    (Modules.pullback (affineLineOver.sectionAt X (0 : k))).obj (part S j) ≅
      ⨁ (fun p : Fin (j + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p.1 j)) :=
  pullbackSectionAtZeroPartIsoCokernel S j ≪≫
    (cokernelMapSyzygyIsoCokernelMapKernelι S j).symm ≪≫
    cokernelPullbackSyzygyIso S j ≪≫
    CategoryTheory.Limits.cokernelBiproductMapIso _ ≪≫
    biproductCokernelStepHomReindexIso S j

theorem partIsoGr_eq_partIsoGr' (j : ℕ) : partIsoGr S (k := k) j = partIsoGr' S (k := k) j := rfl

/-- The five factors of `partIsoGr'` (definitional). -/
theorem partIsoGr'_hom (j : ℕ) :
    (partIsoGr' S (k := k) j).hom =
      (pullbackSectionAtZeroPartIsoCokernel S j).hom ≫ (cokernelMapSyzygyIsoCokernelMapKernelι S j).inv ≫
        (cokernelPullbackSyzygyIso S j).hom ≫
        (CategoryTheory.Limits.cokernelBiproductMapIso fun e : Fin (j + 1) => irrelevantPow.stepHom S (j - e.1) j).hom ≫
        (biproductCokernelStepHomReindexIso S j).hom := rfl

/-- **`ε_j` on the `e`-th generator**: `F(ι_e ≫ factorThruImage (gen S j)) ≫ (partIsoGr' S j).hom` is `η.hom.app` followed by the
class map `cokernel.π (stepHom (j-e) j)` into the summand `p = j - e` (written `Fin.rev e`, with the index transport). -/
theorem map_ι_factorThruImage_gen_comp_partIsoGr_hom (j : ℕ) (e : Fin (j + 1)) :
    (Modules.pullback (affineLineOver.sectionAt X (0 : k))).map
        (CategoryTheory.Limits.biproduct.ι
          (fun e : Fin (j + 1) => (Modules.pullback (affineLineOver.toBase X)).obj (S.irrelevantPow (j - e.1) j).1) e ≫
          CategoryTheory.Limits.factorThruImage (gen S j)) ≫ (partIsoGr' S (k := k) j).hom =
      (pullbackToBaseCompPullbackSectionAtIso (X := X) (0 : k)).hom.app (S.irrelevantPow (j - e.1) j).1 ≫
        CategoryTheory.Limits.cokernel.π (irrelevantPow.stepHom S (j - e.1) j) ≫
        eqToHom (congrArg (fun m => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S m j))
          (show j - e.1 = (Fin.rev e).1 by rw [Fin.val_rev]; omega)) ≫
        CategoryTheory.Limits.biproduct.ι
          (fun p : Fin (j + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p.1 j)) (Fin.rev e) := by
  have := pullbackSectionAt_additive (X := X) (0 : k)
  rw [partIsoGr'_hom, Functor.map_comp, Category.assoc,
    ← Category.assoc ((Modules.pullback (affineLineOver.sectionAt X (0 : k))).map
      (CategoryTheory.Limits.factorThruImage (gen S j))),
    map_factorThruImage_gen_comp_pullbackSectionAtZeroPartIsoCokernel_hom,
    ← Category.assoc (CategoryTheory.Limits.cokernel.π _), π_comp_cokernelMapSyzygyIsoCokernelMapKernelι_inv,
    ← Category.assoc (CategoryTheory.Limits.cokernel.π _), π_comp_cokernelPullbackSyzygyIso_hom]
  simp only [Category.assoc]
  rw [reassoc_of% (map_ι_comp_pullbackSectionAtBiproductIso_hom (X := X) (0 : k)
      (fun e : Fin (j + 1) => (S.irrelevantPow (j - e.1) j).1) e),
    π_comp_cokernelBiproductMapIso_hom_assoc, CategoryTheory.Limits.biproduct.ι_map_assoc,
    ι_comp_biproductCokernelStepHomReindexIso_hom]


/-! ## §B `η = pullbackToBaseCompPullbackSectionAtIso t` is monoidal -/

/-- The three factors of `pullbackToBaseCompPullbackSectionAtIso` on an object (definitional). -/
theorem pullbackToBaseCompPullbackSectionAtIso_hom_app (t : k)
    (hsπ : affineLineOver.sectionAt X t ≫ affineLineOver.toBase X = 𝟙 X) (A : X.Modules) :
    (pullbackToBaseCompPullbackSectionAtIso (X := X) t).hom.app A =
      (Modules.pullbackComp (affineLineOver.sectionAt X t) (affineLineOver.toBase X)).hom.app A ≫
        (eqToHom (congrArg Modules.pullback hsπ)).app A ≫ (Modules.pullbackId X).hom.app A := rfl

/-- **`η = pullbackToBaseCompPullbackSectionAtIso t` is monoidal** (hom form): `μ_{s_t^*} ≫ s_t^*(μ_{π^*}) ≫ η_{A⊗B} =
η_A ⊗ η_B` (`μ_pullbackComp_hom`, transport along `s_t ≫ π = 𝟙`, `μ_pullbackId`). -/
theorem μ_comp_map_μ_comp_pullbackToBaseCompPullbackSectionAtIso_hom_app (t : k) (A B : X.Modules) :
    CategoryTheory.Functor.LaxMonoidal.μ (Modules.pullback (affineLineOver.sectionAt X t))
        ((Modules.pullback (affineLineOver.toBase X)).obj A) ((Modules.pullback (affineLineOver.toBase X)).obj B) ≫
      (Modules.pullback (affineLineOver.sectionAt X t)).map
        (CategoryTheory.Functor.LaxMonoidal.μ (Modules.pullback (affineLineOver.toBase X)) A B) ≫
      (pullbackToBaseCompPullbackSectionAtIso (X := X) t).hom.app (A ⊗ B) =
    ((pullbackToBaseCompPullbackSectionAtIso (X := X) t).hom.app A ⊗ₘ
      (pullbackToBaseCompPullbackSectionAtIso (X := X) t).hom.app B) := by
  have hsπ : affineLineOver.sectionAt X t ≫ affineLineOver.toBase X = 𝟙 X :=
    AlgebraicGeometry.AffineSpace.homOfVector_over _ _
  rw [pullbackToBaseCompPullbackSectionAtIso_hom_app t hsπ, pullbackToBaseCompPullbackSectionAtIso_hom_app t hsπ,
    pullbackToBaseCompPullbackSectionAtIso_hom_app t hsπ,
    reassoc_of% (Modules.μ_pullbackComp_hom (affineLineOver.sectionAt X t) (affineLineOver.toBase X) A B),
    reassoc_of% (Modules.μ_comp_eqToHom_congrArg_pullback_app hsπ A B), Modules.μ_pullbackId,
    CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom]

/-- **`η` is monoidal** (inv form): `(η⁻¹_A ⊗ η⁻¹_B) ≫ μ_{s_t^*} ≫ s_t^*(μ_{π^*}) = η⁻¹_{A⊗B}`. -/
@[reassoc]
theorem tensorHom_inv_app_comp_μ_comp_map_μ (t : k) (A B : X.Modules) :
    ((pullbackToBaseCompPullbackSectionAtIso (X := X) t).inv.app A ⊗ₘ
        (pullbackToBaseCompPullbackSectionAtIso (X := X) t).inv.app B) ≫
      CategoryTheory.Functor.LaxMonoidal.μ (Modules.pullback (affineLineOver.sectionAt X t))
        ((Modules.pullback (affineLineOver.toBase X)).obj A) ((Modules.pullback (affineLineOver.toBase X)).obj B) ≫
      (Modules.pullback (affineLineOver.sectionAt X t)).map
        (CategoryTheory.Functor.LaxMonoidal.μ (Modules.pullback (affineLineOver.toBase X)) A B) =
    (pullbackToBaseCompPullbackSectionAtIso (X := X) t).inv.app (A ⊗ B) := by
  rw [← cancel_mono ((pullbackToBaseCompPullbackSectionAtIso (X := X) t).hom.app (A ⊗ B)), Iso.inv_hom_id_app,
    Category.assoc, Category.assoc, μ_comp_map_μ_comp_pullbackToBaseCompPullbackSectionAtIso_hom_app,
    CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, Iso.inv_hom_id_app, Iso.inv_hom_id_app,
    CategoryTheory.MonoidalCategory.id_tensorHom_id]
  rfl

/-- Naturality of `η⁻¹`: `η⁻¹_A ≫ s_t^*(π^* f) = f ≫ η⁻¹_B`. -/
@[reassoc]
theorem inv_app_comp_map_map (t : k) {A B : X.Modules} (f : A ⟶ B) :
    (pullbackToBaseCompPullbackSectionAtIso (X := X) t).inv.app A ≫
        (Modules.pullback (affineLineOver.sectionAt X t)).map ((Modules.pullback (affineLineOver.toBase X)).map f) =
      f ≫ (pullbackToBaseCompPullbackSectionAtIso (X := X) t).inv.app B :=
  ((pullbackToBaseCompPullbackSectionAtIso (X := X) t).inv.naturality f).symm


/-! ## §C The Rees generators `λ^{j-p}·π^*(I^{(p)}_j) ⟶ R_j` and their products -/

/-- `λ^{j-p} · π^*(I^{(p)}_j → S_j)` lands in the Rees piece `R_j` (`landsInPart_of_landsIn`). -/
theorem landsInPart_pullMap_irrelevantPow_mulCoordPow (j : ℕ) (p : Fin (j + 1)) :
    LandsInPart S (pullMap S (S.irrelevantPow p.1 j).2 ≫
      affineLineOver.mulCoordPow (j - p.1) ((S.pullback (affineLineOver.toBase X)).part j)) :=
  landsInPart_of_landsIn S _ p.1 (by omega) (S.landsIn_self p.1 j)

/-- **The `p`-th Rees generator** `λ^{j-p} · π^*(I^{(p)}_j) ⟶ R_j` (the `e = j - p` slot of `gen S j`, indexed by `p`). -/
noncomputable def reesGen (j : ℕ) (p : Fin (j + 1)) :
    (Modules.pullback (affineLineOver.toBase X)).obj (S.irrelevantPow p.1 j).1 ⟶ part S j :=
  CategoryTheory.Abelian.monoLift (incl S j) _ (landsInPart_pullMap_irrelevantPow_mulCoordPow S j p)

@[reassoc]
theorem reesGen_comp_incl (j : ℕ) (p : Fin (j + 1)) :
    reesGen S j p ≫ incl S j =
      pullMap S (S.irrelevantPow p.1 j).2 ≫
        affineLineOver.mulCoordPow (j - p.1) ((S.pullback (affineLineOver.toBase X)).part j) :=
  CategoryTheory.Abelian.monoLift_comp _ _ _

/-- The slot `e` of `gen S j` is the Rees generator of index `p = j - e = Fin.rev e` (up to the index transport on the
source). -/
theorem eqToHom_comp_reesGen_rev (j : ℕ) (e : Fin (j + 1)) :
    eqToHom (congrArg (fun m => (Modules.pullback (affineLineOver.toBase X)).obj (S.irrelevantPow m j).1)
        (show j - e.1 = (Fin.rev e).1 by rw [Fin.val_rev]; omega)) ≫ reesGen S j (Fin.rev e) =
      CategoryTheory.Limits.biproduct.ι
          (fun e : Fin (j + 1) => (Modules.pullback (affineLineOver.toBase X)).obj (S.irrelevantPow (j - e.1) j).1) e ≫
        CategoryTheory.Limits.factorThruImage (gen S j) := by
  have hje : j - e.1 = (Fin.rev e).1 := by rw [Fin.val_rev]; omega
  apply (cancel_mono (incl S j)).1
  rw [Category.assoc, reesGen_comp_incl, ← Category.assoc, eqToHom_comp_pullMap_irrelevantPow_snd S j hje,
    Category.assoc, CategoryTheory.Limits.image.fac, ι_gen, show j - (Fin.rev e).1 = e.1 by rw [Fin.val_rev]; omega]

/-- **The Rees generators multiply through `S.mul`**: for `m : I^{(p)}_j ⊗ I^{(p')}_{j'} ⟶ I^{(p+p')}_{j+j'}` lifting
`(incl ⊗ incl) ≫ S.mul` (e.g. `irrelevantPowMul`), `(g_{j,p} ⊗ g_{j',p'}) ≫ R.mul = μ_{π^*} ≫ π^*m ≫ g_{j+j',p+p'}`
(`λ^{j-p}·λ^{j'-p'} = λ^{(j+j')-(p+p')}`; `tensor_mulCoordPow_comp_mul`, `tensor_pullMap_comp_mul`). -/
theorem tensor_reesGen_comp_mulHom (j j' : ℕ) (p : Fin (j + 1)) (p' : Fin (j' + 1))
    (m : (S.irrelevantPow p.1 j).1 ⊗ (S.irrelevantPow p'.1 j').1 ⟶ (S.irrelevantPow (p.1 + p'.1) (j + j')).1)
    (hm : m ≫ (S.irrelevantPow (p.1 + p'.1) (j + j')).2 =
      ((S.irrelevantPow p.1 j).2 ⊗ₘ (S.irrelevantPow p'.1 j').2) ≫ S.mul j j') :
    (reesGen S j p ⊗ₘ reesGen S j' p') ≫ mulHom S j j' =
      CategoryTheory.Functor.LaxMonoidal.μ (Modules.pullback (affineLineOver.toBase X)) _ _ ≫
        (Modules.pullback (affineLineOver.toBase X)).map m ≫ reesGen S (j + j') ⟨p.1 + p'.1, by omega⟩ := by
  apply (cancel_mono (incl S (j + j'))).1
  unfold mulHom
  have hmap : pullMap S (m ≫ (S.irrelevantPow (p.1 + p'.1) (j + j')).2) =
      (Modules.pullback (affineLineOver.toBase X)).map m ≫ pullMap S (S.irrelevantPow (p.1 + p'.1) (j + j')).2 :=
    Functor.map_comp _ _ _
  rw [Category.assoc, CategoryTheory.Abelian.monoLift_comp, ← Category.assoc,
    CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, reesGen_comp_incl, reesGen_comp_incl,
    tensor_mulCoordPow_comp_mul, tensor_pullMap_comp_mul_assoc, ← hm, hmap, Category.assoc, Category.assoc,
    Category.assoc, reesGen_comp_incl, show (j - p.1) + (j' - p'.1) = (j + j') - (p.1 + p'.1) by omega]


/-! ## §D The fibre generators and the multiplicativity of `ε` -/

/-- **The `p`-th fibre generator** `I^{(p)}_j ⟶ s₀^*(R_j)`: `η⁻¹` followed by `s₀^*` of the Rees generator
`λ^{j-p}·π^*(I^{(p)}_j) ⟶ R_j`. Under `ε_j` it is the class map into the `p`-th summand (`fiberGen_comp_partIsoGr'_hom`);
it equals `cokernel.π (stepHom p j) ≫ grSummandIncl S j p` (`π_comp_grSummandIncl`, `…_Generators.lean`). The codomain is
written `s₀^*(reesDeformation.part S j)` ("image" spelling, see `partIsoGr'`). -/
noncomputable def fiberGen (j : ℕ) (p : Fin (j + 1)) :
    (S.irrelevantPow p.1 j).1 ⟶ (Modules.pullback (affineLineOver.sectionAt X (0 : k))).obj (part S j) :=
  (pullbackToBaseCompPullbackSectionAtIso (X := X) (0 : k)).inv.app (S.irrelevantPow p.1 j).1 ≫
    (Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (reesGen S j p)

/-- `η⁻¹_A ≫ eqToHom ≫ η_B = eqToHom` for `A = B`. -/
@[reassoc]
theorem inv_app_comp_eqToHom_comp_hom_app (t : k) {A B : X.Modules} (hAB : A = B)
    (h : (Modules.pullback (affineLineOver.sectionAt X t)).obj ((Modules.pullback (affineLineOver.toBase X)).obj A) =
      (Modules.pullback (affineLineOver.sectionAt X t)).obj ((Modules.pullback (affineLineOver.toBase X)).obj B)) :
    (pullbackToBaseCompPullbackSectionAtIso (X := X) t).inv.app A ≫ eqToHom h ≫
        (pullbackToBaseCompPullbackSectionAtIso (X := X) t).hom.app B = eqToHom hAB := by
  subst hAB
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Iso.inv_hom_id_app]
  rfl

/-- `fiberGen_comp_partIsoGr'_hom` for the index `p = Fin.rev e` (this is where the slot `e` of `gen S j` is compared with
the summand `p = j - e`). -/
theorem fiberGen_rev_comp_partIsoGr'_hom (j : ℕ) (e : Fin (j + 1)) :
    fiberGen S j (Fin.rev e) ≫ (partIsoGr' S (k := k) j).hom =
      CategoryTheory.Limits.cokernel.π (irrelevantPow.stepHom S (Fin.rev e).1 j) ≫
        CategoryTheory.Limits.biproduct.ι
          (fun p : Fin (j + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p.1 j)) (Fin.rev e) := by
  have hje : j - e.1 = (Fin.rev e).1 := by rw [Fin.val_rev]; omega
  have h1 : reesGen S j (Fin.rev e) =
      eqToHom (congrArg (fun m => (Modules.pullback (affineLineOver.toBase X)).obj (S.irrelevantPow m j).1) hje.symm) ≫
        (CategoryTheory.Limits.biproduct.ι
          (fun e : Fin (j + 1) => (Modules.pullback (affineLineOver.toBase X)).obj (S.irrelevantPow (j - e.1) j).1) e ≫
        CategoryTheory.Limits.factorThruImage (gen S j)) := by
    rw [← eqToHom_comp_reesGen_rev S j e, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  have h2 := eqToHom_naturality (fun m => CategoryTheory.Limits.cokernel.π (irrelevantPow.stepHom S m j)) hje
  unfold fiberGen
  rw [h1, Functor.map_comp, Category.assoc, Category.assoc, map_ι_factorThruImage_gen_comp_partIsoGr_hom,
    eqToHom_map,
    inv_app_comp_eqToHom_comp_hom_app_assoc (X := X) (0 : k) (congrArg (fun m => (S.irrelevantPow m j).1) hje.symm),
    reassoc_of% h2, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- **`ε_j` on the fibre generators**: `fiberGen S j p ≫ ε_j = cokernel.π (stepHom p j) ≫ ι_p` — the class of
`λ^{j-p}·π^*x` (`x ∈ I^{(p)}_j`) in `T_j` is the class of `x` in the summand `I^{(p)}_j/I^{(p+1)}_j`. -/
@[reassoc]
theorem fiberGen_comp_partIsoGr'_hom (j : ℕ) (p : Fin (j + 1)) :
    fiberGen S j p ≫ (partIsoGr' S (k := k) j).hom =
      CategoryTheory.Limits.cokernel.π (irrelevantPow.stepHom S p.1 j) ≫
        CategoryTheory.Limits.biproduct.ι
          (fun p : Fin (j + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p.1 j)) p := by
  obtain ⟨e, rfl⟩ : ∃ e, p = Fin.rev e := ⟨Fin.rev p, (Fin.rev_rev p).symm⟩
  exact fiberGen_rev_comp_partIsoGr'_hom S j e

/-- `cokernel.π (stepHom p j) ≫ ι_p ≫ ε_j⁻¹ = fiberGen S j p` (the image-spelled form of `π_comp_grSummandIncl`). -/
theorem π_comp_ι_comp_partIsoGr'_inv (j : ℕ) (p : Fin (j + 1)) :
    CategoryTheory.Limits.cokernel.π (irrelevantPow.stepHom S p.1 j) ≫
        CategoryTheory.Limits.biproduct.ι
          (fun p : Fin (j + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p.1 j)) p ≫
        (partIsoGr' S (k := k) j).inv =
      fiberGen S j p := by
  rw [← Category.assoc, ← fiberGen_comp_partIsoGr'_hom S (k := k) j p, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- **The fibre generators multiply through `S.mul`**: for a lift `m` of `(incl ⊗ incl) ≫ S.mul` to
`I^{(p)}_j ⊗ I^{(p')}_{j'} ⟶ I^{(p+p')}_{j+j'}`, `(fiberGen j p ⊗ fiberGen j' p') ≫ T.mul j j' = m ≫ fiberGen (j+j') (p+p')`,
where `T.mul j j' = μ_{s₀^*} ≫ s₀^*(R.mul)` is written out (`μ_natural`, `tensor_reesGen_comp_mulHom`, the monoidality and
naturality of `η`). -/
theorem tensor_fiberGen_comp_μ_comp_map_mulHom (j j' : ℕ) (p : Fin (j + 1)) (p' : Fin (j' + 1))
    (m : (S.irrelevantPow p.1 j).1 ⊗ (S.irrelevantPow p'.1 j').1 ⟶ (S.irrelevantPow (p.1 + p'.1) (j + j')).1)
    (hm : m ≫ (S.irrelevantPow (p.1 + p'.1) (j + j')).2 =
      ((S.irrelevantPow p.1 j).2 ⊗ₘ (S.irrelevantPow p'.1 j').2) ≫ S.mul j j') :
    (fiberGen S j p ⊗ₘ fiberGen S j' p') ≫
        CategoryTheory.Functor.LaxMonoidal.μ (Modules.pullback (affineLineOver.sectionAt X (0 : k))) (part S j) (part S j') ≫
        (Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (mulHom S j j') =
      m ≫ fiberGen S (j + j') ⟨p.1 + p'.1, by omega⟩ := by
  unfold fiberGen
  rw [← CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc,
    CategoryTheory.Functor.LaxMonoidal.μ_natural_assoc, ← Functor.map_comp,
    tensor_reesGen_comp_mulHom S j j' p p' m hm, Functor.map_comp, Functor.map_comp,
    tensorHom_inv_app_comp_μ_comp_map_μ_assoc, inv_app_comp_map_map_assoc]

/-- **(c3-M, diagonal component), image spelling**: the statement of `grSummandIncl_tensor_comp_mul_π_same` with
`grSummandIncl` written as `ι_p ≫ ε⁻¹`, `T.mul` as `μ ≫ s₀^*(R.mul)` and `ε = partIsoGr'`; the main-tree statement is this one
up to definitional unfolding (`exact`). -/
theorem tensor_π_comp_tensor_ι_partIsoGr'_inv_comp_mul_π_same (j j' : ℕ) (p : Fin (j + 1)) (p' : Fin (j' + 1))
    (m : (S.irrelevantPow p.1 j).1 ⊗ (S.irrelevantPow p'.1 j').1 ⟶ (S.irrelevantPow (p.1 + p'.1) (j + j')).1)
    (hm : m ≫ (S.irrelevantPow (p.1 + p'.1) (j + j')).2 =
      ((S.irrelevantPow p.1 j).2 ⊗ₘ (S.irrelevantPow p'.1 j').2) ≫ S.mul j j') :
    (CategoryTheory.Limits.cokernel.π (irrelevantPow.stepHom S p.1 j) ⊗ₘ
        CategoryTheory.Limits.cokernel.π (irrelevantPow.stepHom S p'.1 j')) ≫
      ((CategoryTheory.Limits.biproduct.ι
          (fun p : Fin (j + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p.1 j)) p ≫
          (partIsoGr' S (k := k) j).inv) ⊗ₘ
        (CategoryTheory.Limits.biproduct.ι
          (fun p : Fin (j' + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p.1 j')) p' ≫
          (partIsoGr' S (k := k) j').inv)) ≫
      (CategoryTheory.Functor.LaxMonoidal.μ (Modules.pullback (affineLineOver.sectionAt X (0 : k))) (part S j) (part S j') ≫
        (Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (mulHom S j j')) ≫
      (partIsoGr' S (k := k) (j + j')).hom ≫
      CategoryTheory.Limits.biproduct.π
        (fun p'' : Fin (j + j' + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p''.1 (j + j')))
        ⟨p.1 + p'.1, by omega⟩ =
    m ≫ CategoryTheory.Limits.cokernel.π (irrelevantPow.stepHom S (p.1 + p'.1) (j + j')) := by
  rw [← Category.assoc, CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, π_comp_ι_comp_partIsoGr'_inv,
    π_comp_ι_comp_partIsoGr'_inv, ← Category.assoc, tensor_fiberGen_comp_μ_comp_map_mulHom S j j' p p' m hm,
    Category.assoc, fiberGen_comp_partIsoGr'_hom_assoc, CategoryTheory.Limits.biproduct.ι_π_self, Category.comp_id]

/-- **(c3-M, off-diagonal components), image spelling** (cf. `grSummandIncl_tensor_comp_mul_π_ne`). -/
theorem tensor_ι_partIsoGr'_inv_comp_mul_π_ne (j j' : ℕ) (p : Fin (j + 1)) (p' : Fin (j' + 1))
    (m : (S.irrelevantPow p.1 j).1 ⊗ (S.irrelevantPow p'.1 j').1 ⟶ (S.irrelevantPow (p.1 + p'.1) (j + j')).1)
    (hm : m ≫ (S.irrelevantPow (p.1 + p'.1) (j + j')).2 =
      ((S.irrelevantPow p.1 j).2 ⊗ₘ (S.irrelevantPow p'.1 j').2) ≫ S.mul j j')
    (p'' : Fin (j + j' + 1)) (h : p''.1 ≠ p.1 + p'.1) :
    ((CategoryTheory.Limits.biproduct.ι
          (fun p : Fin (j + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p.1 j)) p ≫
          (partIsoGr' S (k := k) j).inv) ⊗ₘ
        (CategoryTheory.Limits.biproduct.ι
          (fun p : Fin (j' + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p.1 j')) p' ≫
          (partIsoGr' S (k := k) j').inv)) ≫
      (CategoryTheory.Functor.LaxMonoidal.μ (Modules.pullback (affineLineOver.sectionAt X (0 : k))) (part S j) (part S j') ≫
        (Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (mulHom S j j')) ≫
      (partIsoGr' S (k := k) (j + j')).hom ≫
      CategoryTheory.Limits.biproduct.π
        (fun p'' : Fin (j + j' + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p''.1 (j + j'))) p'' = 0 := by
  have : Epi (CategoryTheory.Limits.cokernel.π (irrelevantPow.stepHom S p.1 j) ⊗ₘ
      CategoryTheory.Limits.cokernel.π (irrelevantPow.stepHom S p'.1 j')) :=
    AlgebraicGeometry.Scheme.Modules.epi_tensorHom _ _ inferInstance inferInstance
  rw [← cancel_epi (CategoryTheory.Limits.cokernel.π (irrelevantPow.stepHom S p.1 j) ⊗ₘ
      CategoryTheory.Limits.cokernel.π (irrelevantPow.stepHom S p'.1 j')), comp_zero, ← Category.assoc,
    CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, π_comp_ι_comp_partIsoGr'_inv,
    π_comp_ι_comp_partIsoGr'_inv, ← Category.assoc, tensor_fiberGen_comp_μ_comp_map_mulHom S j j' p p' m hm,
    Category.assoc, fiberGen_comp_partIsoGr'_hom_assoc,
    CategoryTheory.Limits.biproduct.ι_π_ne _ (fun h' => h (congrArg Fin.val h').symm), comp_zero, comp_zero]

end reesDeformation

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
