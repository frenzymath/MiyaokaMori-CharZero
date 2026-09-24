import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Proj.GradedQCAlgebraIsoMk
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymGradedAlgebraCongr

/-! # The symmetric algebra commutes with pullback (Stacks 01CI)

Stacks 01CI: the symmetric algebra commutes with pullback, `f^*Sym(F) ≅ Sym(f^*F)` (likewise for the
tensor and exterior algebras).

## Route

Write `F := pullback f` (a strong braided monoidal functor, `pullbackMonoidal`, and a left adjoint,
`pullbackPushforwardAdjunction`).
1. `pullbackMonoidalPowIso f W m : F(W^{⊗m}) ≅ (F W)^{⊗m}` by recursion on `m`: `m = 0` is
   `pullbackUnitIso` (= `η`), `m + 1` is `μ⁻¹ = δ` followed by whiskering.
2. It commutes with the adjacent transpositions (`pullback_map_monoidalPowTransp_iso`; the same
   recursion as `monoidalPowTransp`, using that `δ` is natural, associative and braided) and with the
   concatenation isomorphisms (`pullback_map_monoidalPowCat_iso`; recursion on `n`, using
   `map_rightUnitor` and `map_associator_inv`).
3. `Sym^m W` is the wide coequalizer of the transpositions. `F(Sym^m W) ⟶ Sym^m(F W)` is obtained
   through the adjunction `F ⊣ f_*`: the invariant map `F(W^{⊗m}) ⟶ (F W)^{⊗m} ⟶ Sym^m (F W)` transposes
   to an invariant map `W^{⊗m} ⟶ f_* Sym^m(F W)`, which descends along `symPowπ` and transposes back.
   The inverse descends `(F W)^{⊗m} ≅ F(W^{⊗m}) ⟶ F(Sym^m W)` along `symPowπ`. Both composites are the
   identity because `F(symPowπ)` (a left adjoint preserves epimorphisms) and `symPowπ` are epimorphisms.
4. Compatibility with the multiplication is checked after precomposing with the epimorphism
   `F π_m ⊗ F π_n`, where both sides become `(ê_m ⊗ ê_n) ≫ cat ≫ π` by `tensorHom_symPowπ_symPowMul`
   and step 2; compatibility with the unit is `ε = pullbackUnitIso.inv`. `GradedQCAlgebra.isoMk`
   assembles the graded algebra isomorphism; the `dite` in `symGradedAlgebra` is resolved with
   `symGradedAlgebra_eq_ofQC` on both sides (`f^*F` is quasi-coherent by `isQuasicoherent_pullback`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-! ## Generic lemmas on (braided) monoidal functors -/

section MonoidalAux

open CategoryTheory.MonoidalCategory CategoryTheory.Functor.OplaxMonoidal CategoryTheory.Functor.LaxMonoidal
  CategoryTheory.Functor.Monoidal

variable {C : Type u'} [Category.{v'} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type w} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]

/-- Naturality of the adjacent transposition `α ≫ (P ◁ β) ≫ α⁻¹` (braiding and associator naturality). -/
private theorem transpAux_naturality {P P' V W : C} (a : P ⟶ P') (g : V ⟶ W) :
    ((α_ P V V).hom ≫ P ◁ (β_ V V).hom ≫ (α_ P V V).inv) ≫ ((a ⊗ₘ g) ⊗ₘ g) =
      ((a ⊗ₘ g) ⊗ₘ g) ≫ (α_ P' W W).hom ≫ P' ◁ (β_ W W).hom ≫ (α_ P' W W).inv := by
  have h : P ◁ (β_ V V).hom ≫ (a ⊗ₘ (g ⊗ₘ g)) = (a ⊗ₘ (g ⊗ₘ g)) ≫ P' ◁ (β_ W W).hom := by
    rw [tensorHom_def', ← whiskerLeft_comp_assoc, ← BraidedCategory.braiding_naturality,
      whiskerLeft_comp_assoc, whisker_exchange, Category.assoc]
  simp only [Category.assoc]
  rw [← associator_inv_naturality, reassoc_of% h, associator_naturality_assoc]

omit [BraidedCategory C] [BraidedCategory D] in
/-- `δ` is natural: `F(t ▷ V) ≫ δ ≫ c ▷ FV = (δ ≫ c ▷ FV) ≫ t' ▷ FV` when `F t ≫ c = c ≫ t'`. -/
private theorem map_whiskerRight_δ_comm (F : C ⥤ D) [F.OplaxMonoidal] {P V : C} {Q : D}
    (c : F.obj P ⟶ Q) (t : P ⟶ P) (t' : Q ⟶ Q) (h : F.map t ≫ c = c ≫ t') :
    F.map (t ▷ V) ≫ δ F P V ≫ c ▷ F.obj V = (δ F P V ≫ c ▷ F.obj V) ≫ t' ▷ F.obj V := by
  rw [← δ_natural_left_assoc, ← comp_whiskerRight, h, comp_whiskerRight, Category.assoc]

/-- `δ` commutes with the adjacent transposition (associativity, naturality and braiding of `δ`). -/
private theorem map_transpAux_δ_comm (F : C ⥤ D) [F.Braided] {P V : C} {Q : D} (c : F.obj P ⟶ Q) :
    F.map ((α_ P V V).hom ≫ P ◁ (β_ V V).hom ≫ (α_ P V V).inv) ≫
        δ F (P ⊗ V) V ≫ (δ F P V ≫ c ▷ F.obj V) ▷ F.obj V =
      (δ F (P ⊗ V) V ≫ (δ F P V ≫ c ▷ F.obj V) ▷ F.obj V) ≫
        (α_ Q (F.obj V) (F.obj V)).hom ≫ Q ◁ (β_ (F.obj V) (F.obj V)).hom ≫
          (α_ Q (F.obj V) (F.obj V)).inv := by
  have hb : F.map (β_ V V).hom ≫ δ F V V = δ F V V ≫ (β_ (F.obj V) (F.obj V)).hom := by
    rw [F.map_braiding, Category.assoc, Category.assoc, μ_δ, Category.comp_id]
  have h1' := transpAux_naturality c (𝟙 (F.obj V))
  simp only [tensorHom_id, Category.assoc] at h1'
  simp only [F.map_comp, Category.assoc, comp_whiskerRight]
  rw [← Functor.OplaxMonoidal.associativity_inv_assoc, ← δ_natural_right_assoc, ← whiskerLeft_comp_assoc, hb,
    whiskerLeft_comp_assoc, ← Functor.OplaxMonoidal.associativity_assoc, h1']

omit [BraidedCategory C] [BraidedCategory D] in
/-- The `n = 0` step of the concatenation compatibility: `F(ρ_P) ≫ a = δ ≫ (a ⊗ u) ≫ ρ_{P'}` for `u = η`. -/
private theorem map_rightUnitor_δ_comm (F : C ⥤ D) [F.Monoidal] {P : C} {P' : D} (a : F.obj P ⟶ P')
    (u : F.obj (𝟙_ C) ⟶ 𝟙_ D) (hu : u = η F) :
    F.map (ρ_ P).hom ≫ a = δ F P (𝟙_ C) ≫ (a ⊗ₘ u) ≫ (ρ_ P').hom := by
  rw [hu, map_rightUnitor, tensorHom_def']
  simp only [Category.assoc]
  rw [rightUnitor_naturality]

omit [BraidedCategory C] [BraidedCategory D] in
/-- The `n + 1` step of the concatenation compatibility. -/
private theorem map_cat_succ_δ_comm (F : C ⥤ D) [F.Monoidal] {P Q W S : C} {P' Q' S' : D}
    (a : F.obj P ⟶ P') (b : F.obj Q ⟶ Q') (c : F.obj S ⟶ S')
    (k : P ⊗ Q ⟶ S) (k' : P' ⊗ Q' ⟶ S')
    (ih : F.map k ≫ c = δ F P Q ≫ (a ⊗ₘ b) ≫ k') :
    F.map ((α_ P Q W).inv ≫ k ▷ W) ≫ δ F S W ≫ c ▷ F.obj W =
      δ F P (Q ⊗ W) ≫ (a ⊗ₘ (δ F Q W ≫ b ▷ F.obj W)) ≫ (α_ P' Q' (F.obj W)).inv ≫ k' ▷ F.obj W := by
  have h1 : (a ⊗ₘ (δ F Q W ≫ b ▷ F.obj W)) =
      (F.obj P ◁ δ F Q W) ≫ (a ⊗ₘ (b ⊗ₘ 𝟙 (F.obj W))) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, tensorHom_id]
  rw [F.map_comp, Category.assoc, ← δ_natural_left_assoc, ← comp_whiskerRight, ih, map_associator_inv, h1]
  simp only [Category.assoc, comp_whiskerRight, μ_δ_assoc, whiskerRight_μ_δ_assoc]
  rw [associator_inv_naturality_assoc, tensorHom_id]

end MonoidalAux

/-! ## Pullback of tensor powers -/

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.MonoidalCategory

variable {X Y : AlgebraicGeometry.Scheme.{u}}

/-- `f^*(W^{⊗m}) ≅ (f^*W)^{⊗m}`: `m = 0` is `f^*O_Y ≅ O_X` (`pullbackUnitIso`), `m + 1` is
`f^*(A ⊗ B) ≅ f^*A ⊗ f^*B` (`pullbackTensorObjIso`, Stacks 01CD) followed by whiskering. Its `hom` is
definitionally the comparison map `pullbackMonoidalPow` of `ProjectiveBundleUniversalProperty.lean`. -/
noncomputable def pullbackMonoidalPowIso (f : X ⟶ Y) (W : Y.Modules) : (m : ℕ) →
    ((pullback f).obj (monoidalPow W m) ≅ monoidalPow ((pullback f).obj W) m)
  | 0 => pullbackUnitIso f
  | m + 1 => pullbackTensorObjIso f (monoidalPow W m) W ≪≫
      whiskerRightIso (pullbackMonoidalPowIso f W m) ((pullback f).obj W)

/-- The pullback comparison commutes with the adjacent transpositions
(`δ` is natural, associative and compatible with the braiding). -/
theorem pullback_map_monoidalPowTransp_iso (f : X ⟶ Y) (W : Y.Modules) : ∀ (m i : ℕ),
    (pullback f).map (monoidalPowTransp W m i) ≫ (pullbackMonoidalPowIso f W m).hom =
      (pullbackMonoidalPowIso f W m).hom ≫ monoidalPowTransp ((pullback f).obj W) m i
  | 0, 0 =>
    ((congrArg (· ≫ _) ((pullback f).map_id _)).trans (Category.id_comp _)).trans
      (Category.comp_id _).symm
  | 0, _ + 1 =>
    ((congrArg (· ≫ _) ((pullback f).map_id _)).trans (Category.id_comp _)).trans
      (Category.comp_id _).symm
  | 1, 0 =>
    ((congrArg (· ≫ _) ((pullback f).map_id _)).trans (Category.id_comp _)).trans
      (Category.comp_id _).symm
  | n + 2, 0 => map_transpAux_δ_comm (pullback f) (pullbackMonoidalPowIso f W n).hom
  | 0 + 1, i + 1 => map_whiskerRight_δ_comm (pullback f) (pullbackMonoidalPowIso f W 0).hom _ _
      (pullback_map_monoidalPowTransp_iso f W 0 i)
  | (n + 1) + 1, i + 1 => map_whiskerRight_δ_comm (pullback f) (pullbackMonoidalPowIso f W (n + 1)).hom _ _
      (pullback_map_monoidalPowTransp_iso f W (n + 1) i)

/-- The pullback comparison commutes with the concatenation isomorphisms `W^{⊗m} ⊗ W^{⊗n} ≅ W^{⊗(m+n)}`. -/
theorem pullback_map_monoidalPowCat_iso (f : X ⟶ Y) (W : Y.Modules) (m : ℕ) : ∀ n : ℕ,
    (pullback f).map (monoidalPowCat W m n).hom ≫ (pullbackMonoidalPowIso f W (m + n)).hom =
      (pullbackTensorObjIso f (monoidalPow W m) (monoidalPow W n)).hom ≫
        ((pullbackMonoidalPowIso f W m).hom ⊗ₘ (pullbackMonoidalPowIso f W n).hom) ≫
        (monoidalPowCat ((pullback f).obj W) m n).hom
  | 0 => map_rightUnitor_δ_comm (pullback f) (pullbackMonoidalPowIso f W m).hom _ (pullback_η f).symm
  | n + 1 => map_cat_succ_δ_comm (pullback f) _ _ _ _ _ (pullback_map_monoidalPowCat_iso f W m n)

/-! ## Pullback of symmetric powers -/

/-- The map `f^*(W^{⊗m}) ≅ (f^*W)^{⊗m} ⟶ Sym^m(f^*W)` is invariant under the transpositions. -/
theorem pullback_map_monoidalPowTransp_symPowπ (f : X ⟶ Y) (W : Y.Modules) (m : ℕ) (i : Fin m) :
    (pullback f).map (monoidalPowTransp W m i) ≫
        ((pullbackMonoidalPowIso f W m).hom ≫ symPowπ ((pullback f).obj W) m) =
      (pullbackMonoidalPowIso f W m).hom ≫ symPowπ ((pullback f).obj W) m := by
  rw [← Category.assoc, pullback_map_monoidalPowTransp_iso, Category.assoc,
    monoidalPowTransp_symPowπ _ m i i.isLt]

/-- `f^*(Sym^m W) ⟶ Sym^m(f^*W)`, through the adjunction `f^* ⊣ f_*` and descent along `symPowπ`. -/
noncomputable def pullbackSymPowHom (f : X ⟶ Y) (W : Y.Modules) (m : ℕ) :
    (pullback f).obj (symPow W m) ⟶ symPow ((pullback f).obj W) m :=
  ((pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (symPowDesc W m
      ((pullbackPushforwardAdjunction f).homEquiv _ _
        ((pullbackMonoidalPowIso f W m).hom ≫ symPowπ ((pullback f).obj W) m))
      (fun i => by
        rw [← Adjunction.homEquiv_naturality_left, pullback_map_monoidalPowTransp_symPowπ]))

theorem pullback_map_symPowπ_pullbackSymPowHom (f : X ⟶ Y) (W : Y.Modules) (m : ℕ) :
    (pullback f).map (symPowπ W m) ≫ pullbackSymPowHom f W m =
      (pullbackMonoidalPowIso f W m).hom ≫ symPowπ ((pullback f).obj W) m := by
  apply ((pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, pullbackSymPowHom, Equiv.apply_symm_apply, symPowπ_desc]

/-- `Sym^m(f^*W) ⟶ f^*(Sym^m W)`, descending `(f^*W)^{⊗m} ≅ f^*(W^{⊗m}) ⟶ f^*(Sym^m W)`. -/
noncomputable def pullbackSymPowInv (f : X ⟶ Y) (W : Y.Modules) (m : ℕ) :
    symPow ((pullback f).obj W) m ⟶ (pullback f).obj (symPow W m) :=
  symPowDesc _ m ((pullbackMonoidalPowIso f W m).inv ≫ (pullback f).map (symPowπ W m))
    (fun i => by
      have h' : monoidalPowTransp ((pullback f).obj W) m i ≫ (pullbackMonoidalPowIso f W m).inv =
          (pullbackMonoidalPowIso f W m).inv ≫ (pullback f).map (monoidalPowTransp W m i) := by
        rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
        exact (pullback_map_monoidalPowTransp_iso f W m i).symm
      rw [← Category.assoc, h', Category.assoc, ← Functor.map_comp,
        monoidalPowTransp_symPowπ W m i i.isLt])

theorem symPowπ_pullbackSymPowInv (f : X ⟶ Y) (W : Y.Modules) (m : ℕ) :
    symPowπ ((pullback f).obj W) m ≫ pullbackSymPowInv f W m =
      (pullbackMonoidalPowIso f W m).inv ≫ (pullback f).map (symPowπ W m) :=
  symPowπ_desc _ _ _ _

/-- `f^*(Sym^m W) ≅ Sym^m(f^*W)` (Stacks 01CI, degree `m` piece). -/
noncomputable def pullbackSymPowIso (f : X ⟶ Y) (W : Y.Modules) (m : ℕ) :
    (pullback f).obj (symPow W m) ≅ symPow ((pullback f).obj W) m where
  hom := pullbackSymPowHom f W m
  inv := pullbackSymPowInv f W m
  hom_inv_id := by
    have : Epi ((pullback f).map (symPowπ W m)) := inferInstance
    rw [← cancel_epi ((pullback f).map (symPowπ W m)), ← Category.assoc,
      pullback_map_symPowπ_pullbackSymPowHom, Category.assoc, symPowπ_pullbackSymPowInv,
      Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := by
    rw [← cancel_epi (symPowπ ((pullback f).obj W) m), ← Category.assoc,
      symPowπ_pullbackSymPowInv, Category.assoc, pullback_map_symPowπ_pullbackSymPowHom,
      Iso.inv_hom_id_assoc, Category.comp_id]

theorem pullback_map_symPowπ_pullbackSymPowIso_hom (f : X ⟶ Y) (W : Y.Modules) (m : ℕ) :
    (pullback f).map (symPowπ W m) ≫ (pullbackSymPowIso f W m).hom =
      (pullbackMonoidalPowIso f W m).hom ≫ symPowπ ((pullback f).obj W) m :=
  pullback_map_symPowπ_pullbackSymPowHom f W m

/-! ## Compatibility with the graded algebra structure -/

/-- Compatibility with the multiplication, checked after the epimorphism `f^*π_m ⊗ f^*π_n`. -/
theorem symGradedAlgebraOfQC_pullback_map_mul (f : X ⟶ Y) (F : Y.Modules) (hF : F.IsQuasicoherent)
    (m n : ℕ) :
    ((symGradedAlgebraOfQC F hF).pullback f).mul m n ≫ (pullbackSymPowIso f F (m + n)).hom =
      ((pullbackSymPowIso f F m).hom ⊗ₘ (pullbackSymPowIso f F n).hom) ≫
        symPowMul ((pullback f).obj F) m n := by
  change (Functor.LaxMonoidal.μ (pullback f) (symPow F m) (symPow F n) ≫
      (pullback f).map (symPowMul F m n)) ≫ _ = _
  have : Epi ((pullback f).map (symPowπ F m)) := inferInstance
  have : Epi ((pullback f).map (symPowπ F n)) := inferInstance
  have := epi_tensorHom_of_epi ((pullback f).map (symPowπ F m)) ((pullback f).map (symPowπ F n))
  -- `μ = (pullbackTensorObjIso f _ _).inv` definitionally (`pullback_μ_eq`)
  have hμδ : Functor.LaxMonoidal.μ (pullback f) (monoidalPow F m) (monoidalPow F n) ≫
      (pullbackTensorObjIso f (monoidalPow F m) (monoidalPow F n)).hom = 𝟙 _ :=
    Iso.inv_hom_id _
  rw [← cancel_epi ((pullback f).map (symPowπ F m) ⊗ₘ (pullback f).map (symPowπ F n))]
  simp only [Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_assoc, ← Functor.map_comp_assoc, tensorHom_symPowπ_symPowMul,
    Functor.map_comp_assoc, pullback_map_symPowπ_pullbackSymPowIso_hom,
    reassoc_of% (pullback_map_monoidalPowCat_iso f F m n), reassoc_of% hμδ,
    tensorHom_comp_tensorHom_assoc, pullback_map_symPowπ_pullbackSymPowIso_hom,
    pullback_map_symPowπ_pullbackSymPowIso_hom, ← tensorHom_comp_tensorHom_assoc,
    tensorHom_symPowπ_symPowMul]

/-- Compatibility with the unit: `ε ≫ f^*π_0 ≫ ê_0 ≫ π'_0 = π'_0` since `ε = pullbackUnitIso.inv`. -/
theorem symGradedAlgebraOfQC_pullback_map_one (f : X ⟶ Y) (F : Y.Modules) (hF : F.IsQuasicoherent) :
    ((symGradedAlgebraOfQC F hF).pullback f).one ≫ (pullbackSymPowIso f F 0).hom =
      symPowπ ((pullback f).obj F) 0 := by
  -- the goal is not type-correct at implicit transparency (`symPowπ F 0 : monoidalPow F 0 ⟶ _` sits
  -- under a `𝟙_ Y.Modules` domain), so we compose closed equalities instead of rewriting
  have hε : Functor.LaxMonoidal.ε (pullback f) ≫ (pullbackMonoidalPowIso f F 0).hom = 𝟙 _ :=
    (congrArg (· ≫ (pullbackMonoidalPowIso f F 0).hom) (pullback_ε_eq f)).trans
      (Iso.inv_hom_id (pullbackUnitIso f))
  change (Functor.LaxMonoidal.ε (pullback f) ≫ (pullback f).map (symPowπ F 0)) ≫
    (pullbackSymPowIso f F 0).hom = _
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => Functor.LaxMonoidal.ε (pullback f) ≫ t)
    (pullback_map_symPowπ_pullbackSymPowIso_hom f F 0)).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ symPowπ ((pullback f).obj F) 0) hε).trans (Category.id_comp _))

/-- Quasi-coherent case of Stacks 01CI as an explicit isomorphism of graded algebras. -/
noncomputable def symGradedAlgebraOfQC_pullbackIso (f : X ⟶ Y) (F : Y.Modules) (hF : F.IsQuasicoherent)
    (hF' : ((pullback f).obj F).IsQuasicoherent) :
    (symGradedAlgebraOfQC F hF).pullback f ≅ symGradedAlgebraOfQC ((pullback f).obj F) hF' :=
  GradedQCAlgebra.isoMk (fun m => pullbackSymPowIso f F m)
    (symGradedAlgebraOfQC_pullback_map_mul f F hF) (symGradedAlgebraOfQC_pullback_map_one f F hF)

end AlgebraicGeometry.Scheme.Modules

theorem AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_pullback {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (F : Y.Modules) [F.IsQuasicoherent] :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra F).pullback f ≅
      AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj F)) :=
  ⟨eqToIso (congrArg (fun S : Y.GradedQCAlgebra => S.pullback f)
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_eq_ofQC F inferInstance)) ≪≫
    AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC_pullbackIso f F inferInstance inferInstance ≪≫
    eqToIso (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_eq_ofQC
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj F) inferInstance).symm⟩

end
