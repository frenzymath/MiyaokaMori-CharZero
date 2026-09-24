import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackCompMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQcAlgebraCategory
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal

/-! # Pullback of graded quasi-coherent algebras

The pullback of a graded quasi-coherent algebra along a morphism: pull back each graded piece;
multiplication and unit are transported through the monoidal structure of the pullback functor.
Needed for the base change of the relative Proj (Stacks 01O3).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem gradedQCAlgebraHom_ext {X : AlgebraicGeometry.Scheme.{u}}
    {S T : X.GradedQCAlgebra} (φ ψ : AlgebraicGeometry.Scheme.GradedQCAlgebra.Hom S T)
    (h : ∀ m, φ.app m = ψ.app m) : φ = ψ := by
  cases φ with
  | mk φ hmul hone =>
    cases ψ with
    | mk ψ hmul' hone' =>
      simp only at h
      cases funext h
      rfl

/-- The pullback `S.pullback g` of a graded quasi-coherent algebra `S` on `Y` along `g : X ⟶ Y`. -/
noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.pullback {X Y : AlgebraicGeometry.Scheme.{u}}
    (S : Y.GradedQCAlgebra) (g : X ⟶ Y) : X.GradedQCAlgebra where
  part m := (AlgebraicGeometry.Scheme.Modules.pullback g).obj (S.part m)
  quasicoherent m := haveI := S.quasicoherent m; inferInstance
  -- `μ`, `ε` come from the braided (hence lax monoidal) structure of `pullback g`
  mul m n := CategoryTheory.Functor.LaxMonoidal.μ (AlgebraicGeometry.Scheme.Modules.pullback g) (S.part m) (S.part n) ≫
    (AlgebraicGeometry.Scheme.Modules.pullback g).map (S.mul m n)
  one := CategoryTheory.Functor.LaxMonoidal.ε (AlgebraicGeometry.Scheme.Modules.pullback g) ≫
    (AlgebraicGeometry.Scheme.Modules.pullback g).map S.one
  one_mul := by
    intro m
    simp only [Category.assoc, CategoryTheory.MonoidalCategory.comp_whiskerRight,
      CategoryTheory.Functor.LaxMonoidal.μ_natural_left_assoc,
      CategoryTheory.Functor.LaxMonoidal.left_unitality]
    rw [← (AlgebraicGeometry.Scheme.Modules.pullback g).map_comp]
    rw [S.one_mul]
    simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.comp_id, Category.id_comp]
  mul_assoc := by
    intro m n p
    simp only [CategoryTheory.MonoidalCategory.whiskerLeft_comp,
      CategoryTheory.MonoidalCategory.comp_whiskerRight, Category.assoc]
    simp only [CategoryTheory.Functor.LaxMonoidal.μ_natural_right_assoc,
      CategoryTheory.Functor.LaxMonoidal.μ_natural_left_assoc]
    rw [← CategoryTheory.Functor.LaxMonoidal.associativity_assoc
      (F := AlgebraicGeometry.Scheme.Modules.pullback g) (S.part m) (S.part n) (S.part p)]
    simp only [← (AlgebraicGeometry.Scheme.Modules.pullback g).map_comp, Category.assoc]
    rw [S.mul_assoc]
    simp only [Functor.map_comp, eqToHom_map, eqToHom_trans_assoc, eqToHom_refl,
      Category.comp_id, Category.id_comp]
  mul_comm := by
    intro m n
    simp only [Category.assoc]
    rw [← CategoryTheory.Functor.LaxBraided.braided_assoc
      (F := AlgebraicGeometry.Scheme.Modules.pullback g) (S.part m) (S.part n)]
    simp only [← (AlgebraicGeometry.Scheme.Modules.pullback g).map_comp, Category.assoc]
    rw [S.mul_comm]
    simp only [Functor.map_comp, eqToHom_map, eqToHom_trans_assoc, eqToHom_refl,
      Category.comp_id, Category.id_comp]

/-- Pullback along a composite is the iterated pullback (as graded algebras): on each piece take the
inverse of the component of Mathlib's `Scheme.Modules.pullbackComp f g`, `(f ≫ g)^* S_m ≅ f^* g^* S_m`;
compatibility with multiplication and unit holds because `pullbackComp` is a monoidal natural
isomorphism. -/

noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.pullbackComp {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (S : Z.GradedQCAlgebra) (f : X ⟶ Y) (g : Y ⟶ Z) :
    S.pullback (f ≫ g) ≅ (S.pullback g).pullback f where
  hom := (⟨fun m => ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).app (S.part m)).inv, by
      intro m n
      dsimp [AlgebraicGeometry.Scheme.GradedQCAlgebra.pullback]
      simp [Category.assoc]
      -- `μ` is compatible with `pullbackComp`
      have h := AlgebraicGeometry.Scheme.Modules.μ_pullbackComp_inv f g (S.part m) (S.part n)
      rw [reassoc_of% h]
    , by
      dsimp [AlgebraicGeometry.Scheme.GradedQCAlgebra.pullback]
      have hn := (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.naturality S.one
      have h := AlgebraicGeometry.Scheme.Modules.ε_pullbackComp_inv f g
      dsimp at hn
      rw [Category.assoc, hn, reassoc_of% h, Functor.map_comp]⟩ :
    AlgebraicGeometry.Scheme.GradedQCAlgebra.Hom _ _)
  inv := (⟨fun m => ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).app (S.part m)).hom, by
      intro m n
      dsimp [AlgebraicGeometry.Scheme.GradedQCAlgebra.pullback]
      simp [Category.assoc]
      have h := AlgebraicGeometry.Scheme.Modules.μ_pullbackComp_hom f g (S.part m) (S.part n)
      rw [← reassoc_of% h]
      have hn := (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.naturality (S.mul m n)
      dsimp at hn
      rw [hn]
    , by
      dsimp [AlgebraicGeometry.Scheme.GradedQCAlgebra.pullback]
      have hn := (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.naturality S.one
      have h := AlgebraicGeometry.Scheme.Modules.ε_pullbackComp_hom f g
      dsimp at hn
      rw [← h]
      simp only [Functor.map_comp, Category.assoc, hn]⟩ :
    AlgebraicGeometry.Scheme.GradedQCAlgebra.Hom _ _)
  hom_inv_id := by
    apply gradedQCAlgebraHom_ext
    intro m
    exact CategoryTheory.Iso.inv_hom_id_app (AlgebraicGeometry.Scheme.Modules.pullbackComp f g)
      (S.part m)
  inv_hom_id := by
    apply gradedQCAlgebraHom_ext
    intro m
    exact CategoryTheory.Iso.hom_inv_id_app (AlgebraicGeometry.Scheme.Modules.pullbackComp f g)
      (S.part m)

/-- Pullback preserves isomorphisms of graded algebras: take `g^*(e.hom.app m)`, `g^*(e.inv.app m)` on each
piece; compatibility with multiplication is the naturality of `μ`. -/

noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.pullbackMapIso {X Y : AlgebraicGeometry.Scheme.{u}}
    {S T : Y.GradedQCAlgebra} (e : S ≅ T) (g : X ⟶ Y) : S.pullback g ≅ T.pullback g where
  hom := (⟨fun m => (AlgebraicGeometry.Scheme.Modules.pullback g).map (e.hom.app m), by
      intro m n
      dsimp [AlgebraicGeometry.Scheme.GradedQCAlgebra.pullback]
      simp only [Category.assoc, ← (AlgebraicGeometry.Scheme.Modules.pullback g).map_comp]
      rw [e.hom.map_mul]
      simp only [Functor.map_comp]
      have hμ := CategoryTheory.Functor.LaxMonoidal.μ_natural_assoc
        (AlgebraicGeometry.Scheme.Modules.pullback g) (e.hom.app m) (e.hom.app n)
        ((AlgebraicGeometry.Scheme.Modules.pullback g).map (T.mul m n))
      rw [← hμ]
    , by
      dsimp [AlgebraicGeometry.Scheme.GradedQCAlgebra.pullback]
      simp only [Category.assoc, ← (AlgebraicGeometry.Scheme.Modules.pullback g).map_comp]
      rw [e.hom.map_one]
    ⟩ :
    AlgebraicGeometry.Scheme.GradedQCAlgebra.Hom _ _)
  inv := (⟨fun m => (AlgebraicGeometry.Scheme.Modules.pullback g).map (e.inv.app m), by
      intro m n
      dsimp [AlgebraicGeometry.Scheme.GradedQCAlgebra.pullback]
      simp only [Category.assoc, ← (AlgebraicGeometry.Scheme.Modules.pullback g).map_comp]
      rw [e.inv.map_mul]
      simp only [Functor.map_comp]
      have hμ := CategoryTheory.Functor.LaxMonoidal.μ_natural_assoc
        (AlgebraicGeometry.Scheme.Modules.pullback g) (e.inv.app m) (e.inv.app n)
        ((AlgebraicGeometry.Scheme.Modules.pullback g).map (S.mul m n))
      rw [← hμ]
    , by
      dsimp [AlgebraicGeometry.Scheme.GradedQCAlgebra.pullback]
      simp only [Category.assoc, ← (AlgebraicGeometry.Scheme.Modules.pullback g).map_comp]
      rw [e.inv.map_one]
    ⟩ :
    AlgebraicGeometry.Scheme.GradedQCAlgebra.Hom _ _)
  hom_inv_id := by
    apply gradedQCAlgebraHom_ext
    intro m
    change (AlgebraicGeometry.Scheme.Modules.pullback g).map (e.hom.app m) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback g).map (e.inv.app m) = 𝟙 _
    rw [← (AlgebraicGeometry.Scheme.Modules.pullback g).map_comp]
    have h := congrArg (fun q : AlgebraicGeometry.Scheme.GradedQCAlgebra.Hom S S => q.app m)
      e.hom_inv_id
    change e.hom.app m ≫ e.inv.app m = 𝟙 _ at h
    rw [h]
    simp
  inv_hom_id := by
    apply gradedQCAlgebraHom_ext
    intro m
    change (AlgebraicGeometry.Scheme.Modules.pullback g).map (e.inv.app m) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback g).map (e.hom.app m) = 𝟙 _
    rw [← (AlgebraicGeometry.Scheme.Modules.pullback g).map_comp]
    have h := congrArg (fun q : AlgebraicGeometry.Scheme.GradedQCAlgebra.Hom T T => q.app m)
      e.inv_hom_id
    change e.inv.app m ≫ e.hom.app m = 𝟙 _ at h
    rw [h]
    simp

end
