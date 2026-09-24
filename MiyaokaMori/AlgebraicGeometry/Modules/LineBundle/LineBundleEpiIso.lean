import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentStalkFinite
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleLocalIso

/-! # An epimorphism between line bundles is an isomorphism

An epimorphism between line bundles is an isomorphism: on stalks, `L_x ≅ O_{X,x} ≅ M_x`, and a surjection
`O_{X,x} → O_{X,x}` is multiplication by a unit (the image contains `1`, which generates), hence injective on
stalks; a morphism of sheaves that is an isomorphism on stalks is an isomorphism.

Reference: standard (a special case of Stacks 05B3: a surjective endomorphism of a finitely generated module
is an isomorphism).

Route (which does not need to identify the stalk of `O_X` with `O_{X,x}` itself):
1. Being an isomorphism is a local property (`moduleHom_isIso_of_locally_isIso`): for every point `x` take
   trivializing opens `U = U₁ ⊓ U₂ ∋ x` of `M` and `N` (`Trivialization.shrink`); it suffices that `φ|_U` is
   an isomorphism.
2. The restriction functor is a left adjoint (`restrictAdjunction`), hence preserves epimorphisms; let
   `e : N|_U ≅ M|_U` be the composite of the two trivializations, so `φ|_U ≫ e.hom` is a surjective
   endomorphism of `M|_U`.
3. Stalkwise criterion (`moduleHom_isIso_iff_stalk_bijective`): the stalk map of `φ|_U ≫ e.hom` at each
   point `y` is a surjective `O_{U,y}`-linear endomorphism of `(M|_U)_y` (`FreeStalk.stalkMap_surjective_of_epi`);
   `M|_U` is a line bundle hence of finite type, so its stalks are finitely generated modules
   (`finite_stalk_of_isFiniteType`); commutative rings have the Orzech property
   (`CommRing.orzechProperty`), and a surjective endomorphism of a finitely generated module is bijective
   (`OrzechProperty.bijective_of_surjective_endomorphism`).
4. `φ|_U ≫ e.hom` and `e.hom` are isomorphisms, so `φ|_U` is an isomorphism (`IsIso.of_isIso_comp_right`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem SheafOfModules.IsLineBundle.isIso_of_epi {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules}
    [M.IsLineBundle] [N.IsLineBundle] (φ : M ⟶ N) [CategoryTheory.Epi φ] : CategoryTheory.IsIso φ := by
  apply AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_of_locally_isIso
  intro x
  obtain ⟨t₁, hx₁⟩ := AlgebraicGeometry.Scheme.Modules.IsLineBundle.exists_trivialization M x
  obtain ⟨t₂, hx₂⟩ := AlgebraicGeometry.Scheme.Modules.IsLineBundle.exists_trivialization N x
  refine ⟨t₁.carrier ⊓ t₂.carrier, ⟨hx₁, hx₂⟩, ?_⟩
  set U : X.Opens := t₁.carrier ⊓ t₂.carrier with hU
  let R := AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι
  have hR : R.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (AlgebraicGeometry.Scheme.Modules.restrictAdjunction U.ι)
  have hψ : Epi (R.map φ) := R.map_epi φ
  let e : N.restrict U.ι ≅ M.restrict U.ι :=
    t₂.shrink inf_le_right ≪≫ (t₁.shrink inf_le_left).symm
  have hepi : Epi (R.map φ ≫ e.hom) := epi_comp _ _
  have hiso : IsIso (R.map φ ≫ e.hom) := by
    rw [AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective]
    intro y
    have hsurj := MiyaokaMori.FreeStalk.stalkMap_surjective_of_epi (R.map φ ≫ e.hom) y
    have hfin : Module.Finite (U.toScheme.presheaf.stalk y) ((M.restrict U.ι).presheaf.stalk y) :=
      AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isFiniteType (M.restrict U.ι) y
    exact OrzechProperty.bijective_of_surjective_endomorphism _ hsurj
  exact IsIso.of_isIso_comp_right (R.map φ) e.hom

end
