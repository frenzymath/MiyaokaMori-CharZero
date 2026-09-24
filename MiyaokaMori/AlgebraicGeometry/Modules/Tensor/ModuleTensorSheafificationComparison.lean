import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.TensorPresheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafificationStalk
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

/-!
# Tensoring the actual module-sheafification unit

Tensoring the original module-sheafification unit with an arbitrary module
presheaf becomes an isomorphism after the same sheafification functor. On stalks,
the actual tensor comparison identifies this map with the tensor product of the
original unit's linear stalk isomorphism and the identity. Local surjectivity is
also established directly by induction on finite sums of tensor generators.

The intended consumer is associativity of the original `moduleTensor`, needed
for the coefficient pairing of the paper. The original unit
retains its identity restriction-of-scalars target. There is no flatness or local
freeness hypothesis, nor any claim that arbitrary tensor-sheaf sections are pure.

Sources: Stacks Project, `modules.tex`, `section-tensor-product` and Tag 01CB;
Mathlib's covering image sieves and localization of module sheaves.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false

/-- Tensoring a locally surjective module-presheaf map with the identity remains
locally surjective. Finite sums of tensor generators require finite intersections
of covering image sieves. -/
theorem moduleTensorHom_isLocallySurjective
    {P P' : X.PresheafOfModules} (f : P ⟶ P') (Q : X.PresheafOfModules)
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f] :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) f (𝟙 Q)) := by
  let J := Opens.grothendieckTopology X
  let f' := (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f
  let t := PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) f (𝟙 Q)
  let t' := (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map t
  refine ⟨fun {U} z ↦ ?_⟩
  change Presheaf.imageSieve t' z ∈ J U
  induction z using TensorProduct.induction_on with
  | zero =>
    apply J.superset_covering (S := ⊤) ?_ (J.top_mem U)
    intro V i _
    exact ⟨0, by simp only [map_zero]⟩
  | tmul p q =>
    apply J.superset_covering ?_ (Presheaf.imageSieve_mem J f' p)
    intro V i hi
    obtain ⟨p', hp'⟩ := hi
    change f.app (op V) p' = P'.map i.op p at hp'
    refine ⟨p' ⊗ₜ Q.map i.op q, ?_⟩
    change f.app (op V) p' ⊗ₜ[X.presheaf.obj (op V)] Q.map i.op q =
      P'.map i.op p ⊗ₜ[X.presheaf.obj (op V)] Q.map i.op q
    rw [hp']
  | add z w hz hw =>
    apply J.superset_covering ?_ (J.intersection_covering hz hw)
    intro V i hi
    obtain ⟨z', hz'⟩ := hi.1
    obtain ⟨w', hw'⟩ := hi.2
    refine ⟨z' + w', ?_⟩
    simp only [map_add, hz', hw']

/-- The original module-sheafification unit is locally surjective, including its
specified restriction of scalars along the identity of the structure presheaf. -/
theorem moduleSheafificationUnit_isLocallySurjective (P : X.PresheafOfModules) :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P) := by
  -- After `rw [toPresheaf_map_sheafificationAdjunction_unit_app]`, `infer_instance` fails: the universe
  -- parameters in the rewritten `toSheafify` term do not match the head of Mathlib's instance. That
  -- lemma is `rfl` anyway, so state the instance directly with `inferInstanceAs` in Mathlib's spelling.
  exact inferInstanceAs (Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf))

/-- Tensoring the original sheafification unit with an arbitrary module presheaf
has local lifts. This supplies only the surjectivity half of local bijectivity. -/
theorem moduleSheafification_tensor_unit_isLocallySurjective
    (P Q : X.PresheafOfModules) :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)
        (𝟙 Q)) := by
  letI := moduleSheafificationUnit_isLocallySurjective P
  exact moduleTensorHom_isLocallySurjective _ Q

/-- Injectivity on the actual module stalks detects local injectivity. The proof
uses a common neighborhood witnessing equality of two germs. -/
theorem modulePresheaf_isLocallyInjective_of_stalkMap_injective
    {P Q : X.PresheafOfModules} (f : P ⟶ Q)
    (h : ∀ x : X, Function.Injective
      ((TopCat.Presheaf.stalkFunctor Ab x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f))) :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f := by
  refine ⟨fun {U} a b hab x hx ↦ ?_⟩
  have key : ∀ s : P.obj U,
      (TopCat.Presheaf.stalkFunctor Ab x).map
          ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f)
          (TopCat.Presheaf.germ P.presheaf U.unop x hx s) =
        TopCat.Presheaf.germ Q.presheaf U.unop x hx
          (((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f).app U s) :=
    fun s => TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _
  have hg : TopCat.Presheaf.germ P.presheaf U.unop x hx a =
      TopCat.Presheaf.germ P.presheaf U.unop x hx b :=
    h x (by rw [key a, key b, hab])
  obtain ⟨V, hxV, i, j, hij⟩ :=
    TopCat.Presheaf.germ_eq P.presheaf x hx hx a b hg
  refine ⟨V, i, ?_, hxV⟩
  show P.presheaf.map i.op a = P.presheaf.map i.op b
  simpa only [Subsingleton.elim j i] using hij

/-- A locally bijective map of the original module presheaves becomes invertible
under the same module-sheafification functor. -/
theorem moduleSheafification_map_isIso_of_locallyBijective
    {P Q : X.PresheafOfModules} (f : P ⟶ Q)
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f] :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f) := by
  have hw : ((Opens.grothendieckTopology X).W.inverseImage
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)) f :=
    (Opens.grothendieckTopology X).W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f)
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 X.ringCatSheaf.obj)] at hw
  exact hw

/-- On actual stalks, tensoring the original unit is identified with tensoring
its linear equivalence. The target explicitly retains restriction of scalars. -/
theorem moduleSheafification_tensor_unit_stalk_naturality
    (P Q : X.PresheafOfModules) (x : X)
    (z : ↑(TopCat.Presheaf.stalk (C := Ab)
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) P Q).presheaf x)) :
    tensorPresheafStalkEquiv X
      ((PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
        (moduleSheafification X P).val) Q x
      ((TopCat.Presheaf.stalkFunctor Ab x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
          (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
            ((PresheafOfModules.sheafificationAdjunction
              (𝟙 X.ringCatSheaf.obj)).unit.app P) (𝟙 Q))) z) =
    TensorProduct.congr (moduleSheafificationStalkEquiv X P x)
      (LinearEquiv.refl (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk (C := Ab) Q.presheaf x))
      (tensorPresheafStalkEquiv X P Q x z) := by
  obtain ⟨U, hx, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) P Q).presheaf z
  induction a using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m n =>
    -- `rw` does not find the pattern here because `(toPresheaf R).obj M` and `M.presheaf` are only
    -- defeq (the goal is ill-typed at implicit transparency); use `erw`. The `_` in `change` must be
    -- spelled out, otherwise the dot notation `.presheaf.germ` resolves to `Functor.germ`.
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change tensorPresheafStalkEquiv X _ Q x
      (TopCat.Presheaf.germ
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
          ((PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
            (moduleSheafification X P).val) Q).presheaf
        U x hx (moduleSheafificationUnit X P U m ⊗ₜ[X.presheaf.obj (op U)] n)) = _
    erw [tensorPresheafStalkEquiv_germ_tmul, tensorPresheafStalkEquiv_germ_tmul,
      TensorProduct.congr_tmul, moduleSheafificationStalkEquiv_germ]
    rfl
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb

/-- Tensoring the actual sheafification unit is locally injective, because its
stalk map is conjugate to a tensor product of linear equivalences. -/
theorem moduleSheafification_tensor_unit_isLocallyInjective
    (P Q : X.PresheafOfModules) :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
      (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)
        (𝟙 Q)) := by
  apply modulePresheaf_isLocallyInjective_of_stalkMap_injective
  intro x a b hab
  apply (tensorPresheafStalkEquiv X P Q x).injective
  apply (TensorProduct.congr (moduleSheafificationStalkEquiv X P x)
    (LinearEquiv.refl (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk (C := Ab) Q.presheaf x))).injective
  rw [← moduleSheafification_tensor_unit_stalk_naturality P Q x a,
    ← moduleSheafification_tensor_unit_stalk_naturality P Q x b, hab]

/-- Tensoring the original module-sheafification unit with any module presheaf
becomes an isomorphism under the same sheafification functor. -/
theorem moduleSheafification_tensor_unit_isIso (P Q : X.PresheafOfModules) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app P) (𝟙 Q))) := by
  -- The two local bijectivity facts are ordinary theorems, not instances; `letI` on a `Prop` does not
  -- register a local instance (Lean only inlines the value), so they are passed explicitly with `@`.
  exact @moduleSheafification_map_isIso_of_locallyBijective _ _ _ _
    (moduleSheafification_tensor_unit_isLocallyInjective P Q)
    (moduleSheafification_tensor_unit_isLocallySurjective P Q)

end AlgebraicGeometry.Scheme.Modules
