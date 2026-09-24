import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.GroupSchemeAction
import MiyaokaMori.AlgebraicGeometry.Modules.RelativeSpecAffine

/-! # Coaction of a `G_m`-action on a relative spectrum

Let `Spec_X A` be an affine `X`-scheme with a `G_m`-action `α` over `X`, and let `U ⊆ X` be an affine
open with `R := A(U)`. This file constructs the coaction `GroupSchemeAction.coaction α U : R →+* R[λ^{±1}]`
of `α` on the coordinate ring, i.e. the ring-level description of the action over `U`. It is the relative
version of the correspondence between `G_m`-actions and gradings (Stacks Project, Tag 0EKK): for an
action whose coaction lands in `R ⊗ k[λ]` (an action of the monoid `A¹`) the coaction gives an
`ℕ`-grading, which is how the coordinate algebra of the twisted affine cone acquires its nonnegative
grading (§2.1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The coaction. For an affine open `U`, `e : (Spec_X A)|_U ≅ Spec R` (`R := A(U)`, `relativeSpec.affineIso`).
   The map `k → R` is the preimage `φ_k` under the fully faithful `Spec` of
   `Spec R → π⁻¹U → Spec_X A → X → Spec k` (`Spec.preimage`, constructive), so that
   `G_m ×_k Spec R ≅ Spec(k[λ^{±1}] ⊗_k R)` (Mathlib `pullbackSpecIso`). Map this into the domain of the
   action through `e⁻¹` and the open immersion, apply `α.act`, come back to `π⁻¹U` by the universal property
   of the open immersion (`IsOpenImmersion.lift`; the action preserves `π`, so the image lies in `π⁻¹U`),
   then to `Spec R` through `e`, and take `Spec.preimage` to get `R → k[λ^{±1}] ⊗_k R`. Finally compose with
   `k[λ^{±1}] ⊗_k R → R[λ^{±1}]`, `λ ↦ λ`, `r ↦ C r` (`Algebra.TensorProduct.lift`). -/

/-! ## Components of `GroupSchemeAction.coaction`

Each intermediate morphism of the construction is a named declaration, together with the three proof
obligations `range_subset`, `laurentHom_commutes` and `constHom_commutes`. -/

section Coaction

/-- `φ_k : k → A(U)`, the preimage under the fully faithful `Spec` of
`Spec R ≅ π⁻¹U ↪ Spec_X A → X → Spec k`. -/
noncomputable def GroupSchemeAction.coaction.structureHom {X : AlgebraicGeometry.Scheme.{u}}
    {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {A : X.QCAlgebra}
    (U : X.affineOpens) : CommRingCat.of k ⟶ CommRingCat.of (A.sectionsRing U.1) :=
  AlgebraicGeometry.Spec.preimage
    ((AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).inv ≫
      ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1).ι ≫
      ((AlgebraicGeometry.Scheme.relativeSpec A).hom ≫
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))

set_option warn.classDefReducibility false in
/-- The `k`-algebra structure on `A(U)` induced by `structureHom`. It is deliberately not registered as a
global instance; it is introduced locally with `letI := GroupSchemeAction.coaction.algebra U`. -/
noncomputable def GroupSchemeAction.coaction.algebra {X : AlgebraicGeometry.Scheme.{u}}
    {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {A : X.QCAlgebra}
    (U : X.affineOpens) : Algebra k (A.sectionsRing U.1) :=
  (GroupSchemeAction.coaction.structureHom (k := k) (A := A) U).hom.toAlgebra

/-- The morphism `Spec(k[λ^{±1}] ⊗_k R) → G_m ×_k (Spec_X A)`. -/
noncomputable def GroupSchemeAction.coaction.toDom {X : AlgebraicGeometry.Scheme.{u}}
    {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {A : X.QCAlgebra}
    (U : X.affineOpens) :
    letI := GroupSchemeAction.coaction.algebra (k := k) (A := A) U
    AlgebraicGeometry.Spec (CommRingCat.of
        (TensorProduct k (LaurentPolynomial k) (A.sectionsRing U.1))) ⟶
      CategoryTheory.Limits.pullback
        ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        ((AlgebraicGeometry.Scheme.relativeSpec A).hom ≫
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :=
  letI := GroupSchemeAction.coaction.algebra (k := k) (A := A) U
  (AlgebraicGeometry.pullbackSpecIso k (LaurentPolynomial k) (A.sectionsRing U.1)).inv ≫
    CategoryTheory.Limits.pullback.map _ _ _ _
      (CategoryTheory.CategoryStruct.id _)
      ((AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).inv ≫
        ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1).ι)
      (CategoryTheory.CategoryStruct.id _)
      (by rw [CategoryTheory.Category.comp_id]; exact (CategoryTheory.Category.id_comp _).symm)
      (by
        rw [CategoryTheory.Category.comp_id, CategoryTheory.Category.assoc]
        exact AlgebraicGeometry.Spec.map_preimage
          ((AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).inv ≫
            ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1).ι ≫
            ((AlgebraicGeometry.Scheme.relativeSpec A).hom ≫
              (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))))

/-- The action restricted to `Spec(k[λ^{±1}] ⊗_k R)`: the morphism `Spec(k[λ^{±1}] ⊗_k R) → Spec_X A`. -/
noncomputable def GroupSchemeAction.coaction.act' {X : AlgebraicGeometry.Scheme.{u}}
    {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {A : X.QCAlgebra}
    (α : GmActionOver k (AlgebraicGeometry.Scheme.relativeSpec A)) (U : X.affineOpens) :
    letI := GroupSchemeAction.coaction.algebra (k := k) (A := A) U
    AlgebraicGeometry.Spec (CommRingCat.of
        (TensorProduct k (LaurentPolynomial k) (A.sectionsRing U.1))) ⟶
      (AlgebraicGeometry.Scheme.relativeSpec A).left :=
  letI := GroupSchemeAction.coaction.algebra (k := k) (A := A) U
  GroupSchemeAction.coaction.toDom (A := A) U ≫ α.act

/-- The image of `act'` lies in `π⁻¹U`. This is the hypothesis needed to restrict the action back to
`V = π⁻¹U` (the input of `IsOpenImmersion.lift`); it is the relative form of the fact that the action
preserves the projection to the base (Stacks Project, Tag 0EKK).

Proof. `α.act_over` says that the action preserves the structure morphism to `X`: `act ≫ π = pr₂ ≫ π`,
where `pr₂` is the second projection `G_m ×_k Spec_X A → Spec_X A`. By construction the second component
of `toDom` is `Spec R ≅ π⁻¹U ↪ Spec_X A`, whose image under `π` lies in `U`. Hence for every point `z` of
`Spec(k[λ^{±1}] ⊗_k R)`, `π (act' z) = π (pr₂ (toDom z)) ∈ U`, i.e. `act' z ∈ π⁻¹U = V`; the image of `V.ι`
is the underlying set of `V` (`Scheme.Opens.range_ι`), so `Set.range act' ⊆ Set.range V.ι`.

In the formal proof this is done first at the level of morphisms (`key`: `act' ≫ π = pullbackSpecIso.inv ≫
pr₂ ≫ affineIso.inv ≫ V.ι ≫ π`, by unfolding `act'`/`toDom` and using `α.act_over` and
`pullback.lift_snd_assoc`), then pointwise. -/
theorem GroupSchemeAction.coaction.range_subset {X : AlgebraicGeometry.Scheme.{u}}
    {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {A : X.QCAlgebra}
    (α : GmActionOver k (AlgebraicGeometry.Scheme.relativeSpec A)) (U : X.affineOpens) :
    letI := GroupSchemeAction.coaction.algebra (k := k) (A := A) U
    Set.range (GroupSchemeAction.coaction.act' α U) ⊆
      Set.range ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1).ι := by
  let _ := GroupSchemeAction.coaction.algebra (k := k) (A := A) U
  -- At the level of morphisms: act' ≫ π = (pullbackSpecIso.inv ≫ pr₂ ≫ affineIso.inv) ≫ V.ι ≫ π
  -- (from act_over and map_snd).
  have key : GroupSchemeAction.coaction.act' α U ≫ (AlgebraicGeometry.Scheme.relativeSpec A).hom =
      (AlgebraicGeometry.pullbackSpecIso k (LaurentPolynomial k) (A.sectionsRing U.1)).inv ≫
        CategoryTheory.Limits.pullback.snd _ _ ≫
        (AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).inv ≫
        ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1).ι ≫
        (AlgebraicGeometry.Scheme.relativeSpec A).hom := by
    unfold GroupSchemeAction.coaction.act' GroupSchemeAction.coaction.toDom
    rw [CategoryTheory.Category.assoc, α.act_over, CategoryTheory.Category.assoc,
      CategoryTheory.Limits.pullback.lift_snd_assoc]
    simp only [CategoryTheory.Category.assoc]
  rintro _ ⟨z, rfl⟩
  rw [AlgebraicGeometry.Scheme.Opens.range_ι, SetLike.mem_coe,
    AlgebraicGeometry.Scheme.Hom.mem_preimage, ← AlgebraicGeometry.Scheme.Hom.comp_apply, key]
  simp only [AlgebraicGeometry.Scheme.Hom.comp_apply]
  rw [← AlgebraicGeometry.Scheme.Hom.mem_preimage]
  exact Subtype.mem _

/-- The action restricted to `V = π⁻¹U`, by the universal property of the open immersion `V.ι`
(no choice is involved). -/
noncomputable def GroupSchemeAction.coaction.actV {X : AlgebraicGeometry.Scheme.{u}}
    {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {A : X.QCAlgebra}
    (α : GmActionOver k (AlgebraicGeometry.Scheme.relativeSpec A)) (U : X.affineOpens) :
    letI := GroupSchemeAction.coaction.algebra (k := k) (A := A) U
    AlgebraicGeometry.Spec (CommRingCat.of
        (TensorProduct k (LaurentPolynomial k) (A.sectionsRing U.1))) ⟶
      ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1).toScheme :=
  letI := GroupSchemeAction.coaction.algebra (k := k) (A := A) U
  AlgebraicGeometry.IsOpenImmersion.lift
    ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1).ι
    (GroupSchemeAction.coaction.act' α U)
    (GroupSchemeAction.coaction.range_subset α U)

/-- The coaction at the level of rings: `R → k[λ^{±1}] ⊗_k R`, the preimage under the fully faithful `Spec`. -/
noncomputable def GroupSchemeAction.coaction.ringHom {X : AlgebraicGeometry.Scheme.{u}}
    {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {A : X.QCAlgebra}
    (α : GmActionOver k (AlgebraicGeometry.Scheme.relativeSpec A)) (U : X.affineOpens) :
    letI := GroupSchemeAction.coaction.algebra (k := k) (A := A) U
    CommRingCat.of (A.sectionsRing U.1) ⟶
      CommRingCat.of (TensorProduct k (LaurentPolynomial k) (A.sectionsRing U.1)) :=
  letI := GroupSchemeAction.coaction.algebra (k := k) (A := A) U
  AlgebraicGeometry.Spec.preimage
    (GroupSchemeAction.coaction.actV α U ≫
      (AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).hom)

/-- `λ` is a unit of `R[λ^{±1}]`. -/
noncomputable def GroupSchemeAction.coaction.unitT {X : AlgebraicGeometry.Scheme.{u}}
    {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {A : X.QCAlgebra}
    (U : X.affineOpens) : (LaurentPolynomial (A.sectionsRing U.1))ˣ :=
  unitOfInvertible (LaurentPolynomial.T 1)

/-- `k[λ^{±1}] → R[λ^{±1}]` is a `k`-algebra homomorphism (the `commutes'` field of the `AlgHom`).

Proof. `algebraMap k (LaurentPolynomial k) r = LaurentPolynomial.C r`, and `eval₂ (C ∘ algebraMap k R) unitT`
sends `C r` to `C (algebraMap k R r)` (`LaurentPolynomial.algebraMap_apply`, `LaurentPolynomial.eval₂_C`),
which is `algebraMap k (LaurentPolynomial R) r` by definition of the algebra structure on
`AddMonoidAlgebra`. -/
theorem GroupSchemeAction.coaction.laurentHom_commutes {X : AlgebraicGeometry.Scheme.{u}}
    {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {A : X.QCAlgebra}
    (U : X.affineOpens) :
    letI := GroupSchemeAction.coaction.algebra (k := k) (A := A) U
    ∀ r : k,
      LaurentPolynomial.eval₂
          (LaurentPolynomial.C.comp (algebraMap k (A.sectionsRing U.1)))
          (GroupSchemeAction.coaction.unitT (k := k) (A := A) U)
          (algebraMap k (LaurentPolynomial k) r) =
        algebraMap k (LaurentPolynomial (A.sectionsRing U.1)) r := by
  intro r
  rw [LaurentPolynomial.algebraMap_apply (A := k),
    LaurentPolynomial.eval₂_C]
  rfl

/-- `k[λ^{±1}] → R[λ^{±1}]`, `λ ↦ λ`, constants through `φ_k`. -/
noncomputable def GroupSchemeAction.coaction.laurentHom {X : AlgebraicGeometry.Scheme.{u}}
    {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {A : X.QCAlgebra}
    (U : X.affineOpens) :
    letI := GroupSchemeAction.coaction.algebra (k := k) (A := A) U
    LaurentPolynomial k →ₐ[k] LaurentPolynomial (A.sectionsRing U.1) :=
  letI := GroupSchemeAction.coaction.algebra (k := k) (A := A) U
  { toRingHom := LaurentPolynomial.eval₂
      (LaurentPolynomial.C.comp (algebraMap k (A.sectionsRing U.1)))
      (GroupSchemeAction.coaction.unitT (k := k) (A := A) U)
    commutes' := GroupSchemeAction.coaction.laurentHom_commutes (k := k) (A := A) U }

/-- The constant embedding `C : R → R[λ^{±1}]` is a `k`-algebra homomorphism.

Proof. The `k`-algebra structure of `R[λ^{±1}] = AddMonoidAlgebra R ℤ` comes from `Algebra k R`, and its
`algebraMap k` is `single 0 ∘ algebraMap k R = C ∘ algebraMap k R`, so both sides agree definitionally
(`LaurentPolynomial.algebraMap_apply`). -/
theorem GroupSchemeAction.coaction.constHom_commutes {X : AlgebraicGeometry.Scheme.{u}}
    {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {A : X.QCAlgebra}
    (U : X.affineOpens) :
    letI := GroupSchemeAction.coaction.algebra (k := k) (A := A) U
    ∀ r : k,
      LaurentPolynomial.C (algebraMap k (A.sectionsRing U.1) r) =
        algebraMap k (LaurentPolynomial (A.sectionsRing U.1)) r := by
  intro r
  rfl

/-- The constant embedding `R → R[λ^{±1}]`. -/
noncomputable def GroupSchemeAction.coaction.constHom {X : AlgebraicGeometry.Scheme.{u}}
    {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {A : X.QCAlgebra}
    (U : X.affineOpens) :
    letI := GroupSchemeAction.coaction.algebra (k := k) (A := A) U
    A.sectionsRing U.1 →ₐ[k] LaurentPolynomial (A.sectionsRing U.1) :=
  letI := GroupSchemeAction.coaction.algebra (k := k) (A := A) U
  { toRingHom := LaurentPolynomial.C
    commutes' := GroupSchemeAction.coaction.constHom_commutes (k := k) (A := A) U }

/-- The coaction `A(U) → A(U)[λ^{±1}]` of the `G_m`-action `α` on `Spec_X A` over the affine open `U`:
the ring-level coaction `R → k[λ^{±1}] ⊗_k R` followed by `k[λ^{±1}] ⊗_k R → R[λ^{±1}]`, `λ ↦ λ`, `r ↦ C r`. -/
noncomputable def GroupSchemeAction.coaction {X : AlgebraicGeometry.Scheme.{u}} {k : Type u} [Field k]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {A : X.QCAlgebra}
    (α : GmActionOver k (AlgebraicGeometry.Scheme.relativeSpec A)) (U : X.affineOpens) :
    A.sectionsRing U.1 →+* LaurentPolynomial (A.sectionsRing U.1) :=
  letI := _root_.GroupSchemeAction.coaction.algebra (k := k) (A := A) U
  (Algebra.TensorProduct.lift
      (_root_.GroupSchemeAction.coaction.laurentHom (k := k) (A := A) U)
      (_root_.GroupSchemeAction.coaction.constHom (k := k) (A := A) U)
      (fun _ _ => Commute.all _ _)).toRingHom.comp
    (_root_.GroupSchemeAction.coaction.ringHom α U).hom

end Coaction

end
