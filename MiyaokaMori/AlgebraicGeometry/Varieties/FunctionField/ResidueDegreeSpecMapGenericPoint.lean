import MiyaokaMori.Prelude

/-! # Residue degree of `Spec φ` at the generic point

For an injective map `φ : R → S` of domains, the residue degree (`Scheme.Hom.residueDegree`) of
`Spec φ : Spec S → Spec R` at the generic point of `Spec S` equals the `Module.finrank` of `S` as
an `R`-module (via `φ`), i.e. `[Frac S : Frac R]`.

Sources: Stacks 02JL (residue fields of `Spec`); Mathlib `IsFractionRing.finrank_eq`. Used for
`deg g = [k(z) : k(y)]` in the degree computation of the weighted power map; it applies to any
degree computation for a morphism which is `Spec` of a ring map on an affine chart.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency.types false in
/-- The residue degree of `Spec φ` at any point `p` is the finrank of the residue field map
`κ(φ⁻¹p) → κ(p)` (`Ideal.ResidueField.map`): naturality of `Spec.residueFieldIso` (via
`Scheme.localRingHom_comp_stalkIso`). -/
theorem AlgebraicGeometry.Scheme.Hom.residueDegree_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (p : AlgebraicGeometry.Spec S) :
    (AlgebraicGeometry.Spec.map φ).residueDegree p =
      @Module.finrank ((AlgebraicGeometry.Spec.map φ) p).asIdeal.ResidueField p.asIdeal.ResidueField _ _
        (@Algebra.toModule _ _ _ _ (Ideal.ResidueField.map _ _ φ.hom rfl).toAlgebra) := by
  unfold AlgebraicGeometry.Scheme.Hom.residueDegree
  let _ : Algebra ((AlgebraicGeometry.Spec R).residueField ((AlgebraicGeometry.Spec.map φ) p))
      ((AlgebraicGeometry.Spec S).residueField p) :=
    ((AlgebraicGeometry.Spec.map φ).residueFieldMap p).hom.toAlgebra
  let _ : Algebra ((AlgebraicGeometry.Spec.map φ) p).asIdeal.ResidueField p.asIdeal.ResidueField :=
    (Ideal.ResidueField.map _ _ φ.hom rfl).toAlgebra
  let i : (AlgebraicGeometry.Spec R).residueField ((AlgebraicGeometry.Spec.map φ) p) ≃+*
      ((AlgebraicGeometry.Spec.map φ) p).asIdeal.ResidueField :=
    (AlgebraicGeometry.Scheme.Spec.residueFieldIso R ((AlgebraicGeometry.Spec.map φ) p)).commRingCatIsoToRingEquiv
  let j : (AlgebraicGeometry.Spec S).residueField p ≃+* p.asIdeal.ResidueField :=
    (AlgebraicGeometry.Scheme.Spec.residueFieldIso S p).commRingCatIsoToRingEquiv
  refine Algebra.finrank_eq_of_equiv_equiv i j ?_
  ext x
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  -- the four elementwise identities
  have e1 : ∀ (T : CommRingCat.{u}) (q : AlgebraicGeometry.Spec T)
      (t : (AlgebraicGeometry.Spec T).presheaf.stalk q),
      (AlgebraicGeometry.Scheme.Spec.residueFieldIso T q).hom ((AlgebraicGeometry.Spec T).residue q t) =
        IsLocalRing.residue _ ((AlgebraicGeometry.Spec.stalkIso T q).hom t) := by
    intro T q t
    rw [← CategoryTheory.ConcreteCategory.comp_apply,
      AlgebraicGeometry.Scheme.Spec.residue_residueFieldIso_hom,
      CategoryTheory.ConcreteCategory.comp_apply]
    rfl
  have e2 : ((AlgebraicGeometry.Spec.map φ).residueFieldMap p)
      ((AlgebraicGeometry.Spec R).residue _ r) =
      (AlgebraicGeometry.Spec S).residue p (((AlgebraicGeometry.Spec.map φ).stalkMap p) r) := by
    have := CategoryTheory.ConcreteCategory.congr_hom
      (AlgebraicGeometry.Scheme.residue_residueFieldMap (AlgebraicGeometry.Spec.map φ) p) r
    simpa only [CategoryTheory.ConcreteCategory.comp_apply] using this
  have e4 : (AlgebraicGeometry.Spec.stalkIso S p).hom (((AlgebraicGeometry.Spec.map φ).stalkMap p) r) =
      Localization.localRingHom _ _ φ.hom rfl ((AlgebraicGeometry.Spec.stalkIso R _).hom r) := by
    have h := AlgebraicGeometry.Scheme.localRingHom_comp_stalkIso_apply φ p r
    exact (congrArg (fun y => (AlgebraicGeometry.Spec.stalkIso S p).hom y) h.symm).trans
      ((AlgebraicGeometry.Spec.stalkIso S p).inv_hom_id_apply _)
  change Ideal.ResidueField.map _ _ φ.hom rfl
      ((AlgebraicGeometry.Scheme.Spec.residueFieldIso R ((AlgebraicGeometry.Spec.map φ) p)).hom
        ((AlgebraicGeometry.Spec R).residue _ r)) =
    (AlgebraicGeometry.Scheme.Spec.residueFieldIso S p).hom
      (((AlgebraicGeometry.Spec.map φ).residueFieldMap p) ((AlgebraicGeometry.Spec R).residue _ r))
  rw [e1, e2, e1, e4]
  exact IsLocalRing.ResidueField.map_residue _ _

/-- Pure algebra: for `I = ⊥`, `J = ⊥`, the finrank of `κ(I) → κ(J)` equals the finrank of `S` as
an `R`-module (the degree of the fraction fields is the rank of the rings,
`IsFractionRing.finrank_eq`). -/
theorem Ideal.ResidueField.finrank_map_bot {R S : Type u} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    (φ : R →+* S) (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime] (hIJ : I = J.comap φ)
    (hI : I = ⊥) (hJ : J = ⊥) :
    @Module.finrank I.ResidueField J.ResidueField _ _
        (@Algebra.toModule _ _ _ _ (Ideal.ResidueField.map I J φ hIJ).toAlgebra) =
      @Module.finrank R S _ _ (@Algebra.toModule _ _ _ _ φ.toAlgebra) := by
  subst hI hJ
  let _ : Algebra R S := φ.toAlgebra
  let _ : Algebra (⊥ : Ideal R).ResidueField (⊥ : Ideal S).ResidueField :=
    (Ideal.ResidueField.map ⊥ ⊥ φ hIJ).toAlgebra
  let _ : Algebra R (⊥ : Ideal S).ResidueField :=
    ((algebraMap S (⊥ : Ideal S).ResidueField).comp φ).toAlgebra
  have : IsScalarTower R (⊥ : Ideal R).ResidueField (⊥ : Ideal S).ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change (algebraMap S _).comp φ r = Ideal.ResidueField.map ⊥ ⊥ φ hIJ (algebraMap R _ r)
      rw [Ideal.ResidueField.map_algebraMap]; rfl
  have : IsScalarTower R S (⊥ : Ideal S).ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  exact IsFractionRing.finrank_eq R (⊥ : Ideal R).ResidueField S (⊥ : Ideal S).ResidueField

set_option backward.isDefEq.respectTransparency.types false in
/-- An injective map `φ : R → S` of domains gives `Spec φ : Spec S → Spec R`; its residue degree at
the generic point (the zero ideal) of `Spec S` is `[Frac S : Frac R]`, which equals the finrank of
`S` as an `R`-module (`IsFractionRing.finrank_eq`).

Sources: Stacks 02JL (residue fields of `Spec`) and Mathlib `IsFractionRing.finrank_eq`.

Proof: the generic point of `Spec S` is the zero ideal `⊥` (`genericPoint_eq_bot_of_affine`), and
`φ` is injective so `(Spec φ)(⊥) = φ⁻¹(⊥) = ⊥`. `Spec.residueFieldIso` identifies the residue
fields of `Spec R`, `Spec S` at `⊥` with `(⊥ : Ideal R).ResidueField`, `(⊥ : Ideal S).ResidueField`,
which are the fraction fields of `R`, `S` (`IsFractionRing R (⊥ : Ideal R).ResidueField`).
`Scheme.localRingHom_comp_stalkIso` shows that the stalk map of `Spec φ` is
`Localization.localRingHom` under `Spec.stalkIso`; passing to residue fields
(`IsLocalRing.ResidueField.map`), `(Spec φ).residueFieldMap ⊥` corresponds to
`Ideal.ResidueField.map ⊥ ⊥ φ`. Hence the residue degree is `finrank_{κ(⊥_R)} κ(⊥_S)`
(`Algebra.finrank_eq_of_equiv_equiv` to change to the isomorphic algebra structure), which equals
`finrank_R S` by `IsFractionRing.finrank_eq R κ(⊥_R) S κ(⊥_S)` (the scalar towers
`R → κ(⊥_R) → κ(⊥_S)` and `R → S → κ(⊥_S)` come from `Ideal.ResidueField.map_algebraMap`).

Edge case: for infinite rank both sides are `0` (the `finrank` convention), and the equation
still holds. -/
theorem AlgebraicGeometry.Scheme.Hom.residueDegree_specMap_genericPoint
    {R S : CommRingCat.{u}} [IsDomain R] [IsDomain S] (φ : R ⟶ S)
    (hφ : Function.Injective φ.hom) :
    (AlgebraicGeometry.Spec.map φ).residueDegree (genericPoint (AlgebraicGeometry.Spec S)) =
      @Module.finrank R S _ _ (@Algebra.toModule _ _ _ _ φ.hom.toAlgebra) := by
  have hJ : (genericPoint (AlgebraicGeometry.Spec S) : PrimeSpectrum S).asIdeal = ⊥ := by
    rw [AlgebraicGeometry.genericPoint_eq_bot_of_affine]
    rfl
  refine (AlgebraicGeometry.Scheme.Hom.residueDegree_specMap φ (genericPoint (AlgebraicGeometry.Spec S))).trans ?_
  refine Ideal.ResidueField.finrank_map_bot φ.hom _ _ rfl ?_ hJ
  change Ideal.comap φ.hom (genericPoint (AlgebraicGeometry.Spec S) : PrimeSpectrum S).asIdeal = ⊥
  rw [hJ]
  exact Ideal.comap_bot_of_injective _ hφ

end
