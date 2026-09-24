import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldEqResidueFieldAtGenericPoint

/-! # Stalks of the generic fibre

The generic fibre `X_η = X ×_Y Spec κ(η)` of a morphism `f : X → Y` to an integral scheme `Y`
(η the generic point of `Y`), at the level of general schemes:

* `Spec 𝒪_{Y,y} → Y` is flat (locally a localisation `Spec A_𝔭 → Spec A`), so at the generic
  point of an integral scheme `Spec κ(η) → Y` is flat (`κ(η) = 𝒪_{Y,η}`);
* a flat morphism which is surjective on stalks (e.g. a flat preimmersion) is an isomorphism on
  every stalk: a flat local homomorphism of local rings is faithfully flat, hence injective
  (Mathlib `Module.FaithfullyFlat.of_flat_of_isLocalHom`; Stacks, Algebra, "flat local
  homomorphisms of local rings are faithfully flat", Lemma 10.39.17);
* hence the fibre inclusion `X_η → X` (a preimmersion, Mathlib) induces isomorphisms
  `𝒪_{X,ι(ξ)} ≅ 𝒪_{X_η,ξ}` at every point;
* the fibre is irreducible as soon as it contains the generic point of `X` (its underlying set is
  `f⁻¹{y}`, which is then squeezed between `{ξ₀}` and `closure {ξ₀} = X`), reduced (stalks are
  stalks of `X`), so integral (Stacks 02S2, proof, third paragraph);
* it is locally Noetherian since `X_η → Spec κ(η)` is locally of finite type over a field
  (Mathlib `LocallyOfFiniteType.isLocallyNoetherian`);
* naturality of the global-sections / germ maps along the fibre square, used to identify the
  `k`-algebra structures on the function field of the fibre (`fiber_appTop_comm`);
* the generic point of `X_η` maps to the generic point of `X` (`fiberι_genericPoint_eq`).

Source: Stacks 02S2 (third paragraph of the proof); flatness of base change: Stacks 01U2.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
/-- `Spec 𝒪_{X,x} → X` is flat: locally it is `Spec A_𝔭 → Spec A`, a localization. -/
theorem flat_fromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  unfold IsAffineOpen.fromSpecStalk
  have : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
    haveI := hU.isLocalization_stalk ⟨x, hxU⟩
    exact IsLocalization.flat _ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have : Flat hU.fromSpec := HasRingHomProperty.of_isOpenImmersion RingHom.Flat.containsIdentities
  exact Flat.comp _ _

/-- At the generic point of an integral scheme, `Spec κ(η) → X` is flat
(`κ(η) = 𝒪_{X,η}` is the function field, so `Spec κ(η) → X` is `Spec 𝒪_{X,η} → X` up to an
isomorphism). -/
theorem flat_fromSpecResidueField_genericPoint (X : Scheme.{u}) [IsIntegral X] :
    Flat (X.fromSpecResidueField (genericPoint X)) := by
  unfold Scheme.fromSpecResidueField
  haveI := flat_fromSpecStalk X (genericPoint X)
  infer_instance

/-- A flat morphism which is surjective on stalks induces isomorphisms on all stalks
(a flat local homomorphism of local rings is faithfully flat, hence injective). -/
theorem isIso_stalkMap_of_flat_of_surjectiveOnStalks {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [SurjectiveOnStalks f] (x : X) : IsIso (f.stalkMap x) := by
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, f.stalkMap_surjective x⟩
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

/-- The generic fibre `X_η → X` of a morphism to an integral scheme induces isomorphisms on
all stalks: `𝒪_{X,ι(ξ)} ≅ 𝒪_{X_η,ξ}`. -/
theorem isIso_stalkMap_fiberι_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y]
    (ξ : f.fiber (genericPoint Y)) : IsIso ((f.fiberι (genericPoint Y)).stalkMap ξ) := by
  haveI := flat_fromSpecResidueField_genericPoint Y
  haveI : Flat (f.fiberι (genericPoint Y)) :=
    inferInstanceAs (Flat (pullback.fst f (Y.fromSpecResidueField (genericPoint Y))))
  exact isIso_stalkMap_of_flat_of_surjectiveOnStalks _ ξ

/-- A fibre containing the generic point of an irreducible source is irreducible: its underlying
set `f⁻¹{y}` lies between `{ξ₀}` and `closure {ξ₀} = X`. -/
theorem irreducibleSpace_fiber_of_genericPoint_mem {X Y : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ Y) (y : Y) (hp : f (genericPoint X) = y) : IrreducibleSpace (f.fiber y) := by
  rw [(f.fiberHomeo y).irreducibleSpace_iff]
  apply Subtype.irreducibleSpace
  refine ⟨⟨genericPoint X, hp⟩, ?_⟩
  rw [← isPreirreducible_iff_closure]
  have : closure (f ⁻¹' {y}) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    calc Set.univ = closure ({genericPoint X} : Set X) := (genericPoint_closure X).symm
      _ ⊆ closure (f ⁻¹' {y}) := closure_mono (Set.singleton_subset_iff.mpr hp)
  rw [this]
  exact PreirreducibleSpace.isPreirreducible_univ

/-- The generic fibre of a reduced scheme over an integral scheme is reduced (its stalks are
stalks of `X`). -/
theorem isReduced_fiber_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] [IsReduced X] :
    IsReduced (f.fiber (genericPoint Y)) := by
  haveI : ∀ ξ : f.fiber (genericPoint Y),
      _root_.IsReduced ((f.fiber (genericPoint Y)).presheaf.stalk ξ) := fun ξ => by
    haveI := isIso_stalkMap_fiberι_genericPoint f ξ
    exact isReduced_of_injective (inv ((f.fiberι (genericPoint Y)).stalkMap ξ)).hom
      (ConcreteCategory.bijective_of_isIso _).1
  exact isReduced_of_isReduced_stalk _

/-- The generic fibre of a dominant morphism of integral schemes is integral
(Stacks 02S2, proof, third paragraph). -/
theorem isIntegral_fiber_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    (hp : f (genericPoint X) = genericPoint Y) : IsIntegral (f.fiber (genericPoint Y)) := by
  haveI := isReduced_fiber_genericPoint f
  haveI := irreducibleSpace_fiber_of_genericPoint_mem f _ hp
  exact isIntegral_of_irreducibleSpace_of_isReduced _

set_option backward.isDefEq.respectTransparency.types false in
/-- Any fibre of a morphism locally of finite type is locally Noetherian: it is locally of
finite type over the field `κ(y)`. -/
theorem isLocallyNoetherian_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y) :
    IsLocallyNoetherian (f.fiber y) := by
  have : IsNoetherianRing (Y.residueField y) := inferInstance
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField y)))
  exact LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)

/-- `Γ(Y,⊤) → 𝒪_{Y,y} → κ(y) = Γ(Spec κ(y), ⊤)` is the global-sections map of `Spec κ(y) → Y`. -/
theorem fromSpecResidueField_appTop (Y : Scheme.{u}) (y : Y) :
    (Y.fromSpecResidueField y).appTop =
      Y.presheaf.germ ⊤ y trivial ≫ Y.residue y ≫ (Scheme.ΓSpecIso (Y.residueField y)).inv := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop,
    Scheme.ΓSpecIso_inv_naturality]
  simp

/-- Naturality of germs along the fibre inclusion, with `U = ⊤`. -/
theorem germ_top_stalkMap_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (ξ : f.fiber y) :
    X.presheaf.germ ⊤ ((f.fiberι y) ξ) trivial ≫ (f.fiberι y).stalkMap ξ =
      (f.fiberι y).appTop ≫ (f.fiber y).presheaf.germ ⊤ ξ trivial :=
  Scheme.Hom.germ_stalkMap (f.fiberι y) ⊤ ξ trivial

/-- Compatibility of the structure maps in the fibre square: for an `S`-morphism `f : X → Y`
and a point `ξ` of the fibre `X_y`, the composite `Γ(S) → Γ(X) → 𝒪_{X,ι(ξ)} → 𝒪_{X_y,ξ}` equals
`Γ(S) → Γ(Y) → 𝒪_{Y,y} → κ(y) = Γ(Spec κ(y)) → Γ(X_y) → 𝒪_{X_y,ξ}`. This identifies the
`k`-algebra structure on the function field of the generic fibre (through `κ(η)`) with the one
transported from `X`. -/
theorem fiber_appTop_comm {X Y S : Scheme.{u}} [X.Over S] [Y.Over S] (f : X ⟶ Y) [f.IsOver S]
    (y : Y) (ξ : f.fiber y) :
    (X ↘ S).appTop ≫ X.presheaf.germ ⊤ ((f.fiberι y) ξ) trivial ≫ (f.fiberι y).stalkMap ξ =
      (Y ↘ S).appTop ≫ Y.presheaf.germ ⊤ y trivial ≫ Y.residue y ≫
        (Scheme.ΓSpecIso (Y.residueField y)).inv ≫ (f.fiberToSpecResidueField y).appTop ≫
        (f.fiber y).presheaf.germ ⊤ ξ trivial := by
  rw [germ_top_stalkMap_fiberι, ← Category.assoc, ← Scheme.Hom.comp_appTop,
    ← comp_over f S, ← Category.assoc, Scheme.Hom.fiber_fac,
    Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, fromSpecResidueField_appTop]
  simp only [Category.assoc]

/-- The generic point of a fibre containing the generic point `ξ₀` of the (irreducible) source
maps to `ξ₀`: both points specialise to each other, and schemes are `T₀`. -/
theorem fiberι_genericPoint_eq {X Y : Scheme.{u}} [IrreducibleSpace X] (f : X ⟶ Y) (y : Y)
    [IrreducibleSpace (f.fiber y)] (hp : f (genericPoint X) = y) :
    (f.fiberι y) (genericPoint (f.fiber y)) = genericPoint X := by
  obtain ⟨z, hz⟩ : genericPoint X ∈ Set.range (f.fiberι y) := by
    rw [Scheme.Hom.range_fiberι]; exact hp
  have h1 : (f.fiberι y) (genericPoint (f.fiber y)) ⤳ genericPoint X :=
    hz ▸ (genericPoint_specializes z).map (f.fiberι y).continuous
  exact (h1.antisymm (genericPoint_specializes _)).eq

end AlgebraicGeometry

end
