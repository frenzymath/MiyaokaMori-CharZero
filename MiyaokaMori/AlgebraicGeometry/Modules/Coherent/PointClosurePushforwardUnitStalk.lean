import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.PointClosureTransport
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesFiniteTypeInstances
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesQuasicoherentClosure
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01y6
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.Stacks00ae
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupportBasics

/-! # The pushforward of the structure sheaf of the closure of a point

The generator of the dévissage in Stacks 0BEN (paragraph "`dim V = d`" of the
proof, and Stacks 01YI condition (3)): for a point `ξ` of a locally Noetherian scheme `X`, with
`i := X.pointClosureι ξ : Z_ξ → X` the reduced induced structure on `closure {ξ}` (an integral scheme with
generic point `ξ`), the coherent sheaf `G := i_* O_{Z_ξ}` satisfies

* `G` is coherent (Stacks 01Y6: pushforward along a finite morphism; a closed immersion is finite);
* `Supp G = closure {ξ}` (Stacks 00AE: stalks of a pushforward along a closed embedding vanish off the
  image and agree with the stalks of `O_{Z_ξ}` on it; `O_{Z_ξ}` has nontrivial stalks);
* `m_ξ · G_ξ = 0` and `length_{O_{X,ξ}} G_ξ = 1`.

The last two are `pushforward_unit_pointClosure_stalk` below.
**Natural-language proof.**
`G_ξ = (i_* O_Z)_{i η}` with `η` the generic point of `Z = Z_ξ` (`i η = ξ`,
`Scheme.pointClosureι_genericPoint`). The stalk of a pushforward along a closed embedding at a point of
the image is the stalk of the original sheaf (Stacks 00AE, Mathlib `stalkPushforward_iso_of_isInducing`):
as abelian groups `G_ξ ≅ (O_Z)_η = O_{Z,η}`, and this isomorphism is `O_{X,ξ}`-linear when `O_{Z,η}` is
viewed as an `O_{X,ξ}`-module through the stalk map `i^♯_η : O_{X,ξ} → O_{Z,η}` (the module structure
of `i_* O_Z` on sections is through `i^♯`, and germs are compatible). `Z` is integral with generic point
`η`, so `O_{Z,η}` is a field (the function field; Mathlib `functionField` / `IsIntegral` ⇒ stalk at the
generic point is a field, `Scheme.functionField` is `Z.presheaf.stalk (genericPoint Z)` with a `Field`
instance). The stalk map `i^♯_η` is a surjective local ring homomorphism (`i` is a closed immersion:
`Scheme.Hom.stalkMap_surjective`; local by construction), so it kills `m_ξ` (the image of `m_ξ` lies in the
maximal ideal of the field `O_{Z,η}`, which is `0`): this is `m_ξ ≤ Ann(G_ξ)`. Finally
`length_{O_{X,ξ}} O_{Z,η} = length_{O_{Z,η}} O_{Z,η}` (Mathlib `Module.length_eq_of_surjective`, lattice
of submodules unchanged under a surjective scalar map) `= 1` (a field is a simple module over itself:
Mathlib `IsSimpleModule K K`, `Module.length_eq_one`).

**Edge cases.** `ξ` a closed point: `Z_ξ = Spec κ(ξ)`, `G` the skyscraper `κ(ξ)`, both statements are
literal. `X` a single point: same. `ξ` a generic point of `X`: `G_ξ = O_{X,ξ}/nilradical`, still a field.

**Formalization.** `pushforwardUnitStalkLinearEquiv i z` is the `O_{X,iz}`-linear
comparison `(i_* O_Z)_{iz} ≃ O_{Z,z}` for any closed immersion `i` and any `z ∈ Z` (the `O_{X,iz}`-action on
`O_{Z,z}` is `(i.stalkMap z).hom.toAlgebra`); it is Mathlib's abelian `stalkPushforward` iso composed with
`unitStalkLinearEquiv`, and linearity is checked on germs (`pushforward_smul_def`,
`stalkPushforward_germ_apply`, `unitStalkLinearEquiv_germ`, `germ_stalkMap_apply`).
`maximalIdeal_le_annihilator_and_length_pushforward_unit_stalk` is the general statement for a point `z`
with `O_{Z,z}` a field; the main statement is its instance at the generic point of `Z_ξ`, where `O_{Z_ξ,η}` is
Mathlib's `functionField` (a field since `Z_ξ` is integral).

Source: Stacks 0BEN (proof), 01YI (3), 00AE, 01Y6.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- `G_ξ := (i_* O_{Z_ξ})_ξ` for `i = pointClosureι ξ`: the generator sheaf of the 0BEN dévissage. -/
abbrev pointClosureUnitPushforward {X : AlgebraicGeometry.Scheme.{u}} (ξ : X) : X.Modules :=
  (AlgebraicGeometry.Scheme.Modules.pushforward (X.pointClosureι ξ)).obj
    (SheafOfModules.unit (X.pointClosure ξ).ringCatSheaf)

section StalkOfPushforwardUnit

variable {Z X : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] (z : Z)

/-- The `O_{X, i z}`-linear stalk comparison `(i_* O_Z)_{i z} ≃ O_{Z,z}` for a closed immersion `i`
(Stacks 00AE: the underlying abelian group is `stalkPushforward_iso_of_isInducing`; the scalar action
of `O_{X,iz}` on `O_{Z,z}` is through the stalk map `i^♯_z`, i.e. `(i.stalkMap z).hom.toAlgebra`). -/
noncomputable def pushforwardUnitStalkLinearEquiv :
    letI := AlgebraicGeometry.Scheme.Modules.moduleStalkModule X
      ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) (i.base z)
    letI : Algebra (X.presheaf.stalk (i.base z)) (Z.presheaf.stalk z) := (i.stalkMap z).hom.toAlgebra
    ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk (i.base z) ≃ₗ[X.presheaf.stalk (i.base z)]
      Z.presheaf.stalk z := by
  letI := AlgebraicGeometry.Scheme.Modules.moduleStalkModule X
    ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) (i.base z)
  letI : Algebra (X.presheaf.stalk (i.base z)) (Z.presheaf.stalk z) := (i.stalkMap z).hom.toAlgebra
  letI := AlgebraicGeometry.Scheme.Modules.moduleStalkModule Z (SheafOfModules.unit Z.ringCatSheaf) z
  -- the abelian-group isomorphism (Stacks 00AE)
  have hiso : IsIso ((AlgebraicGeometry.Scheme.Modules.presheaf (X := Z)
      (SheafOfModules.unit Z.ringCatSheaf)).stalkPushforward AddCommGrpCat.{u} i.base z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{u}
      i.isClosedEmbedding.isInducing _ z
  let ψ : ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk (i.base z) ≃+
      (AlgebraicGeometry.Scheme.Modules.presheaf (X := Z) (SheafOfModules.unit Z.ringCatSheaf)).stalk z :=
    (asIso ((AlgebraicGeometry.Scheme.Modules.presheaf (X := Z)
      (SheafOfModules.unit Z.ringCatSheaf)).stalkPushforward AddCommGrpCat.{u} i.base z)).addCommGroupIsoToAddEquiv
  let u := AlgebraicGeometry.Divisors.LineGenericCoordinates.unitStalkLinearEquiv Z z
  refine { ψ.trans u.toAddEquiv with map_smul' := ?_ }
  intro r m
  obtain ⟨V, hxV, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨W, hWV, hxW, b, rfl⟩ := ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)).presheaf.exists_le_germ_eq m hxV
  rw [← X.presheaf.germ_res_apply (homOfLE hWV) (i.base z) hxW a]
  erw [← PresheafOfModules.germ_smul (R := X.presheaf)
    ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).val]
  -- the composite comparison sends a germ of `i_* O_Z` on `W` to the germ of the same section of
  -- `O_Z` on `i⁻¹ W`
  have key : ∀ s : Γ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf), W),
      (ψ.trans u.toAddEquiv)
        (((AlgebraicGeometry.Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.germ W (i.base z) hxW s) =
      Z.presheaf.germ (i ⁻¹ᵁ W) z hxW (show Γ(Z, i ⁻¹ᵁ W) from s) := by
    intro s
    have h1 : ψ (((AlgebraicGeometry.Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.germ W (i.base z) hxW s) =
        (AlgebraicGeometry.Scheme.Modules.presheaf (X := Z) (SheafOfModules.unit Z.ringCatSheaf)).germ
          (i ⁻¹ᵁ W) z hxW s :=
      TopCat.Presheaf.stalkPushforward_germ_apply AddCommGrpCat.{u} i.base
        (AlgebraicGeometry.Scheme.Modules.presheaf (X := Z) (SheafOfModules.unit Z.ringCatSheaf)) W z hxW s
    change u (ψ _) = _
    rw [h1]
    exact AlgebraicGeometry.Divisors.LineGenericCoordinates.unitStalkLinearEquiv_germ Z z (i ⁻¹ᵁ W) hxW s
  change (ψ.trans u.toAddEquiv) _ = _ • (ψ.trans u.toAddEquiv) _
  erw [key, key]
  change Z.presheaf.germ (i ⁻¹ᵁ W) z hxW
      ((show Γ(Z, i ⁻¹ᵁ W) from i.app W (X.presheaf.map (homOfLE hWV).op a)) *
        (show Γ(Z, i ⁻¹ᵁ W) from b)) =
    i.stalkMap z (X.presheaf.germ W (i.base z) hxW (X.presheaf.map (homOfLE hWV).op a)) *
      Z.presheaf.germ (i ⁻¹ᵁ W) z hxW (show Γ(Z, i ⁻¹ᵁ W) from b)
  rw [AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply]
  exact (Z.presheaf.germ (i ⁻¹ᵁ W) z hxW).hom.map_mul _ _

/-- **General form of the stalk statement.** Let `i : Z → X` be a closed immersion and `z ∈ Z` a point
whose local ring `O_{Z,z}` is a field (e.g. the generic point of an integral `Z`); put `x := i z`. Then
`m_x` kills the stalk `(i_* O_Z)_x` and `length_{O_{X,x}} (i_* O_Z)_x = 1`.

Proof: through `pushforwardUnitStalkLinearEquiv`, `(i_* O_Z)_x ≃ O_{Z,z}` `O_{X,x}`-linearly, the action
on `O_{Z,z}` being through the stalk map `i^♯_z`. This map is local (Mathlib instance) and surjective
(`Scheme.Hom.stalkMap_surjective`, closed immersions are preimmersions); a local map into a field kills the
maximal ideal, which gives the annihilator statement; `Module.length_eq_of_surjective` reduces the length to
`length_{O_{Z,z}} O_{Z,z} = 1` (a field is a simple module over itself, `isSimpleModule_self_iff_isUnit`). -/
theorem maximalIdeal_le_annihilator_and_length_pushforward_unit_stalk
    (hF : IsField (Z.presheaf.stalk z)) {x : X} (hx : i.base z = x) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≤
        Module.annihilator (X.presheaf.stalk x)
          (((AlgebraicGeometry.Scheme.Modules.pushforward i).obj
            (SheafOfModules.unit Z.ringCatSheaf)).stalk x) ∧
      Module.length (X.presheaf.stalk x)
        (((AlgebraicGeometry.Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).stalk x) = 1 := by
  subst hx
  let _ := AlgebraicGeometry.Scheme.Modules.moduleStalkModule X
    ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) (i.base z)
  let _ : Algebra (X.presheaf.stalk (i.base z)) (Z.presheaf.stalk z) := (i.stalkMap z).hom.toAlgebra
  let e := pushforwardUnitStalkLinearEquiv i z
  -- the stalk map is local and lands in a field, so it kills the maximal ideal
  have hφ : ∀ r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i.base z)), i.stalkMap z r = 0 := by
    intro r hr
    have hnu : ¬ IsUnit (i.stalkMap z r) := fun h =>
      (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal r).mp hr))
        (isUnit_of_map_unit (i.stalkMap z).hom r h)
    by_contra hne
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel hne
    exact hnu (isUnit_iff_exists_inv.mpr ⟨b, hb⟩)
  have hann : ∀ r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i.base z)),
      ∀ m : ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk (i.base z), r • m = 0 := by
    intro r hr m
    apply e.injective
    erw [e.map_smul, e.map_zero]
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    change i.stalkMap z r * e m = 0
    rw [hφ r hr, zero_mul]
  have hsurj : Function.Surjective (algebraMap (X.presheaf.stalk (i.base z)) (Z.presheaf.stalk z)) :=
    i.stalkMap_surjective z
  have hsimple : IsSimpleModule (Z.presheaf.stalk z) (Z.presheaf.stalk z) := by
    rw [isSimpleModule_self_iff_isUnit]
    refine ⟨⟨hF.exists_pair_ne⟩, fun k hk => ?_⟩
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel hk
    exact isUnit_iff_exists_inv.mpr ⟨b, hb⟩
  have hlen : Module.length (X.presheaf.stalk (i.base z))
      (((AlgebraicGeometry.Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk (i.base z)) = 1 := by
    rw [e.length_eq, Module.length_eq_of_surjective (S := X.presheaf.stalk (i.base z))
      (R := Z.presheaf.stalk z) (M := Z.presheaf.stalk z) hsurj]
    exact Module.length_eq_one (Z.presheaf.stalk z) (Z.presheaf.stalk z)
  exact ⟨fun r hr => Module.mem_annihilator.mpr (fun m => hann r hr m), hlen⟩

end StalkOfPushforwardUnit

/-- Stalk part of the generator: `m_ξ` kills the stalk of
`i_* O_{Z_ξ}` at `ξ`, and that stalk has length `1` over `O_{X,ξ}` (see the module docstring).
Instance of `maximalIdeal_le_annihilator_and_length_pushforward_unit_stalk` at the generic point `η` of the
integral scheme `Z_ξ` (`i η = ξ`, `pointClosureι_genericPoint`; `O_{Z_ξ,η}` is the function field, a field by
Mathlib's `Field X.functionField` instance for integral `X`). -/
theorem pushforward_unit_pointClosure_stalk {X : AlgebraicGeometry.Scheme.{u}} (ξ : X) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ≤
        Module.annihilator (X.presheaf.stalk ξ) ((pointClosureUnitPushforward ξ).stalk ξ) ∧
      Module.length (X.presheaf.stalk ξ) ((pointClosureUnitPushforward ξ).stalk ξ) = 1 :=
  maximalIdeal_le_annihilator_and_length_pushforward_unit_stalk (X.pointClosureι ξ)
    (genericPoint (X.pointClosure ξ)) (Field.toIsField (X.pointClosure ξ).functionField)
    (AlgebraicGeometry.Scheme.pointClosureι_genericPoint ξ)

/-- `i_* O_{Z_ξ}` is coherent on a locally Noetherian `X` (Stacks 01Y6; closed immersions are finite). -/
theorem pointClosureUnitPushforward_isCoherent {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (ξ : X) :
    (pointClosureUnitPushforward ξ).IsCoherent := by
  have hfin : AlgebraicGeometry.IsFinite (X.pointClosureι ξ) :=
    ((AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono (f := X.pointClosureι ξ)).mp
      inferInstance).1
  have hcoh : AlgebraicGeometry.Scheme.Modules.IsCoherent (X := X.pointClosure ξ)
      (SheafOfModules.unit (X.pointClosure ξ).ringCatSheaf) := by
    have hq := AlgebraicGeometry.Scheme.Modules.unit_isQuasicoherent (X.pointClosure ξ)
    rw [← AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit (X.pointClosure ξ)] at hq
    exact ⟨hq, inferInstance⟩
  exact AlgebraicGeometry.Scheme.Modules.isCoherent_pushforward_of_isFinite (X.pointClosureι ξ) _

/-- `Supp (i_* O_{Z_ξ}) = closure {ξ}` (Stacks 00AE). -/
theorem pointClosureUnitPushforward_support {X : AlgebraicGeometry.Scheme.{u}} (ξ : X) :
    (pointClosureUnitPushforward ξ).support = closure {ξ} := by
  have hrange : Set.range (X.pointClosureι ξ).base = closure {ξ} := by
    rw [MiyaokaMori.PointClosureTransport.range_eq_closure_of_isClosedImmersion (X.pointClosureι ξ),
      AlgebraicGeometry.Scheme.pointClosureι_genericPoint]
  ext η
  constructor
  · intro hη
    by_contra hnot
    rw [← hrange] at hnot
    -- Stacks 00AE: the stalk of `i_* O_Z` off the image of `i` is zero
    have hz := TopCat.Sheaf.isZero_stalk_pushforward_of_notMem_range (X.pointClosureι ξ).base
      (X.pointClosureι ξ).isClosedEmbedding
      ((SheafOfModules.toSheaf (X.pointClosure ξ).ringCatSheaf).obj
        (SheafOfModules.unit (X.pointClosure ξ).ringCatSheaf)) η hnot
    have hsub : Subsingleton ((pointClosureUnitPushforward ξ).presheaf.stalk η) :=
      AddCommGrpCat.isZero_iff_subsingleton.mp hz
    have hnt : Nontrivial ((pointClosureUnitPushforward ξ).stalk η) := hη
    exact not_nontrivial_iff_subsingleton.mpr hsub hnt
  · intro hη
    rw [← hrange] at hη
    obtain ⟨z, rfl⟩ := hη
    refine mem_support_pushforward_of_isClosedImmersion (X.pointClosureι ξ) _ ?_
    show Nontrivial (AlgebraicGeometry.Scheme.Modules.stalk (X := X.pointClosure ξ)
      (SheafOfModules.unit (X.pointClosure ξ).ringCatSheaf) z)
    let _ := AlgebraicGeometry.Scheme.Modules.moduleStalkModule (X.pointClosure ξ) (SheafOfModules.unit _) z
    exact (AlgebraicGeometry.Divisors.LineGenericCoordinates.unitStalkLinearEquiv (X.pointClosure ξ) z).toEquiv.nontrivial

end AlgebraicGeometry.Scheme.Modules

end
