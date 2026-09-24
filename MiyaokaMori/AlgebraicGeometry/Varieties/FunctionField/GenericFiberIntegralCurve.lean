import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.GenericFiberStalkIso
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.DimensionFiniteness
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0a216

/-! # The generic fibre of a dominant proper morphism of varieties

The fibre `W_η` of a dominant proper `k`-morphism `p : W → W′` over the generic point `η` of `W′`
is a proper integral scheme over `κ(η)`, locally Noetherian, of dimension `dim W − dim W′`; the
image of the fibre inclusion is exactly `p⁻¹{η}`, and the inclusion induces stalk isomorphisms
`O_{W,ι(ξ)} ≅ O_{W_η,ξ}` at every point (`W_η = W ×_{W′} Spec O_{W′,η}` is a "localization" of `W`),
so in particular the function fields agree, `R(W_η) = R(W)`.

Sources: Stacks 02R5, 02RM, 02RH, 02RT, 02S2.

Proof sketch:

1. Image of the fibre inclusion: Mathlib `Scheme.Hom.range_fiberι`.
2. Stalk isomorphisms: `Spec κ(η) → W'` is flat at the generic point (`κ(η) = 𝒪_{W',η}`, and
   `Spec 𝒪_{Y,y} → Y` is a localisation), so the fibre inclusion is flat (base change) and a
   preimmersion (Mathlib); a flat local homomorphism of local rings is faithfully flat, hence
   injective, and surjective by preimmersion — `GenericFiberStalkIso.lean`.
3. Integrality: irreducible because the underlying set `p⁻¹{η}` contains the generic point `ξ₀` of
   `W` and lies inside `closure {ξ₀}`; reduced because its stalks are stalks of `W`.
4. Locally Noetherian: `W_η → Spec κ(η)` is locally of finite type over a field
   (Mathlib `LocallyOfFiniteType.isLocallyNoetherian`), instead of "localisation of Noetherian".
5. Dimension: Stacks 0A21(6) for `W_η` over `κ(η)` (`topologicalKrullDim_eq_trdeg_functionField`,
   `Stacks0a216.lean`) gives `dim W_η = trdeg_{κ(η)} R(W_η)`; `R(W_η) ≅ R(W)` by (2) at the
   generic point of `W_η` (which maps to `ξ₀`), compatibly with the structure maps
   (`fiber_appTop_comm`); the tower `trdeg_k κ(η) + trdeg_{κ(η)} R(W) = trdeg_k R(W)`
   (Stacks 030H, Mathlib `trdeg_add_eq`) with `trdeg_k κ(η) = trdeg_k R(W') = dim W'` and
   `trdeg_k R(W) = dim W` (Stacks 0A21(6) for `W`, `W'`; finiteness from
   `Variety.topologicalKrullDim_eq_trdeg`).
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
/-- Dimension of the generic fibre: `dim W_η = dim W - dim W'` (as a `WithBot ℕ∞`), for a
dominant morphism of `k`-varieties locally of finite type. Proof: Stacks 0A21(6) for `W_η` over
`κ(η)`, the identification `R(W_η) ≅ R(W)` through the stalk isomorphism at the generic point, and
the transcendence-degree tower `trdeg_k κ(η) + trdeg_{κ(η)} R(W) = trdeg_k R(W)` (Stacks 030H)
with `trdeg_k κ(η) = trdeg_k R(W') = dim W'`, `trdeg_k R(W) = dim W`. -/
theorem genericFiber_topologicalKrullDim {k : Type u} [Field k] {W W' : Variety k}
    (p : W.toScheme ⟶ W'.toScheme) [p.IsOver (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType p]
    (hp : p.base (genericPoint W.toScheme) = genericPoint W'.toScheme) :
    topologicalKrullDim (p.fiber (genericPoint W'.toScheme))
      = ((W.toScheme.dimension - W'.toScheme.dimension : ℕ) : WithBot ℕ∞) := by
  haveI hF : IsIntegral (p.fiber (genericPoint W'.toScheme)) := isIntegral_fiber_genericPoint p hp
  letI : (p.fiber (genericPoint W'.toScheme)).Over
      (Spec (CommRingCat.of (W'.toScheme.residueField (genericPoint W'.toScheme)))) :=
    ⟨p.fiberToSpecResidueField (genericPoint W'.toScheme)⟩
  haveI hFT : LocallyOfFiniteType ((p.fiber (genericPoint W'.toScheme)) ↘
      Spec (CommRingCat.of (W'.toScheme.residueField (genericPoint W'.toScheme)))) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd p _))
  have hdimF := topologicalKrullDim_eq_trdeg_functionField
    (k := W'.toScheme.residueField (genericPoint W'.toScheme)) (p.fiber (genericPoint W'.toScheme))
  have hdimW := topologicalKrullDim_eq_trdeg_functionField (k := k) W.toScheme
  have hdimW' := topologicalKrullDim_eq_trdeg_functionField (k := k) W'.toScheme
  have hWtop := (Variety.topologicalKrullDim_eq_trdeg W).2
  have hW'top := (Variety.topologicalKrullDim_eq_trdeg W').2
  -- (statements are already zeta-reduced)
  -- the algebra structures
  letI algWk : Algebra k W.toScheme.functionField :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (W.toScheme ↘ Spec (CommRingCat.of k)).appTop ≫
      W.toScheme.presheaf.germ ⊤ (genericPoint W.toScheme) trivial).hom.toAlgebra
  letI algW'k : Algebra k W'.toScheme.functionField :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (W'.toScheme ↘ Spec (CommRingCat.of k)).appTop ≫
      W'.toScheme.presheaf.germ ⊤ (genericPoint W'.toScheme) trivial).hom.toAlgebra
  letI algκk : Algebra k (W'.toScheme.residueField (genericPoint W'.toScheme)) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (W'.toScheme ↘ Spec (CommRingCat.of k)).appTop ≫
      W'.toScheme.presheaf.germ ⊤ (genericPoint W'.toScheme) trivial ≫
      W'.toScheme.residue (genericPoint W'.toScheme)).hom.toAlgebra
  letI algFκ : Algebra (W'.toScheme.residueField (genericPoint W'.toScheme))
      (p.fiber (genericPoint W'.toScheme)).functionField :=
    ((Scheme.ΓSpecIso (CommRingCat.of (W'.toScheme.residueField (genericPoint W'.toScheme)))).inv ≫
      ((p.fiber (genericPoint W'.toScheme)) ↘
        Spec (CommRingCat.of (W'.toScheme.residueField (genericPoint W'.toScheme)))).appTop ≫
      (p.fiber (genericPoint W'.toScheme)).presheaf.germ ⊤
        (genericPoint (p.fiber (genericPoint W'.toScheme))) trivial).hom.toAlgebra
  letI algFk : Algebra k (p.fiber (genericPoint W'.toScheme)).functionField :=
    ((algebraMap (W'.toScheme.residueField (genericPoint W'.toScheme))
      (p.fiber (genericPoint W'.toScheme)).functionField).comp
        (algebraMap k (W'.toScheme.residueField (genericPoint W'.toScheme)))).toAlgebra
  haveI : IsScalarTower k (W'.toScheme.residueField (genericPoint W'.toScheme))
      (p.fiber (genericPoint W'.toScheme)).functionField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FaithfulSMul k (W'.toScheme.residueField (genericPoint W'.toScheme)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap k (W'.toScheme.residueField (genericPoint W'.toScheme))).injective
  haveI : FaithfulSMul (W'.toScheme.residueField (genericPoint W'.toScheme))
      (p.fiber (genericPoint W'.toScheme)).functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap (W'.toScheme.residueField (genericPoint W'.toScheme))
        (p.fiber (genericPoint W'.toScheme)).functionField).injective
  -- the function field of the fibre is the function field of `W`
  have hξ := fiberι_genericPoint_eq p (genericPoint W'.toScheme) hp
  haveI := isIso_stalkMap_fiberι_genericPoint p (genericPoint (p.fiber (genericPoint W'.toScheme)))
  let e : W.toScheme.functionField ≅ (p.fiber (genericPoint W'.toScheme)).functionField :=
    W.toScheme.presheaf.stalkCongr (Inseparable.of_eq hξ.symm) ≪≫
      asIso ((p.fiberι (genericPoint W'.toScheme)).stalkMap
        (genericPoint (p.fiber (genericPoint W'.toScheme))))
  have hcomm : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (W.toScheme ↘ Spec (CommRingCat.of k)).appTop ≫
      W.toScheme.presheaf.germ ⊤ (genericPoint W.toScheme) trivial ≫ e.hom =
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (W'.toScheme ↘ Spec (CommRingCat.of k)).appTop ≫
      W'.toScheme.presheaf.germ ⊤ (genericPoint W'.toScheme) trivial ≫
      W'.toScheme.residue (genericPoint W'.toScheme) ≫
      (Scheme.ΓSpecIso (W'.toScheme.residueField (genericPoint W'.toScheme))).inv ≫
      (p.fiberToSpecResidueField (genericPoint W'.toScheme)).appTop ≫
      (p.fiber (genericPoint W'.toScheme)).presheaf.germ ⊤
        (genericPoint (p.fiber (genericPoint W'.toScheme))) trivial := by
    rw [← fiber_appTop_comm p (genericPoint W'.toScheme)]
    simp only [e, Iso.trans_hom, asIso_hom, TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.germ_stalkSpecializes_assoc]
  let eW : W.toScheme.functionField ≃ₐ[k] (p.fiber (genericPoint W'.toScheme)).functionField :=
    AlgEquiv.ofRingEquiv (f := e.commRingCatIsoToRingEquiv) (fun a => by
      have := congrArg (fun g => g.hom a) hcomm
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      exact this)
  let eW' : W'.toScheme.functionField ≃ₐ[k] W'.toScheme.residueField (genericPoint W'.toScheme) :=
    AlgEquiv.ofRingEquiv
      (f := (Scheme.functionFieldIsoResidueField W'.toScheme).commRingCatIsoToRingEquiv)
      (fun a => rfl)
  have htower := trdeg_add_eq k (W'.toScheme.residueField (genericPoint W'.toScheme))
    (A := (p.fiber (genericPoint W'.toScheme)).functionField)
  have hW := eW.trdeg_eq
  have hW' := eW'.trdeg_eq
  -- finiteness
  have hWfin : Algebra.trdeg k W.toScheme.functionField < Cardinal.aleph0 := by
    rw [← Cardinal.toENat_ne_top]
    intro h
    apply hWtop
    rw [hdimW, h]
    rfl
  have hW'fin : Algebra.trdeg k W'.toScheme.functionField < Cardinal.aleph0 := by
    rw [← Cardinal.toENat_ne_top]
    intro h
    apply hW'top
    rw [hdimW', h]
    rfl
  obtain ⟨nW, hnW⟩ := Cardinal.lt_aleph0.mp hWfin
  obtain ⟨nW', hnW'⟩ := Cardinal.lt_aleph0.mp hW'fin
  have hdW : W.toScheme.dimension = nW := by
    unfold Scheme.dimension
    rw [hdimW, hnW, Cardinal.toENat_nat]
    simp
  have hdW' : W'.toScheme.dimension = nW' := by
    unfold Scheme.dimension
    rw [hdimW', hnW', Cardinal.toENat_nat]
    simp
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Algebra.trdeg (W'.toScheme.residueField (genericPoint W'.toScheme))
      (p.fiber (genericPoint W'.toScheme)).functionField = m := by
    apply Cardinal.lt_aleph0.mp
    calc Algebra.trdeg (W'.toScheme.residueField (genericPoint W'.toScheme))
          (p.fiber (genericPoint W'.toScheme)).functionField
        ≤ Algebra.trdeg k (W'.toScheme.residueField (genericPoint W'.toScheme)) +
          Algebra.trdeg (W'.toScheme.residueField (genericPoint W'.toScheme))
            (p.fiber (genericPoint W'.toScheme)).functionField := le_add_self
      _ = Algebra.trdeg k W.toScheme.functionField := by rw [htower, hW]
      _ = nW := hnW
      _ < Cardinal.aleph0 := Cardinal.natCast_lt_aleph0
  have hsum : ((nW' : Cardinal.{u}) + m : Cardinal.{u}) = nW := by
    rw [← hnW', ← hm, hW', htower, ← hW, hnW]
  have hsum' : nW' + m = nW := by exact_mod_cast hsum
  rw [hdimF, hm, Cardinal.toENat_nat, hdW, hdW']
  have : m = nW - nW' := by omega
  rw [this]
  rfl

end AlgebraicGeometry

/-- The generic fibre of a proper dominant morphism of
`k`-varieties is an integral, locally Noetherian scheme of dimension `dim W - dim W'`, its
underlying set is `p⁻¹{η}`, and the fibre inclusion induces isomorphisms on all stalks. -/
theorem AlgebraicGeometry.genericFiber_structure {k : Type u} [Field k] {W W' : Variety k}
    (p : W.toScheme ⟶ W'.toScheme) [p.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsProper p]
    (hp : p.base (genericPoint W.toScheme) = genericPoint W'.toScheme) :
    AlgebraicGeometry.IsIntegral (p.fiber (genericPoint W'.toScheme)) ∧
    AlgebraicGeometry.IsLocallyNoetherian (p.fiber (genericPoint W'.toScheme)) ∧
    topologicalKrullDim (p.fiber (genericPoint W'.toScheme))
      = ((W.toScheme.dimension - W'.toScheme.dimension : ℕ) : WithBot ℕ∞) ∧
    Set.range (p.fiberι (genericPoint W'.toScheme)).base = p.base ⁻¹' {genericPoint W'.toScheme} ∧
    ∀ ξ : p.fiber (genericPoint W'.toScheme),
      CategoryTheory.IsIso ((p.fiberι (genericPoint W'.toScheme)).stalkMap ξ) :=
  ⟨isIntegral_fiber_genericPoint p hp, isLocallyNoetherian_fiber p _,
    genericFiber_topologicalKrullDim p hp, Scheme.Hom.range_fiberι p _,
    fun ξ => isIso_stalkMap_fiberι_genericPoint p ξ⟩

end
