import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.IsLineBundle

/-! # A pulled-back line bundle is trivial on the fibres

A line bundle pulled back from `C` restricts to a trivial line bundle on each fibre `π^{-1}(c)`
(`Q|_c` is a one-dimensional vector space over the residue field, and its pullback is `O_{π^{-1}(c)}`).

Proof route (not passing through line bundles on `Spec κ(c)`): `g := π.fiberι c ≫ π` sends every point of
the fibre to `c` (`Scheme.Hom.range_fiberι`), so the open of a local trivialization `t` of `L` at `c`
(`IsLineBundle.exists_trivialization`) pulled back along `g` (`Trivialization.pullback`) is
`g ⁻¹ᵁ t.carrier = ⊤`; then `iso_unit_of_trivialization_top` (a module restricted to `⊤` is isomorphic to
itself) gives `g^*L ≅ O`, and finally `pullbackComp` replaces `g^*L` by `(π.fiberι c)^*(π^*L)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- Pulling `M|_⊤` back along the isomorphism `Z.topIso.inv : Z ≅ ⊤` gives back `M` itself: `⊤.ι` is an
isomorphism (`Scheme.toIso_inv_ι`) and pullback is pseudofunctorial (`restrictFunctorIsoPullback`,
`pullbackComp`, `pullbackCongr`, `pullbackId`). -/
def pullbackTopIsoInvRestrictTopIso {Z : Scheme.{u}} (M : Z.Modules) :
    (pullback Z.topIso.inv).obj (M.restrict (⊤ : Z.Opens).ι) ≅ M :=
  (pullback Z.topIso.inv).mapIso ((restrictFunctorIsoPullback (⊤ : Z.Opens).ι).app M) ≪≫
    (pullbackComp Z.topIso.inv (⊤ : Z.Opens).ι).app M ≪≫
    (pullbackCongr Z.toIso_inv_ι).app M ≪≫
    (pullbackId Z).app M

/-- If the open of a trivialization is the whole space `⊤`, the module is globally isomorphic to the
structure sheaf (`M ≅ (topIso.inv)^*(M|_⊤) ≅ (topIso.inv)^*O_⊤ ≅ O_Z`). -/
theorem iso_unit_of_trivialization_top {Z : Scheme.{u}} (M : Z.Modules)
    (t : Trivialization M) (ht : t.carrier = ⊤) :
    Nonempty (M ≅ SheafOfModules.unit Z.ringCatSheaf) := by
  obtain ⟨U, e⟩ := t
  simp only at ht
  subst ht
  exact ⟨(pullbackTopIsoInvRestrictTopIso M).symm ≪≫ (pullback Z.topIso.inv).mapIso e ≪≫
    pullbackUnitIso Z.topIso.inv⟩

end AlgebraicGeometry.Scheme.Modules

/- Unbundled form (matching its use for the vanishing of pullbacks on fibres): `X`, `Y` are arbitrary
   schemes and the fibre `π.fiber c` is not a variety, so the bundled `LineBundle` (which requires a
   `Variety`) does not apply. -/

theorem AlgebraicGeometry.pullback_fiberι_pullback_iso_unit
    {X Y : AlgebraicGeometry.Scheme.{u}} (π : Y ⟶ X) (L : X.Modules) [L.IsLineBundle] (c : X) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback (π.fiberι c)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj L)
      ≅ SheafOfModules.unit (π.fiber c).ringCatSheaf) := by
  obtain ⟨t, hc⟩ := AlgebraicGeometry.Scheme.Modules.IsLineBundle.exists_trivialization L c
  have hg : ∀ y : π.fiber c, π (π.fiberι c y) = c := by
    intro y
    have : π.fiberι c y ∈ Set.range (π.fiberι c) := ⟨y, rfl⟩
    rw [π.range_fiberι c] at this
    exact this
  have htop : (t.pullback (π.fiberι c ≫ π)).carrier = ⊤ := by
    rw [AlgebraicGeometry.Scheme.Modules.Trivialization.pullback_carrier]
    ext y
    simp [hg y, hc]
  obtain ⟨e⟩ := AlgebraicGeometry.Scheme.Modules.iso_unit_of_trivialization_top _ _ htop
  exact ⟨(AlgebraicGeometry.Scheme.Modules.pullbackComp (π.fiberι c) π).app L ≪≫ e⟩

end
