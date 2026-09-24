import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupHomRestrictIsoOfDisjointSupport
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SurfaceVanishingIdealPointNeBot
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks02nd
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks02ns
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01wc
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0a213

/-! # The blowup of a surface at a point has dimension two

`dim Bl_p S = 2` (the dimension step in showing that the blowup of a smooth projective surface at
a closed point is again a smooth projective surface).

Sources: Stacks 0807, 02OS (1) (a blowup is an isomorphism away from the centre); Hartshorne
II.7.16 (b) (a blowup is birational).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The topological Krull dimension of `Bl_p S` is `2`.

Proof: `π : Bl_p S → S` is an isomorphism over `S ∖ {p}` (`𝓘_p` is the unit ideal sheaf there,
`Scheme.blowup_hom_restrict_isIso_of_disjoint_support` with `coe_support_vanishingIdeal` giving
`supp 𝓘_p = {p}`), so the open `U := π⁻¹(S ∖ {p})` is homeomorphic to `S ∖ {p}`. `Bl_p S` is
integral (`Scheme.blowup_isIntegral`, Stacks 02ND, with
`SmoothProjectiveSurface.vanishingIdeal_closedPoint_ne_bot`), hence irreducible, and `U` is
nonempty (since `dim S = 2 > 0`) hence dense. `Bl_p S` is locally of finite type over `k` (the
structure morphism is `π ≫ (S ↘ Spec k)` with `π` projective, hence proper). The dimension of an
irreducible scheme locally of finite type over a field can be computed on any nonempty open
(`topologicalKrullDim_opens_eq_of_irreducible`, Stacks 0A21 (3)), applied to `Bl_p S ⊇ π⁻¹U` and to
`S ⊇ U`; `π⁻¹U ≅ U` gives equal `topologicalKrullDim` (`IsHomeomorph.topologicalKrullDim_eq`), and
`dim S = 2` (`S.dim_eq_two` with `Variety.dim_spec`). Hence `dim Bl_p S = 2`.

The conclusion is stated as `topologicalKrullDim … = (2 : WithBot ℕ∞)`; `Variety.dim = 2` follows
directly from the definition of `Variety.dim` (`(·.unbotD 0).toNat`). -/
theorem AlgebraicGeometry.Scheme.blowupClosedPoint_topologicalKrullDim {k : Type u} [Field k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    topologicalKrullDim
      (AlgebraicGeometry.Scheme.blowup
        (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).left.carrier = 2 := by
  set I : S.toScheme.IdealSheafData :=
    AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩ with hI
  set X : AlgebraicGeometry.Scheme.{u} := (AlgebraicGeometry.Scheme.blowup I).left with hX
  set π : X ⟶ S.toScheme := (AlgebraicGeometry.Scheme.blowup I).hom with hπ
  -- dim S = 2
  have hS : topologicalKrullDim S.toScheme = 2 := by
    rw [Variety.dim_spec S.toVariety, S.dim_eq_two]
    rfl
  have : AlgebraicGeometry.IsIntegral S.toScheme := inferInstance
  have : IrreducibleSpace S.toScheme := inferInstance
  -- Bl_p S is integral (Stacks 02ND), hence irreducible
  have hint : AlgebraicGeometry.IsIntegral X :=
    AlgebraicGeometry.Scheme.blowup_isIntegral I (S.vanishingIdeal_closedPoint_ne_bot p hp)
  have : IrreducibleSpace X := inferInstance
  -- k-structure on Bl_p S, locally of finite type
  have : AlgebraicGeometry.IsNoetherian S.toScheme :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  have : AlgebraicGeometry.IsProjectiveMorphism π :=
    AlgebraicGeometry.Scheme.blowup_isProjectiveMorphism I
  have : AlgebraicGeometry.IsProper π := AlgebraicGeometry.IsProjectiveMorphism.isProper π
  let _ : X.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨π ≫ (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have : AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    show AlgebraicGeometry.LocallyOfFiniteType
      (π ≫ (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    infer_instance
  -- the open U = S ∖ {p} and its preimage V
  let U : S.toScheme.Opens := ⟨{p}ᶜ, hp.isOpen_compl⟩
  have hU : (U : Set S.toScheme).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hss : Subsingleton S.toScheme := ⟨fun a b => by
      have ha : a ∈ ({p} : Set S.toScheme) := by
        by_contra h
        have : a ∈ (U : Set S.toScheme) := h
        rw [hemp] at this
        exact this
      have hb : b ∈ ({p} : Set S.toScheme) := by
        by_contra h
        have : b ∈ (U : Set S.toScheme) := h
        rw [hemp] at this
        exact this
      rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]⟩
    have hsub : Subsingleton (IrreducibleCloseds S.toScheme) := ⟨fun s t => by
      ext x
      obtain ⟨y, hy⟩ := s.isIrreducible.nonempty
      obtain ⟨z, hz⟩ := t.isIrreducible.nonempty
      exact ⟨fun _ => Subsingleton.elim z x ▸ hz, fun _ => Subsingleton.elim y x ▸ hy⟩⟩
    have hle : topologicalKrullDim S.toScheme ≤ 0 := Order.krullDim_nonpos_of_subsingleton
    rw [hS] at hle
    exact absurd hle (by decide)
  have hdisj : Disjoint (U : Set S.toScheme) (I.support : Set S.toScheme) := by
    rw [hI, AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact Set.disjoint_singleton_right.mpr (fun h => h rfl)
  have hiso : IsIso (π ∣_ U) :=
    AlgebraicGeometry.Scheme.blowup_hom_restrict_isIso_of_disjoint_support I U hdisj
  have hV : ((π ⁻¹ᵁ U : X.Opens) : Set X).Nonempty := by
    obtain ⟨y, hy⟩ := hU
    obtain ⟨z, hz⟩ := (π ∣_ U).surjective ⟨y, hy⟩
    exact ⟨((π ⁻¹ᵁ U).ι z), z.2⟩
  -- dimensions of the opens
  have h1 : topologicalKrullDim (π ⁻¹ᵁ U) = topologicalKrullDim X :=
    AlgebraicGeometry.topologicalKrullDim_opens_eq_of_irreducible (k := k) X (π ⁻¹ᵁ U) hV
  have h2 : topologicalKrullDim U = topologicalKrullDim S.toScheme :=
    AlgebraicGeometry.topologicalKrullDim_opens_eq_of_irreducible (k := k) S.toScheme U hU
  have h3 : topologicalKrullDim (π ⁻¹ᵁ U) = topologicalKrullDim U :=
    IsHomeomorph.topologicalKrullDim_eq _
      (AlgebraicGeometry.Scheme.homeoOfIso (asIso (π ∣_ U))).isHomeomorph
  rw [← h1, h3, h2, hS]

end
