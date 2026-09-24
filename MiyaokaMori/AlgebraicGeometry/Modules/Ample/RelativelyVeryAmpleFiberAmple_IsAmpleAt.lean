import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowCanonicalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorUnitIso
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveQuasiProjectiveProperSectionsGenerated
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GeneratedInDegreeOne
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSectionInPunctured
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackNotZeroAt
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01mw
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01nq
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01nr

/-! # Pointwise ampleness

Pointwise ampleness (the half of the definition of `IsAmple` without compactness) and its
transport lemmas.

`IsAmple L = CompactSpace X ∧ ∀ x, IsAmpleAt L x` (`isAmple_iff_compactSpace_isAmpleAt`, by
definition). The pointwise part is preserved under isomorphisms and under pullback along affine
morphisms; on `Proj 𝒜` covered by the `D₊(f)` (`f ∈ 𝒜 1`) the sheaf `O(1)` is pointwise ample; on a
relative Proj, `O(1)` is pointwise ample on the preimage of an affine open `V` (no finite type
hypothesis on `𝒜_1` is needed: finite type is only used for compactness).

These are the pointwise versions of `IsAmple.pullback_of_isClosedImmersion`, `IsAmple.of_iso`,
`Proj.twist_one_isAmple_of_iSup_basicOpen` and `relativeProj.isAmple_twist_one_pullback_preimage_ι`
(same proofs, without compactness), used for the ampleness of a relatively very ample line bundle
on fibres: there the compactness of the fibre comes from `π` quasi-compact, while `Proj_{κ(x)}`
itself need not be compact.

References: Stacks 01PU (ampleness pulls back along closed immersions), Stacks 01MW(5) (the
nonvanishing locus of `x_f` is `D₊(f)`), the core of Stacks 07RL.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Pointwise ampleness**: the second conjunct of the definition of `IsAmple` at a point `x`:
there are `m > 0` and a global section `s ∈ Γ(X, L^{⊗m})` with `x ∈ X_s` and `X_s` affine. -/
def AlgebraicGeometry.IsAmpleAt {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules)
    [L.IsLineBundle] (x : X) : Prop :=
  ∃ (m : ℕ) (_ : 0 < m)
    (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L m, ⊤)),
    x ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus s ∧
    AlgebraicGeometry.IsAffineOpen
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus s)

/-- `IsAmple L ↔ CompactSpace X ∧ ∀ x, IsAmpleAt L x` (by definition). -/
theorem AlgebraicGeometry.isAmple_iff_compactSpace_isAmpleAt {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    AlgebraicGeometry.IsAmple L ↔ CompactSpace X ∧ ∀ x : X, AlgebraicGeometry.IsAmpleAt L x :=
  Iff.rfl

/-- Pointwise ampleness transports along isomorphisms of line bundles (the pointwise version of
`IsAmple.of_iso`: transport the section along `tensorPowMapIso e m`; the nonvanishing locus is
unchanged). -/
theorem AlgebraicGeometry.IsAmpleAt.of_iso {X : AlgebraicGeometry.Scheme.{u}} {L L' : X.Modules}
    [L.IsLineBundle] [L'.IsLineBundle] (e : L ≅ L') {x : X}
    (h : AlgebraicGeometry.IsAmpleAt L x) : AlgebraicGeometry.IsAmpleAt L' x := by
  obtain ⟨m, hm, s, hxs, haff⟩ := h
  refine ⟨m, hm,
    (AlgebraicGeometry.Scheme.Modules.tensorPowMapIso e m).hom.app ⊤ s, ?_, ?_⟩
  · exact (AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_iso
      (AlgebraicGeometry.Scheme.Modules.tensorPowMapIso e m) s x).mpr hxs
  · rw [AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso]
    exact haff

/-- **Pointwise ampleness pulls back along affine morphisms** (the pointwise, affine-morphism
version of Stacks 01PU): if `g : Z → X` is affine and `L` is pointwise ample at `g z`, then `g^*L`
is pointwise ample at `z`. Proof: take `m` and `s ∈ Γ(L^{⊗m})` with `g z ∈ X_s` affine; for
`t := θ(g^*s) ∈ Γ((g^*L)^{⊗m})` (`θ = pullbackTensorPowIso g L m`) one has `Z_t = g⁻¹(X_s)`
(`sectionPullbackAlong` vanishes at `z` iff `s` vanishes at `g z`), which contains `z` and is affine
because preimages of affine opens under affine morphisms are affine (`IsAffineOpen.preimage`). -/
theorem AlgebraicGeometry.IsAmpleAt.pullback_of_isAffineHom {Z X : AlgebraicGeometry.Scheme.{u}}
    (g : Z ⟶ X) [AlgebraicGeometry.IsAffineHom g] (L : X.Modules) [L.IsLineBundle] {z : Z}
    (hL : AlgebraicGeometry.IsAmpleAt L (g.base z)) :
    AlgebraicGeometry.IsAmpleAt ((AlgebraicGeometry.Scheme.Modules.pullback g).obj L) z := by
  obtain ⟨m, hm, sΓ, hzs, hsa⟩ := hL
  letI hpow_m : (AlgebraicGeometry.Scheme.Modules.tensorPow L m).IsLineBundle :=
    SheafOfModules.IsLineBundle.tensorPow L m
  letI hpull : ((AlgebraicGeometry.Scheme.Modules.pullback g).obj L).IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback g L
  letI hpull_pow :
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj
        (AlgebraicGeometry.Scheme.Modules.tensorPow L m)).IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback g
      (AlgebraicGeometry.Scheme.Modules.tensorPow L m)
  letI hpull_mpow :
      (AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback g).obj L) m).IsLineBundle :=
    SheafOfModules.IsLineBundle.tensorPow
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj L) m
  let s : ((AlgebraicGeometry.Scheme.Modules.tensorPow L m).val.obj
      (Opposite.op ⊤) : Type u) := by
    change Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L m, ⊤)
    exact sΓ
  have hs_nonzero : ¬ IsZeroAt s (g.base z) := by
    have hiff : ¬ IsZeroAt s (g.base z) ↔
        g.base z ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus sΓ := by
      rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus]
      rfl
    exact hiff.mpr hzs
  let θ := AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso g L m
  let u : Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj
      (AlgebraicGeometry.Scheme.Modules.tensorPow L m), ⊤) := by
    change (((AlgebraicGeometry.Scheme.Modules.pullback g).obj
      (AlgebraicGeometry.Scheme.Modules.tensorPow L m)).val.obj
      (Opposite.op ⊤) : Type u)
    exact sectionPullbackAlong g s
  let t := θ.hom.app ⊤ u
  have hzt : z ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj L) m).nonvanishingLocus t := by
    dsimp [t]
    rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_iso θ]
    rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus]
    change ¬ IsZeroAt (sectionPullbackAlong g s) z
    exact not_isZeroAt_sectionPullbackAlong g (AlgebraicGeometry.Scheme.Modules.tensorPow L m) s z
      hs_nonzero
  have hloc : (AlgebraicGeometry.Scheme.Modules.tensorPow
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj L) m).nonvanishingLocus t =
      g ⁻¹ᵁ (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus sΓ := by
    ext z'
    change z' ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj L) m).nonvanishingLocus
        (θ.hom.app ⊤ u) ↔ g.base z' ∈
      (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus sΓ
    rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_iso θ]
    rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus,
      AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus]
    change ¬ IsZeroAt (sectionPullbackAlong g s) z' ↔ ¬ IsZeroAt s (g.base z')
    constructor
    · intro h hz
      exact h (isZeroAt_sectionPullbackAlong_of_isZeroAt g
        (AlgebraicGeometry.Scheme.Modules.tensorPow L m) s z' hz)
    · intro h
      exact not_isZeroAt_sectionPullbackAlong g
        (AlgebraicGeometry.Scheme.Modules.tensorPow L m) s z' h
  refine ⟨m, hm, t, hzt, ?_⟩
  rw [hloc]
  exact hsa.preimage g

/-- **`O(1)` on `Proj 𝒜` is pointwise ample** (the pointwise form of Stacks 01MW(5)): if `Proj 𝒜`
is covered by the `D₊(f)` (`f ∈ 𝒜 1`), then `O(1)` is pointwise ample at every point: take
`f ∈ 𝒜 1` with `x ∈ D₊(f)`; the nonvanishing locus of `x_f ∈ Γ(O(1))` (`Proj.twistSection`) is
exactly `D₊(f)`, which is affine (`Proj.isAffineOpen_basicOpen`); take `m = 1` and transport along
`O(1)^{⊗1} ≅ O(1)` (`unitTensorIso`). -/
theorem AlgebraicGeometry.Proj.twist_one_isAmpleAt_of_iSup_basicOpen {σ A : Type u} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (hcover : ⨆ f : 𝒜 1, AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) = ⊤)
    [(AlgebraicGeometry.Proj.twist 𝒜 1).IsLineBundle] (x : AlgebraicGeometry.Proj 𝒜) :
    AlgebraicGeometry.IsAmpleAt (AlgebraicGeometry.Proj.twist 𝒜 1) x := by
  obtain ⟨f, hf⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover.ge (Set.mem_univ x))
  let L : (AlgebraicGeometry.Proj 𝒜).Modules := AlgebraicGeometry.Proj.twist 𝒜 1
  let e1 : AlgebraicGeometry.Scheme.Modules.tensorPow L 1 ≅ L := by
    change AlgebraicGeometry.Scheme.Modules.tensor
      (SheafOfModules.unit (AlgebraicGeometry.Proj 𝒜).ringCatSheaf) L ≅ L
    exact AlgebraicGeometry.Scheme.Modules.unitTensorIso L
  let s : Γ(L, ⊤) := AlgebraicGeometry.Proj.twistSection 𝒜 (f : A) f.2
  let s1 : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L 1, ⊤) := e1.inv.app ⊤ s
  have he1 : e1.hom.app ⊤ s1 = s := by
    dsimp only [s1]
    have hh := e1.inv_hom_id
    have hh' := congrArg (fun q => q.val.app (Opposite.op ⊤)) hh
    exact congrArg (fun q => q.hom s) hh'
  have hloc : L.nonvanishingLocus s = AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) := by
    ext y
    change y ∈ L.nonvanishingLocus s ↔ y ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)
    rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus]
    change ¬ IsZeroAt (AlgebraicGeometry.Proj.twistSection 𝒜 (f : A) f.2) y ↔ _
    exact AlgebraicGeometry.Proj.not_isZeroAt_twistSection_iff_of_iSup_basicOpen_eq_top 𝒜 (f : A) f.2
      hcover y
  refine ⟨1, Nat.one_pos, s1, ?_, ?_⟩
  · rw [← AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_iso e1 s1 x, he1, hloc]
    exact hf
  · rw [← AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso e1 s1, he1, hloc]
    exact AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒜 (f : A) f.2 Nat.one_pos

/-- When `𝒜` is generated in degree one, the `D₊(f)` (`f ∈ Γ(V,𝒜)_1`) cover `Proj Γ(V,𝒜)`
(`Proj.iSup_basicOpen_eq_top'`). -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.iSup_basicOpen_sectionsGrading_one_eq_top
    {X : AlgebraicGeometry.Scheme.{u}} (𝒜 : X.GradedQCAlgebra) (h𝒜 : 𝒜.GeneratedInDegreeOne)
    (V : X.affineOpens) :
    ⨆ f : 𝒜.sectionsGrading V.1 1,
      AlgebraicGeometry.Proj.basicOpen (𝒜.sectionsGrading V.1) (f : 𝒜.sectionsRing V.1) = ⊤ := by
  have hrange : Set.range (fun f : 𝒜.sectionsGrading V.1 1 => (f : 𝒜.sectionsRing V.1)) =
      ((𝒜.sectionsGrading V.1 1 : AddSubgroup (𝒜.sectionsRing V.1)) : Set (𝒜.sectionsRing V.1)) :=
    Subtype.range_coe
  apply AlgebraicGeometry.Proj.iSup_basicOpen_eq_top' (𝒜.sectionsGrading V.1)
    (fun f : 𝒜.sectionsGrading V.1 1 => (f : 𝒜.sectionsRing V.1)) (fun f => ⟨1, f.2⟩)
  rw [hrange]
  exact 𝒜.adjoin_sectionsGrading_one_eq_top h𝒜 V

/-- When `𝒜` is generated in degree one, `O(1)|_{π⁻¹V}` (the pullback along the open immersion
`(π⁻¹V).ι`) is a line bundle: transport along `φ_V : π⁻¹V ≅ Proj Γ(V,𝒜)` (Stacks 01NQ) and
`O(1)|_{π⁻¹V} ≅ φ_V^* O_{Proj}(1)` (Stacks 01NR); `O_{Proj}(1)` is a line bundle
(`Proj.twist_isLineBundle`, from the cover). (Same source as `twist_restrict_isLineBundle_of_affine`,
but without `irrelevant_le_span_degOne`.) -/
theorem AlgebraicGeometry.Scheme.relativeProj.isLineBundle_pullback_twist_one_preimage_ι
    {X : AlgebraicGeometry.Scheme.{u}} (𝒜 : X.GradedQCAlgebra) (h𝒜 : 𝒜.GeneratedInDegreeOne)
    (V : X.affineOpens) :
    ((AlgebraicGeometry.Scheme.Modules.pullback
        ((AlgebraicGeometry.Scheme.relativeProj 𝒜).hom ⁻¹ᵁ V.1).ι).obj
      (AlgebraicGeometry.Scheme.relativeProj.twist 𝒜 1)).IsLineBundle := by
  have hcover := 𝒜.iSup_basicOpen_sectionsGrading_one_eq_top h𝒜 V
  haveI : (AlgebraicGeometry.Proj.twist (𝒜.sectionsGrading V.1) 1).IsLineBundle :=
    AlgebraicGeometry.Proj.twist_isLineBundle (𝒜.sectionsGrading V.1)
      (fun f : 𝒜.sectionsGrading V.1 1 => (f : 𝒜.sectionsRing V.1)) (fun f => f.2) hcover 1
  haveI h3 : ((AlgebraicGeometry.Scheme.relativeProj.twist 𝒜 1).restrict
      ((AlgebraicGeometry.Scheme.relativeProj 𝒜).hom ⁻¹ᵁ V.1).ι).IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.of_iso
      (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso 𝒜 V 1).symm
  exact AlgebraicGeometry.Scheme.Modules.IsLineBundle.of_iso
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback
      ((AlgebraicGeometry.Scheme.relativeProj 𝒜).hom ⁻¹ᵁ V.1).ι).app
      (AlgebraicGeometry.Scheme.relativeProj.twist 𝒜 1))

/-- **`O(1)` on a relative Proj is pointwise ample on the preimage of an affine open `V ⊆ X`** (the
pointwise version of `isAmple_twist_one_pullback_preimage_ι`, without finite type of `𝒜_1`):
`π⁻¹V ≅ Proj A` with `A = Γ(V,𝒜)` (Stacks 01NQ), `O(1)|_{π⁻¹V}` corresponds to `O_{Proj A}(1)`
(Stacks 01NR); `A` generated by `A_1` ⇒ the `D₊(f)` cover `Proj A` ⇒ `O_{Proj A}(1)` is pointwise
ample (`twist_one_isAmpleAt_of_iSup_basicOpen`); pull back along the isomorphism (an affine
morphism) and transport along the isomorphism of module sheaves. -/
theorem AlgebraicGeometry.Scheme.relativeProj.isAmpleAt_twist_one_pullback_preimage_ι
    {X : AlgebraicGeometry.Scheme.{u}} (𝒜 : X.GradedQCAlgebra) (h𝒜 : 𝒜.GeneratedInDegreeOne)
    (V : X.affineOpens)
    [((AlgebraicGeometry.Scheme.Modules.pullback
        ((AlgebraicGeometry.Scheme.relativeProj 𝒜).hom ⁻¹ᵁ V.1).ι).obj
      (AlgebraicGeometry.Scheme.relativeProj.twist 𝒜 1)).IsLineBundle]
    (z : ((AlgebraicGeometry.Scheme.relativeProj 𝒜).hom ⁻¹ᵁ V.1).toScheme) :
    AlgebraicGeometry.IsAmpleAt
      ((AlgebraicGeometry.Scheme.Modules.pullback
        ((AlgebraicGeometry.Scheme.relativeProj 𝒜).hom ⁻¹ᵁ V.1).ι).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist 𝒜 1)) z := by
  have hcover := 𝒜.iSup_basicOpen_sectionsGrading_one_eq_top h𝒜 V
  haveI : (AlgebraicGeometry.Proj.twist (𝒜.sectionsGrading V.1) 1).IsLineBundle :=
    AlgebraicGeometry.Proj.twist_isLineBundle (𝒜.sectionsGrading V.1)
      (fun f : 𝒜.sectionsGrading V.1 1 => (f : 𝒜.sectionsRing V.1)) (fun f => f.2) hcover 1
  have h1 : AlgebraicGeometry.IsAmpleAt (AlgebraicGeometry.Proj.twist (𝒜.sectionsGrading V.1) 1)
      ((AlgebraicGeometry.Scheme.relativeProj.affineIso 𝒜 V).hom.base z) :=
    AlgebraicGeometry.Proj.twist_one_isAmpleAt_of_iSup_basicOpen (𝒜.sectionsGrading V.1) hcover _
  have h2 := h1.pullback_of_isAffineHom (AlgebraicGeometry.Scheme.relativeProj.affineIso 𝒜 V).hom _
  haveI h3i : ((AlgebraicGeometry.Scheme.relativeProj.twist 𝒜 1).restrict
      ((AlgebraicGeometry.Scheme.relativeProj 𝒜).hom ⁻¹ᵁ V.1).ι).IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.of_iso
      (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso 𝒜 V 1).symm
  have h3 : AlgebraicGeometry.IsAmpleAt
      ((AlgebraicGeometry.Scheme.relativeProj.twist 𝒜 1).restrict
        ((AlgebraicGeometry.Scheme.relativeProj 𝒜).hom ⁻¹ᵁ V.1).ι) z :=
    AlgebraicGeometry.IsAmpleAt.of_iso (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso 𝒜 V 1).symm h2
  exact AlgebraicGeometry.IsAmpleAt.of_iso
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback
      ((AlgebraicGeometry.Scheme.relativeProj 𝒜).hom ⁻¹ᵁ V.1).ι).app
      (AlgebraicGeometry.Scheme.relativeProj.twist 𝒜 1)) h3

end
