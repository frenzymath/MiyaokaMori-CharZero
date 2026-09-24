import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.ModulesAssociatedPoints
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.EmbeddedPartCoherent

/-! # Removing embedded points (Stacks 02OL)

On a locally Noetherian scheme, a coherent sheaf `F` has a largest coherent subsheaf `K` whose support
is nowhere dense in `Supp F`; `F' = F/K` has the same support as `F` and no embedded associated points.

Source: Stacks 02OL.

**Proof.** Instead of gluing Stacks 02M6's `K(M)` over an affine cover, the subsheaf
`K := embeddedPart F` is defined directly on `X` as the sheaf of sections whose germs vanish at all
generic points of `Supp F` (`EmbeddedPartSubsheaf`; on `Spec A` this is exactly 02M6's
`K(M) = {m | m ↦ 0 in M_q for all minimal q ∈ Supp M}`), and all properties are proved stalkwise:

* `K` is coherent: `EmbeddedPartCoherent` (affine-local quasi-coherence criterion + Stacks 01Y1);
* (a) `Supp K` is nowhere dense in `Supp F` (`isNowhereDense_support_embeddedPart`): `Supp K` is
  closed (Stacks 01B4) and contains no generic point of `Supp F` (`K_y = 0` there), while every
  nonempty open subset of `Supp F` contains a generic point (every point is a specialization of one);
* (b) `Supp (F/K) = Supp F` (`support_cokernel_embeddedPart_ι`): `F_x → (F/K)_x` is surjective
  (the stalk functor is exact), so `⊆`; conversely if `(F/K)_x = 0` then every germ
  at `x` lies in `K_x`, so its germ at any generic point `y ⤳ x` is `0`, forcing `F_y = 0` (all germs of
  sections over an affine `U ∋ x, y` vanish at `y`), contradicting `y ∈ Supp F`;
* (c) `F/K` has no embedded associated points (`hasNoEmbeddedAssociatedPoints_cokernel_embeddedPart_ι`):
  every associated point `x` of `F/K` is a generic point of `Supp F`
  (`mem_genericPoints_of_isAssociatedPoint_cokernel`). Indeed, let `m_x = rad(Ann m̄)`, `m̄ ≠ 0` in
  `(F/K)_x`; lift `m̄` to `m = germ_x t ∈ F_x`; `m ∉ K_x`, so some generic `y ⤳ x` has `germ_y t ≠ 0`
  (stalkwise description of `K`). If `x ≠ y`, pick `f` with `y ∈ D(f)`, `x ∉ D(f)`; then
  `germ_x f ∈ m_x`, so `(germ_x f)^k • m̄ = 0`, i.e. `germ_x (f^k • t) ∈ K_x`, hence
  `germ_y (f^k • t) = 0`; but `germ_y f` is a unit, so `germ_y t = 0`, contradiction. Hence `x = y` is
  generic; two generic points with `x ⤳ y` are equal by minimality.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Stalks of the cokernel sequence `0 → K → F → F/K → 0`: `F_x → (F/K)_x` is surjective with kernel
the image of `K_x` (the stalk functor is exact). -/
theorem embeddedPart.cokernel_stalk_exact (F : X.Modules) (x : X) :
    Function.Surjective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (cokernel.π (embeddedPart.ι F))) ∧
    ∀ m : F.presheaf.stalk x, AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (cokernel.π (embeddedPart.ι F)) m = 0 ↔
      m ∈ LinearMap.range (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (embeddedPart.ι F)) := by
  let i := embeddedPart.ι F
  let G := AlgebraicGeometry.Scheme.Modules.stalkFunctor x
  have hp := AlgebraicGeometry.Scheme.Modules.stalk_preservesFiniteLimits_colimits x
  let hlim : PreservesFiniteLimits G := hp.1
  let hcolAll : PreservesColimits G := hp.2
  let hcol : PreservesFiniteColimits G := by
    let _ : PreservesColimits G := hcolAll
    infer_instance
  let hzero : G.PreservesZeroMorphisms := by
    let _ : PreservesFiniteLimits G := hlim
    infer_instance
  let T := @ShortComplex.map _ _ _ _ _ _ (ShortComplex.cokernelSequence i) G hzero
  have hseq : (ShortComplex.cokernelSequence i).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact i
      mono_f := embeddedPart.mono_ι F
      epi_g := by change Epi (cokernel.π i); infer_instance }
  have hT : T.ShortExact :=
    @ShortComplex.ShortExact.map_of_exact _ _ _ _ _ _ _ hseq G hzero hlim hcol
  have hf : T.f.hom = AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x i := by
    ext m
    rfl
  have hg : T.g.hom = AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (cokernel.π i) := by
    ext m
    rfl
  refine ⟨?_, fun m => ?_⟩
  · rw [← hg]
    exact hT.moduleCat_surjective_g
  · have hm := ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT.exact) m
    change T.g.hom m = 0 ↔ ∃ y, T.f.hom y = m at hm
    rw [hf, hg] at hm
    exact hm

/-- **(a)** `Supp K` is nowhere dense in `Supp F` (see the module docstring). -/
theorem isNowhereDense_support_embeddedPart (F : X.Modules) [AlgebraicGeometry.IsLocallyNoetherian X]
    [F.IsCoherent] :
    IsNowhereDense (Subtype.val ⁻¹' F.embeddedPart.support : Set ↥F.support) := by
  haveI := embeddedPart_isCoherent F
  have hcl : IsClosed (Subtype.val ⁻¹' F.embeddedPart.support : Set ↥F.support) :=
    (isClosed_support_of_isCoherent F.embeddedPart).preimage continuous_subtype_val
  rw [hcl.isNowhereDense_iff, Set.eq_empty_iff_forall_notMem]
  intro v hv
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp
    (isOpen_interior (s := (Subtype.val ⁻¹' F.embeddedPart.support : Set ↥F.support)))
  have hvO : v.1 ∈ O := by
    rw [← hOeq] at hv
    exact hv
  obtain ⟨y, hyg, hyv⟩ := exists_mem_genericPoints_specializes F v.2
  have hyO : y ∈ O := hyv.mem_open hO hvO
  have hy : (⟨y, hyg.1⟩ : F.support) ∈
      interior (Subtype.val ⁻¹' F.embeddedPart.support : Set ↥F.support) := by
    rw [← hOeq]
    exact hyO
  have hyK' : (⟨y, hyg.1⟩ : F.support) ∈ (Subtype.val ⁻¹' F.embeddedPart.support : Set ↥F.support) :=
    interior_subset hy
  have hyK : y ∈ F.embeddedPart.support := hyK'
  have h1 : Nontrivial (F.embeddedPart.presheaf.stalk y) := hyK
  exact not_subsingleton_iff_nontrivial.mpr h1 (subsingleton_stalk_embeddedPart F hyg)

/-- **(b)** `Supp (F/K) = Supp F` (see the module docstring). -/
theorem support_cokernel_embeddedPart_ι (F : X.Modules) [AlgebraicGeometry.IsLocallyNoetherian X]
    [F.IsCoherent] : (cokernel (embeddedPart.ι F)).support = F.support := by
  haveI : F.IsQuasicoherent := IsCoherent.quasicoherent
  ext x
  obtain ⟨hsurj, hex⟩ := embeddedPart.cokernel_stalk_exact F x
  constructor
  · intro hx
    have hnt : Nontrivial ((cokernel (embeddedPart.ι F)).presheaf.stalk x) := hx
    show Nontrivial (F.presheaf.stalk x)
    by_contra hF
    have hsub : Subsingleton (F.presheaf.stalk x) := not_nontrivial_iff_subsingleton.mp hF
    exact not_subsingleton_iff_nontrivial.mpr hnt hsurj.subsingleton
  · intro hx
    show Nontrivial ((cokernel (embeddedPart.ι F)).presheaf.stalk x)
    by_contra hC
    have hsub : Subsingleton ((cokernel (embeddedPart.ι F)).presheaf.stalk x) :=
      not_nontrivial_iff_subsingleton.mp hC
    obtain ⟨y, hyg, hyx⟩ := exists_mem_genericPoints_specializes F hx
    obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ (⊤ : X.Opens) from trivial)
    have hU : AlgebraicGeometry.IsAffineOpen U := hU
    have hyU : y ∈ U := hyx.mem_open U.2 hxU
    have hy : Nontrivial (F.presheaf.stalk y) := hyg.1
    have hall : ∀ m : Γ(F, U), F.presheaf.germ U y hyU m = 0 := by
      intro m
      have hm : F.presheaf.germ U x hxU m ∈
          LinearMap.range (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (embeddedPart.ι F)) := by
        rw [← hex]
        exact Subsingleton.elim _ _
      exact germ_eq_zero_of_mem_range_moduleStalkMap_ι F hxU m hm hyg hyx hyU
    exact not_subsingleton_iff_nontrivial.mpr hy ((subsingleton_stalk_iff F hU hyU).mpr hall)

/-- **(c), main step**: every associated point of `F/K` is a generic point of `Supp F`
(see the module docstring). -/
theorem mem_genericPoints_of_isAssociatedPoint_cokernel (F : X.Modules)
    [AlgebraicGeometry.IsLocallyNoetherian X] [F.IsCoherent] {x : X}
    (hx : AlgebraicGeometry.Scheme.Modules.IsAssociatedPoint (cokernel (embeddedPart.ι F)) x) :
    x ∈ F.genericPoints := by
  haveI : F.IsQuasicoherent := IsCoherent.quasicoherent
  obtain ⟨hsurj, hex⟩ := embeddedPart.cokernel_stalk_exact F x
  obtain ⟨hprime, m', hm'⟩ := hx
  -- `m' ≠ 0`
  have hm'ne : m' ≠ 0 := by
    rintro rfl
    apply hprime.ne_top
    rw [hm', Ideal.radical_eq_top]
    ext r
    simp [Submodule.mem_colon_singleton]
  -- lift `m'` to `F_x`
  obtain ⟨m, rfl⟩ := hsurj m'
  have hmnot : m ∉ LinearMap.range (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (embeddedPart.ι F)) := by
    intro hm
    exact hm'ne ((hex m).mpr hm)
  obtain ⟨U, hxU, t, rfl⟩ := F.presheaf.exists_germ_eq m
  rw [mem_range_moduleStalkMap_ι_iff F hxU t] at hmnot
  push Not at hmnot
  obtain ⟨y, hyg, hyx, hyU, hyt⟩ := hmnot
  suffices hxy : x = y by
    rw [hxy]
    exact hyg
  by_contra hne
  -- an open set containing `y` but not `x`
  have hnxy : ¬ x ⤳ y := fun h => hne (h.antisymm hyx).eq
  rw [specializes_iff_forall_open] at hnxy
  push Not at hnxy
  obtain ⟨D, hD, hyD, hxD⟩ := hnxy
  obtain ⟨W, hW, hxW, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ (⊤ : X.Opens) from trivial)
  have hW : AlgebraicGeometry.IsAffineOpen W := hW
  have hyW : y ∈ W := hyx.mem_open W.2 hxW
  obtain ⟨f, hfle, hyf⟩ := hW.exists_basicOpen_le (V := ⟨D, hD⟩ ⊓ W) ⟨y, ⟨hyD, hyW⟩⟩ hyW
  have hxf : x ∉ X.basicOpen f := fun h => hxD (hfle h).1
  -- `germ_x f ∈ m_x = rad(Ann m')`
  have hfm : X.presheaf.germ W x hxW f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => hxf ((X.mem_basicOpen f x hxW).mpr h)
  rw [hm', Ideal.mem_radical_iff] at hfm
  obtain ⟨k, hk⟩ := hfm
  have hk0 : (X.presheaf.germ W x hxW f) ^ k •
      AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (cokernel.π (embeddedPart.ι F)) (F.presheaf.germ U x hxU t) = 0 :=
    (Submodule.mem_bot _).mp (Submodule.mem_colon_singleton.mp hk)
  have hk1 : AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (cokernel.π (embeddedPart.ι F))
      ((X.presheaf.germ W x hxW (f ^ k)) • F.presheaf.germ U x hxU t) = 0 := by
    rw [LinearMap.map_smul, map_pow]
    exact hk0
  have hk' : (X.presheaf.germ W x hxW (f ^ k)) • F.presheaf.germ U x hxU t ∈
      LinearMap.range (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (embeddedPart.ι F)) := (hex _).mp hk1
  -- rewrite as the germ of a section over `V := U ⊓ W`
  let V : X.Opens := U ⊓ W
  have hxV : x ∈ V := ⟨hxU, hxW⟩
  have hyV : y ∈ V := ⟨hyU, hyW⟩
  let s : Γ(F, V) := X.presheaf.map (homOfLE (inf_le_right : V ≤ W)).op (f ^ k) •
    F.presheaf.map (homOfLE (inf_le_left : V ≤ U)).op t
  have hs : F.presheaf.germ V x hxV s =
      (X.presheaf.germ W x hxW (f ^ k)) • F.presheaf.germ U x hxU t := by
    simp only [s]
    rw [CoherentFreeStalksAux.germ_smul', X.presheaf.germ_res_apply, F.presheaf.germ_res_apply]
  rw [← hs] at hk'
  have h0 := germ_eq_zero_of_mem_range_moduleStalkMap_ι F hxV s hk' hyg hyx hyV
  simp only [s] at h0
  rw [CoherentFreeStalksAux.germ_smul', X.presheaf.germ_res_apply, F.presheaf.germ_res_apply,
    map_pow] at h0
  have hunit : IsUnit (X.presheaf.germ W y hyW f) := (X.mem_basicOpen f y hyW).mp hyf
  exact hyt ((hunit.pow k).smul_left_cancel.mp (h0.trans (smul_zero _).symm))

/-- **(c)** `F/K` has no embedded associated points. -/
theorem hasNoEmbeddedAssociatedPoints_cokernel_embeddedPart_ι (F : X.Modules)
    [AlgebraicGeometry.IsLocallyNoetherian X] [F.IsCoherent] :
    AlgebraicGeometry.Scheme.Modules.HasNoEmbeddedAssociatedPoints (cokernel (embeddedPart.ι F)) := by
  intro x y hx hy hxy
  have hxg := mem_genericPoints_of_isAssociatedPoint_cokernel F hx
  have hyg := mem_genericPoints_of_isAssociatedPoint_cokernel F hy
  exact hyg.2 x hxg.1 hxy

end AlgebraicGeometry.Scheme.Modules

/-- **Stacks 02OL** (remove embedded points): `K := embeddedPart F`, `ι` its inclusion. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_remove_embedded_points {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent] :
    ∃ (K : X.Modules) (ι : K ⟶ F) (_ : CategoryTheory.Mono ι), K.IsCoherent ∧
      IsNowhereDense (Subtype.val ⁻¹' K.support : Set ↥F.support) ∧
      (CategoryTheory.Limits.cokernel ι).support = F.support ∧
      AlgebraicGeometry.Scheme.Modules.HasNoEmbeddedAssociatedPoints (CategoryTheory.Limits.cokernel ι) :=
  ⟨F.embeddedPart, AlgebraicGeometry.Scheme.Modules.embeddedPart.ι F,
    AlgebraicGeometry.Scheme.Modules.embeddedPart.mono_ι F,
    AlgebraicGeometry.Scheme.Modules.embeddedPart_isCoherent F,
    AlgebraicGeometry.Scheme.Modules.isNowhereDense_support_embeddedPart F,
    AlgebraicGeometry.Scheme.Modules.support_cokernel_embeddedPart_ι F,
    AlgebraicGeometry.Scheme.Modules.hasNoEmbeddedAssociatedPoints_cokernel_embeddedPart_ι F⟩

end
