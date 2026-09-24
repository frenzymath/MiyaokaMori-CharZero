import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModuleUnit
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RegularMeromorphicDenominatorIdeal
import MiyaokaMori.AlgebraicGeometry.Modules.FrameLocusOn
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FrameLocus
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.DenominatorMapsAssembly

/-! # The cokernels of `1 : I → O_X` and `s : I → L` are supported on a closed nowhere-dense set

Third paragraph of the proof of Stacks 02P0 (`Stacks02p0`).

**Statement.** `s` a regular meromorphic section of the line bundle `L` on the scheme `X`, with local fraction
representation `s|_{U i} = num i / den i`; `I = denomIdeal s` its ideal of denominators, `a : I → O_X` the
inclusion and `b : I → L` multiplication by `s` (`RegularMeromorphicDenominatorIdeal`). Then
`T := closure (Supp (coker a) ∪ Supp (coker b))` is closed, contains both supports, and has empty interior.

**Proof (Stacks 02P0, as formalized).**
1. `a` is surjective on the stalk at `x` whenever `x ∈ D(den i)` (`denomInclusion_stalk_surjective`): on a
   neighbourhood `W ≤ U i` of `x` the section `den i` is a unit `u`, so for `g ∈ O(W)`, `l := (u⁻¹ g) • num i`
   satisfies `den i • l = g • num i`, i.e. `g ∈ I(W)` (`exists_app_eq_of_den_smul`).
2. `b` is surjective on the stalk at `x` whenever `num i` is a frame of `L` near `x`, i.e.
   `x ∈ frameLocusOn (num i)` (`mulHom_stalk_surjective`): a section `l` of `L` near `x` is `c • num i` for a
   function `c`, and `g := den i • c ∈ I(W)` with `b(g) = l`.
3. Hence `Supp (coker a) ∩ U i ⊆ U i \ D(den i)` and `Supp (coker b) ∩ U i ⊆ U i \ frameLocusOn (num i)`
   (`notMem_support_cokernel_iff`).
4. `D(den i)` is dense in `U i` (`denseIn_basicOpen_of_germ_mem_nonZeroDivisors`): if a nonempty open
   `O ⊆ U i` missed `D(den i)`, pick an affine `V ⊆ O`; then `D(den i|_V) = V ⊓ D(den i) = ∅`, so `den i|_V` is
   nilpotent (Stacks 01OM / Mathlib `isNilpotent_iff_basicOpen_eq_bot_of_isCompact`), hence its germ at a point
   of `V` is a nilpotent non-zero-divisor in a nontrivial local ring — impossible. (This replaces Stacks' use of
   00EU, "minimal primes consist of zero-divisors".)
5. `frameLocusOn (num i)` is dense in `U i` (`denseIn_frameLocusOn_num`): near any point choose a frame `e` of
   `L` and write `num i = c • e`; regularity of `num i` on stalks makes the germs of `c` non-zero-divisors, so
   `D(c)` is dense by step 4, and on `D(c)` the section `num i = c • e` is a frame (`IsFrame.of_isUnit_coord`).
6. The intersection of two open sets dense in `U i` is dense in `U i`, and a set whose intersection with each
   member `U i` of an open cover lies in the complement of an open dense subset of `U i` has nowhere-dense
   closure (`interior_closure_eq_empty_of_locally`: if `x ∈ interior (closure S)` with `x ∈ U i`, the nonempty open
   `interior (closure S) ∩ U i` meets the dense set `D i`, in a point `y ∈ closure S`; the open neighbourhood
   `interior (closure S) ∩ D i` of `y` then meets `S`, in a point of `S ∩ U i ∩ D i = ∅`).

Source: Stacks 02P0 (third paragraph), 01OM; the reduction "nowhere density is local" is elementary topology.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.RegularMeromorphicSection

/-! ## Elementary topology: nowhere density is local -/

/-- `D` is dense in `U`: every nonempty open subset of `U` meets `D`. -/
def DenseIn {Y : Type*} [TopologicalSpace Y] (D U : Set Y) : Prop :=
  ∀ O : Set Y, IsOpen O → O ⊆ U → O.Nonempty → (O ∩ D).Nonempty

theorem DenseIn.inter {Y : Type*} [TopologicalSpace Y] {D₁ D₂ U : Set Y} (h₁ : DenseIn D₁ U)
    (h₂ : DenseIn D₂ U) (hD₁ : IsOpen D₁) : DenseIn (D₁ ∩ D₂) U := by
  intro O hO hOU hne
  obtain ⟨y, hy⟩ := h₂ (O ∩ D₁) (hO.inter hD₁) (Set.inter_subset_left.trans hOU) (h₁ O hO hOU hne)
  exact ⟨y, hy.1.1, hy.1.2, hy.2⟩

/-- **Nowhere density is local**: if `S ∩ U i` lies in the complement of an open subset `D i` dense in `U i`
for every member of an open cover `U`, then `closure S` has empty interior. -/
theorem interior_closure_eq_empty_of_locally {Y : Type*} [TopologicalSpace Y] (S : Set Y) {ι : Type*}
    (U : ι → TopologicalSpace.Opens Y) (hcov : ∀ y, ∃ i, y ∈ U i) (D : ι → Set Y) (hD : ∀ i, IsOpen (D i))
    (hDU : ∀ i, D i ⊆ U i) (hdense : ∀ i, DenseIn (D i) (U i)) (hS : ∀ i, S ∩ U i ⊆ (U i : Set Y) \ D i) :
    interior (closure S) = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨i, hi⟩ := hcov x
  obtain ⟨y, hyO, hyD⟩ := hdense i (interior (closure S) ∩ U i) (isOpen_interior.inter (U i).isOpen)
    Set.inter_subset_right ⟨x, hx, hi⟩
  have hyS : y ∈ closure S := interior_subset hyO.1
  obtain ⟨z, ⟨hzO, hzD⟩, hzS⟩ := mem_closure_iff.mp hyS (interior (closure S) ∩ D i)
    (isOpen_interior.inter (hD i)) ⟨hyO.1, hyD⟩
  exact (hS i ⟨hzS, hDU i hzD⟩).2 hzD

variable {X : AlgebraicGeometry.Scheme.{u}}

/-! ## Density of the basic open of a stalkwise non-zero-divisor -/

/-- **The basic open of a function whose germs are non-zero-divisors is dense** (in the open where the function
lives): on an affine open missing `D(c)`, `c` would be nilpotent, but a nilpotent non-zero-divisor forces the
(nontrivial, local) stalk ring to be trivial. -/
theorem denseIn_basicOpen_of_germ_mem_nonZeroDivisors {W : X.Opens} (c : Γ(X, W))
    (hc : ∀ (x : X) (hx : x ∈ W), X.presheaf.germ W x hx c ∈ nonZeroDivisors (X.presheaf.stalk x)) :
    DenseIn (X.basicOpen c : Set X) (W : Set X) := by
  intro O hO hOW hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVO⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx hO
  have hVW : V ≤ W := fun y hy => hOW (hVO hy)
  by_contra hempty
  have hbot : X.basicOpen (X.presheaf.map (homOfLE hVW).op c) = ⊥ := by
    rw [AlgebraicGeometry.Scheme.basicOpen_res]
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    refine le_bot_iff.mp fun y hy => ?_
    have : y ∈ O ∩ (X.basicOpen c : Set X) := ⟨hVO hy.1, hy.2⟩
    rw [hempty] at this
    exact this
  obtain ⟨n, hn⟩ :=
    (AlgebraicGeometry.Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hV.isCompact _).mpr hbot
  have hgerm : (X.presheaf.germ W x (hVW hxV) c) ^ n = 0 := by
    have := congrArg (X.presheaf.germ V x hxV) hn
    rw [map_pow, map_zero, X.presheaf.germ_res_apply] at this
    exact this
  have hmem : (X.presheaf.germ W x (hVW hxV) c) ^ n ∈ nonZeroDivisors (X.presheaf.stalk x) :=
    pow_mem (hc x (hVW hxV)) n
  rw [hgerm] at hmem
  exact zero_notMem_nonZeroDivisors hmem

variable {L : X.Modules} [L.IsLineBundle] (s : AlgebraicGeometry.Scheme.Modules.RegularMeromorphicSection L)

/-- `D(den i)` is dense in `U i`. -/
theorem denseIn_basicOpen_den (i : s.ι) : DenseIn (X.basicOpen (s.den i) : Set X) (s.U i : Set X) :=
  denseIn_basicOpen_of_germ_mem_nonZeroDivisors (s.den i) (s.den_mem_nonZeroDivisors i)

/-- **The frame locus of `num i` is dense in `U i`**: near any point write `num i = c • e` in a frame `e`;
the germs of `c` are non-zero-divisors (regularity of `num i`), so `D(c)` is dense, and on `D(c)` the section
`num i` is a frame. -/
theorem denseIn_frameLocusOn_num (i : s.ι) :
    DenseIn (L.frameLocusOn (s.num i) : Set X) (s.U i : Set X) := by
  intro O hO hOU hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨W, hWO, hxW, e, hf⟩ := AlgebraicGeometry.Scheme.Modules.exists_frame_le L (U := ⟨O, hO⟩) hx
  have hWU : W ≤ s.U i := fun y hy => hOU (hWO hy)
  -- the coordinate of `num i` in the frame `e`
  set c : Γ(X, W) := hf.coord le_rfl (L.res hWU (s.num i)) with hc_def
  have hce : c • e = L.res hWU (s.num i) := by
    have := hf.coord_smul_frame le_rfl (L.res hWU (s.num i))
    rwa [AlgebraicGeometry.Scheme.Modules.res_self] at this
  -- its germs are non-zero-divisors
  have hc : ∀ (y : X) (hy : y ∈ W), X.presheaf.germ W y hy c ∈ nonZeroDivisors (X.presheaf.stalk y) := by
    intro y hy
    rw [mem_nonZeroDivisors_iff_right]
    intro r hr
    apply s.num_regular i y (hWU hy) r
    rw [← L.presheaf.germ_res_apply (homOfLE hWU) y hy (s.num i)]
    change r • L.presheaf.germ W y hy (L.res hWU (s.num i)) = 0
    rw [← hce, germ_smul'', ← mul_smul, hr, zero_smul]
  -- a point of `D(c) ⊆ W ⊆ O`
  obtain ⟨y, hyW, hyc⟩ := denseIn_basicOpen_of_germ_mem_nonZeroDivisors c hc W W.isOpen le_rfl ⟨x, hxW⟩
  refine ⟨y, hWO hyW, ?_⟩
  -- on `D(c)`, `num i = c • e` is a frame
  have hDW : X.basicOpen c ≤ W := X.basicOpen_le c
  have hu : IsUnit (X.presheaf.map (homOfLE hDW).op c) := X.toRingedSpace.isUnit_res_basicOpen c
  have hfr : IsFrame L (X.basicOpen c) (L.res (hDW.trans hWU) (s.num i)) := by
    refine AlgebraicGeometry.Scheme.Modules.IsFrame.of_isUnit_coord (hf.restrict hDW) ?_
    have hcoord : (hf.restrict hDW).coord le_rfl (L.res (hDW.trans hWU) (s.num i)) =
        X.presheaf.map (homOfLE hDW).op c := by
      apply (hf.restrict hDW).coord_unique
      rw [AlgebraicGeometry.Scheme.Modules.res_self, ← AlgebraicGeometry.Scheme.Modules.res_smul, hce,
        AlgebraicGeometry.Scheme.Modules.res_res]
    rw [hcoord]
    exact hu
  exact (AlgebraicGeometry.Scheme.Modules.IsFrame.le_frameLocusOn (hDW.trans hWU) hfr) hyc

/-! ## Stalkwise surjectivity of `a` and `b` off the bad loci -/

/-- **`a` is surjective on stalks over `D(den i)`**: where `den i` is a unit `u`, every `g` lies in `I`, with
witness `l = (u⁻¹ g) • num i`. -/
theorem denomInclusion_stalk_surjective (i : s.ι) (x : X) (hx : x ∈ X.basicOpen (s.den i)) :
    Function.Surjective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x s.denomInclusion) := by
  intro t
  obtain ⟨V, hxV, g, rfl⟩ := (unitModule X).presheaf.exists_germ_eq t
  set W := V ⊓ X.basicOpen (s.den i) with hW_def
  have hxW : x ∈ W := ⟨hxV, hx⟩
  have hWD : W ≤ X.basicOpen (s.den i) := inf_le_right
  have hWU : W ≤ s.U i := hWD.trans (X.basicOpen_le _)
  have hu : IsUnit (X.presheaf.map (homOfLE hWU).op (s.den i)) := by
    have hu0 : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le (s.den i))).op (s.den i)) :=
      X.toRingedSpace.isUnit_res_basicOpen (s.den i)
    have := hu0.map (X.presheaf.map (homOfLE hWD).op).hom
    rwa [resX_resX] at this
  obtain ⟨u, hu⟩ := hu
  set g' : Γ(X, W) := toRing ((unitModule X).presheaf.map (homOfLE (inf_le_left : W ≤ V)).op g) with hg'_def
  obtain ⟨h, hh⟩ := s.exists_app_eq_of_den_smul i hWU g'
    ⟨((↑u⁻¹ : Γ(X, W)) * g') • L.presheaf.map (homOfLE hWU).op (s.num i), by
      rw [← hu, smul_smul, ← mul_assoc, Units.mul_inv, one_mul]⟩
  refine ⟨s.denomIdeal.presheaf.germ W x hxW h, ?_⟩
  rw [AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ]
  have hh' : s.denomInclusion.app W h = (unitModule X).presheaf.map (homOfLE (inf_le_left : W ≤ V)).op g :=
    toRing_injective W hh
  rw [hh']
  exact (unitModule X).presheaf.germ_res_apply (homOfLE (inf_le_left : W ≤ V)) x hxW g

/-- **`b` is surjective on stalks over the frame locus of `num i`**: if `num i` is a frame near `x`, a local
section `l` of `L` is `c • num i`, and `g := den i • c ∈ I` has `b(g) = l`. -/
theorem mulHom_stalk_surjective (i : s.ι) (x : X) (hx : x ∈ L.frameLocusOn (s.num i)) :
    Function.Surjective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x s.mulHom) := by
  obtain ⟨W₀, hW₀U, hxW₀, hfr⟩ :=
    AlgebraicGeometry.Scheme.Modules.mem_frameLocusOn_iff_exists_isFrame.mp hx
  intro t
  obtain ⟨V, hxV, l, rfl⟩ := L.presheaf.exists_germ_eq t
  set W := V ⊓ W₀ with hW_def
  have hxW : x ∈ W := ⟨hxV, hxW₀⟩
  have hWW₀ : W ≤ W₀ := inf_le_right
  have hWU : W ≤ s.U i := hWW₀.trans hW₀U
  set l' : Γ(L, W) := L.presheaf.map (homOfLE (inf_le_left : W ≤ V)).op l with hl'_def
  set c : Γ(X, W) := hfr.coord hWW₀ l' with hc_def
  have hcl : c • L.presheaf.map (homOfLE hWU).op (s.num i) = l' := by
    have := hfr.coord_smul_frame hWW₀ l'
    rwa [AlgebraicGeometry.Scheme.Modules.res_res] at this
  have hwit : X.presheaf.map (homOfLE hWU).op (s.den i) • l' =
      (X.presheaf.map (homOfLE hWU).op (s.den i) * c) • L.presheaf.map (homOfLE hWU).op (s.num i) := by
    rw [mul_smul, hcl]
  have hmem : s.IsMul W (X.presheaf.map (homOfLE hWU).op (s.den i) * c) l' :=
    IsMul.of_single s i hWU hwit
  let h : Γ(s.denomIdeal, W) := ⟨X.presheaf.map (homOfLE hWU).op (s.den i) * c, l', hmem⟩
  refine ⟨s.denomIdeal.presheaf.germ W x hxW h, ?_⟩
  rw [AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ, mulHom_app, s.mulSection_eq h hmem]
  exact L.presheaf.germ_res_apply (homOfLE (inf_le_left : W ≤ V)) x hxW l

/-! ## The bad set `T` -/

/-- The closed set `T := closure (Supp (coker a) ∪ Supp (coker b))`. -/
def badSet : Set X :=
  closure ((CategoryTheory.Limits.cokernel s.denomInclusion).support ∪
    (CategoryTheory.Limits.cokernel s.mulHom).support)

theorem isClosed_badSet : IsClosed s.badSet := isClosed_closure

theorem support_cokernel_denomInclusion_subset_badSet :
    (CategoryTheory.Limits.cokernel s.denomInclusion).support ⊆ s.badSet :=
  Set.subset_union_left.trans subset_closure

theorem support_cokernel_mulHom_subset_badSet :
    (CategoryTheory.Limits.cokernel s.mulHom).support ⊆ s.badSet :=
  Set.subset_union_right.trans subset_closure

/-- **`T` has empty interior** (Stacks 02P0, third paragraph): on each chart `U i` the supports of the two
cokernels avoid the open dense subset `D(den i) ∩ frameLocusOn (num i)`. -/
theorem interior_badSet_eq_empty : interior s.badSet = ∅ := by
  refine interior_closure_eq_empty_of_locally _ s.U s.cover
    (fun i => (X.basicOpen (s.den i) : Set X) ∩ (L.frameLocusOn (s.num i) : Set X))
    (fun i => (X.basicOpen (s.den i)).isOpen.inter (L.frameLocusOn (s.num i)).isOpen)
    (fun i => Set.inter_subset_left.trans (X.basicOpen_le (s.den i)))
    (fun i => (s.denseIn_basicOpen_den i).inter (s.denseIn_frameLocusOn_num i)
      (X.basicOpen (s.den i)).isOpen)
    fun i => ?_
  rintro x ⟨hxS, hxU⟩
  refine ⟨hxU, fun hxD => ?_⟩
  have ha : x ∉ (CategoryTheory.Limits.cokernel s.denomInclusion).support :=
    (AlgebraicGeometry.Scheme.Modules.notMem_support_cokernel_iff s.denomInclusion x).mpr
      (s.denomInclusion_stalk_surjective i x hxD.1)
  have hb : x ∉ (CategoryTheory.Limits.cokernel s.mulHom).support :=
    (AlgebraicGeometry.Scheme.Modules.notMem_support_cokernel_iff s.mulHom x).mpr
      (s.mulHom_stalk_surjective i x hxD.2)
  exact hxS.elim ha hb

end AlgebraicGeometry.Scheme.Modules.RegularMeromorphicSection

end
