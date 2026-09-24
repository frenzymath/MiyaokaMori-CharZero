import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RegularMeromorphicSection
import MiyaokaMori.RingTheory.Localization.RegularMeromorphicSectionAlgebra
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.LineBundleStalkFrame
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.NoEmbeddedPointsSectionsByMinimalGerms

/-! # Construction of a regular meromorphic section from generic point data

The construction of a regular meromorphic section of a line bundle `L` (Stacks 02OZ / 0EMI, `Stacks02oz`),
from abstract "generic point data" `GenericData X`:

a set `G` of minimal points of `X` such that every point is a specialization of a point of `G`, `G ∩ U`
is finite for affine `U`, and a section of `O_X` over a nonempty affine open whose germs vanish at all
points of `G` is zero. (For `X` locally Noetherian without embedded points: `G` = all minimal points;
for `X` integral: `G = {η}`, Stacks 01X5.)

Proof (`GenericData.nonempty_regularMeromorphicSection`; Stacks 0EMI, spelled with local fractions):
1. Choose a stalk frame `fr x` at every point (`LineBundleStalkFrame`) and an affine open `W x ∋ x`
   inside it; the cover of the meromorphic section is `x ↦ W x`. The global datum is the family of germs
   `s y := germ_y (fr y).q ∈ L_y`, `y ∈ G` (a generator of the free rank-one `O_{X,y}`-module `L_y`).
2. On a chart `W i`, for `y ∈ G ∩ W i` the coordinate `c_{i,y}` of `s y` in the frame `fr i` is a unit
   (`StalkFrame.isUnit_coord`); write it as a fraction `a_{i,y}/b_{i,y}` of sections of `O_X` over `W i`
   with `y ∈ D(a) ∩ D(b)` (the stalk is the localization of the sections, Stacks 01I8).
3. `Ideal.exists_common_fraction_of_minimalPrimes` gives `A_i, B_i ∈ Γ(W i, O_X)`
   with `A_i / B_i = c_{i,y}` at every `y ∈ G ∩ W i`, and `y ∈ D(A_i) ∩ D(B_i)`; then
   `germ_y A_i • germ_y q_i = germ_y B_i • s y` (`hkey`).
4. `num i := A_i • q_i`, `den i := B_i`. `B_i` and `A_i` are nonzerodivisors on `Γ(W i, O_X)`: a
   multiple `m` with `m B_i = 0` has vanishing germs at all `y ∈ G ∩ W i` (`germ_y B_i` is a unit), so
   `m = 0` (`GenericData.mem_nonZeroDivisors`); nonzerodivisors stay nonzerodivisors in the stalks
   (`IsLocalization.map_nonZeroDivisors_le`), which gives `den_mem_nonZeroDivisors`, and together with the
   regularity of `germ q_i` gives `num_regular`.
5. `compat`: on `W i ⊓ W j` the section `B_j A_i q_i − B_i A_j q_j` has germ `B_j B_i s y − B_i B_j s y = 0`
   at every `y ∈ G`, hence vanishes (`GenericData.section_eq_zero`: a section of `L` with vanishing germs at
   all points of `G` is zero — in a frame its coordinate is a section `g` of `O_X` near `x` with
   `germ_y g • germ_y q = 0`, so `germ_y g = 0` at all `y ∈ G`, so `g = 0` on an affine neighbourhood).

Source: Stacks 02OZ, 0EMI (the "choose generators at the generic points and multiply" argument),
02OX (local fraction form of regular meromorphic sections).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Generic point data on a scheme (see the module docstring). -/
structure GenericData (X : AlgebraicGeometry.Scheme.{u}) where
  /-- the set of "generic points" -/
  G : Set X
  minimal : ∀ y ∈ G, AlgebraicGeometry.Scheme.IsMinimalPoint y
  spec : ∀ x : X, ∃ y ∈ G, y ⤳ x
  finite : ∀ U : X.Opens, AlgebraicGeometry.IsAffineOpen U → (G ∩ (U : Set X)).Finite
  sections_eq_zero : ∀ (U : X.Opens), AlgebraicGeometry.IsAffineOpen U → ∀ x : X, x ∈ U →
    ∀ f : Γ(X, U), (∀ y ∈ G, ∀ (hy : y ∈ U), X.presheaf.germ U y hy f = 0) → f = 0

namespace GenericData

/-- A section of `O_X` over a nonempty affine open which is a unit at every generic point is a
nonzerodivisor. -/
theorem mem_nonZeroDivisors (D : GenericData X) {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    {x : X} (hx : x ∈ U) (b : Γ(X, U)) (hb : ∀ y ∈ D.G, ∀ (_ : y ∈ U), y ∈ X.basicOpen b) :
    b ∈ nonZeroDivisors Γ(X, U) := by
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · apply D.sections_eq_zero U hU x hx m
    intro y hy hyU
    have hunit : IsUnit (X.presheaf.germ U y hyU b) := (X.mem_basicOpen b y hyU).mp (hb y hy hyU)
    have : X.presheaf.germ U y hyU m * X.presheaf.germ U y hyU b = 0 := by
      rw [← map_mul, mul_comm, hm, map_zero]
    exact hunit.mul_left_eq_zero.mp this
  · apply D.sections_eq_zero U hU x hx m
    intro y hy hyU
    have hunit : IsUnit (X.presheaf.germ U y hyU b) := (X.mem_basicOpen b y hyU).mp (hb y hy hyU)
    have : X.presheaf.germ U y hyU m * X.presheaf.germ U y hyU b = 0 := by
      rw [← map_mul, hm, map_zero]
    exact hunit.mul_left_eq_zero.mp this

end GenericData

/-- Germs of nonzerodivisors are nonzerodivisors (the stalk is a localization of the sections). -/
theorem germ_mem_nonZeroDivisors {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) {x : X}
    (hx : x ∈ U) {b : Γ(X, U)} (hb : b ∈ nonZeroDivisors Γ(X, U)) :
    X.presheaf.germ U x hx b ∈ nonZeroDivisors (X.presheaf.stalk x) := by
  letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.map_nonZeroDivisors_le (M := (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
    (S := X.presheaf.stalk x) (Submonoid.mem_map_of_mem _ hb)

namespace GenericData

/-- A section of a line bundle whose germs vanish at all generic points is zero. -/
theorem section_eq_zero (D : GenericData X) (L : X.Modules) [L.IsLineBundle] {V : X.Opens}
    (σ : Γ(L, V)) (h : ∀ y ∈ D.G, ∀ hy : y ∈ V, L.presheaf.germ V y hy σ = 0) : σ = 0 := by
  apply TopCat.Presheaf.section_ext (⟨L.presheaf, L.isSheaf⟩ : TopCat.Sheaf Ab X) V σ 0
  intro x hx
  rw [map_zero]
  obtain ⟨fr, hxfr⟩ := exists_stalkFrame L x
  set c := fr.coord x hxfr (L.presheaf.germ V x hx σ) with hc
  obtain ⟨W, hxW, g, hg⟩ := X.presheaf.exists_germ_eq c
  let V₁ : X.Opens := W ⊓ V ⊓ fr.U
  have hxV₁ : x ∈ V₁ := ⟨⟨hxW, hx⟩, hxfr⟩
  have hV₁W : V₁ ≤ W := inf_le_left.trans inf_le_left
  have hV₁V : V₁ ≤ V := inf_le_left.trans inf_le_right
  have hV₁fr : V₁ ≤ fr.U := inf_le_right
  have h1 : L.presheaf.germ V₁ x hxV₁ (L.presheaf.map (homOfLE hV₁V).op σ) =
      L.presheaf.germ V₁ x hxV₁ (X.presheaf.map (homOfLE hV₁W).op g •
        L.presheaf.map (homOfLE hV₁fr).op fr.q) := by
    rw [L.presheaf.germ_res_apply, CoherentFreeStalksAux.germ_smul', X.presheaf.germ_res_apply,
      L.presheaf.germ_res_apply, hg]
    exact fr.eq_coord_smul hxfr _
  obtain ⟨W₂, hxW₂, iV₁, iV₁', heq⟩ := TopCat.Presheaf.germ_eq L.presheaf x hxV₁ hxV₁ _ _ h1
  obtain ⟨W₃, hW₃, hxW₃, hW₃le⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxW₂
  have hW₃ : AlgebraicGeometry.IsAffineOpen W₃ := hW₃
  have hW₃V₁ : W₃ ≤ V₁ := hW₃le.trans iV₁.le
  have hg3 : X.presheaf.map (homOfLE (hW₃V₁.trans hV₁W)).op g = 0 := by
    apply D.sections_eq_zero W₃ hW₃ x hxW₃
    intro y hy hyW₃
    have hyV₁ : y ∈ V₁ := hW₃V₁ hyW₃
    have e1 := congrArg (L.presheaf.germ W₂ y (hW₃le hyW₃)) heq
    simp only [TopCat.Presheaf.germ_res_apply, CoherentFreeStalksAux.germ_smul'] at e1
    rw [h y hy (hV₁V hyV₁)] at e1
    rw [X.presheaf.germ_res_apply]
    exact fr.eq_zero_of_smul_germ_eq_zero (hV₁fr hyV₁) e1.symm
  have hc0 : c = 0 := by
    rw [← hg, ← X.presheaf.germ_res_apply (homOfLE (hW₃V₁.trans hV₁W)) x hxW₃ g, hg3, map_zero]
  rw [fr.eq_coord_smul hxfr (L.presheaf.germ V x hx σ), ← hc, hc0, zero_smul]

/-- **The construction** (see the module docstring). -/
theorem nonempty_regularMeromorphicSection (D : GenericData X) (L : X.Modules) [L.IsLineBundle] :
    Nonempty (AlgebraicGeometry.Scheme.Modules.RegularMeromorphicSection L) := by
  classical
  -- frames and affine charts
  choose fr hfr using exists_stalkFrame L
  have hch : ∀ x : X, ∃ W : X.Opens, AlgebraicGeometry.IsAffineOpen W ∧ x ∈ W ∧ W ≤ (fr x).U := by
    intro x
    obtain ⟨W, hW, hxW, hle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (hfr x)
    exact ⟨W, hW, hxW, hle⟩
  choose W hWaff hxW hWle using hch
  let F : X → StalkFrame L := fun i => (fr i).restrict (W i) (hWle i)
  let q : ∀ i : X, Γ(L, W i) := fun i => (F i).q
  -- the coordinates of the global germs `s y := germ_y (fr y).q` as fractions
  have hfrac : ∀ (i y : X), y ∈ D.G → ∀ hy : y ∈ W i, ∃ a b : Γ(X, W i),
      y ∈ X.basicOpen a ∧ y ∈ X.basicOpen b ∧
      X.presheaf.germ (W i) y hy a =
        (F i).coord y hy (L.presheaf.germ (fr y).U y (hfr y) (fr y).q) * X.presheaf.germ (W i) y hy b := by
    intro i y hy hyW
    set c := (F i).coord y hyW (L.presheaf.germ (fr y).U y (hfr y) (fr y).q) with hc
    have hcu : IsUnit c := (F i).isUnit_coord (fr y) hyW (hfr y)
    letI := X.presheaf.algebra_section_stalk ⟨y, hyW⟩
    haveI : IsLocalization.AtPrime (X.presheaf.stalk y) ((hWaff i).primeIdealOf ⟨y, hyW⟩).asIdeal :=
      (hWaff i).isLocalization_stalk ⟨y, hyW⟩
    obtain ⟨⟨a, b⟩, hab⟩ :=
      IsLocalization.mk'_surjective ((hWaff i).primeIdealOf ⟨y, hyW⟩).asIdeal.primeCompl c
    have hb : y ∈ X.basicOpen (b : Γ(X, W i)) :=
      (mem_basicOpen_iff_notMem_primeIdealOf (hWaff i) hyW b).mpr b.2
    have hbu : IsUnit (X.presheaf.germ (W i) y hyW b) := (X.mem_basicOpen _ y hyW).mp hb
    have heq : X.presheaf.germ (W i) y hyW a = c * X.presheaf.germ (W i) y hyW b := by
      rw [← hab]
      exact (IsLocalization.mk'_spec _ a b).symm
    refine ⟨a, b, ?_, hb, heq⟩
    rw [X.mem_basicOpen a y hyW, heq]
    exact hcu.mul hbu
  choose! a b ha hb hab using hfrac
  -- the common fractions `A i / B i`
  have hCRT : ∀ i : X, ∃ A B : Γ(X, W i), ∀ y ∈ D.G, ∀ hy : y ∈ W i,
      A ∉ ((hWaff i).primeIdealOf ⟨y, hy⟩).asIdeal ∧ B ∉ ((hWaff i).primeIdealOf ⟨y, hy⟩).asIdeal ∧
      ∃ c ∉ ((hWaff i).primeIdealOf ⟨y, hy⟩).asIdeal, c * (A * b i y) = c * (B * a i y) := by
    intro i
    let t : Finset X := (D.finite (W i) (hWaff i)).toFinset
    have hmem : ∀ y, y ∈ t ↔ y ∈ D.G ∧ y ∈ W i := fun y => Set.Finite.mem_toFinset _
    let P : X → PrimeSpectrum Γ(X, W i) := fun y =>
      if hy : y ∈ W i then (hWaff i).primeIdealOf ⟨y, hy⟩ else (hWaff i).primeIdealOf ⟨i, hxW i⟩
    have hP : ∀ y (hy : y ∈ W i), P y = (hWaff i).primeIdealOf ⟨y, hy⟩ := fun y hy => dif_pos hy
    have hPinj : Set.InjOn P t := by
      intro y hy y' hy' hyy'
      have hyW : y ∈ W i := ((hmem y).mp hy).2
      have hy'W : y' ∈ W i := ((hmem y').mp hy').2
      rw [hP y hyW, hP y' hy'W] at hyy'
      have := congrArg (fun p => (hWaff i).fromSpec p) hyy'
      simp only at this
      rwa [(hWaff i).fromSpec_primeIdealOf, (hWaff i).fromSpec_primeIdealOf] at this
    obtain ⟨A, B, h⟩ := Ideal.exists_common_fraction_of_minimalPrimes t P hPinj
      (fun y hyt => by
        have hyG := ((hmem y).mp hyt).1
        have hyW := ((hmem y).mp hyt).2
        rw [hP y hyW]
        exact primeIdealOf_mem_minimalPrimes_bot_of_isMinimalPoint (hWaff i) hyW (D.minimal y hyG))
      (fun y => a i y) (fun y => b i y)
      (fun y hyt => by
        have hyG := ((hmem y).mp hyt).1
        have hyW := ((hmem y).mp hyt).2
        rw [hP y hyW]
        exact (mem_basicOpen_iff_notMem_primeIdealOf (hWaff i) hyW _).mp (ha i y hyG hyW))
      (fun y hyt => by
        have hyG := ((hmem y).mp hyt).1
        have hyW := ((hmem y).mp hyt).2
        rw [hP y hyW]
        exact (mem_basicOpen_iff_notMem_primeIdealOf (hWaff i) hyW _).mp (hb i y hyG hyW))
    refine ⟨A, B, fun y hy hyW => ?_⟩
    have hyt : y ∈ t := (hmem y).mpr ⟨hy, hyW⟩
    have := h y hyt
    rwa [hP y hyW] at this
  choose A B hAB using hCRT
  -- consequences
  have hAy : ∀ i y, y ∈ D.G → ∀ hy : y ∈ W i, y ∈ X.basicOpen (A i) := fun i y hy hyW =>
    (mem_basicOpen_iff_notMem_primeIdealOf (hWaff i) hyW _).mpr (hAB i y hy hyW).1
  have hBy : ∀ i y, y ∈ D.G → ∀ hy : y ∈ W i, y ∈ X.basicOpen (B i) := fun i y hy hyW =>
    (mem_basicOpen_iff_notMem_primeIdealOf (hWaff i) hyW _).mpr (hAB i y hy hyW).2.1
  have hAnzd : ∀ i, A i ∈ nonZeroDivisors Γ(X, W i) := fun i =>
    D.mem_nonZeroDivisors (hWaff i) (hxW i) (A i) (hAy i)
  have hBnzd : ∀ i, B i ∈ nonZeroDivisors Γ(X, W i) := fun i =>
    D.mem_nonZeroDivisors (hWaff i) (hxW i) (B i) (hBy i)
  -- the key identity `germ A • germ q = germ B • s y`
  have hkey : ∀ i y, y ∈ D.G → ∀ hy : y ∈ W i,
      X.presheaf.germ (W i) y hy (A i) • L.presheaf.germ (W i) y hy (q i) =
        X.presheaf.germ (W i) y hy (B i) • L.presheaf.germ (fr y).U y (hfr y) (fr y).q := by
    intro i y hy hyW
    obtain ⟨-, -, c, hc, hcAB⟩ := hAB i y hy hyW
    have hcu : IsUnit (X.presheaf.germ (W i) y hyW c) :=
      (X.mem_basicOpen c y hyW).mp ((mem_basicOpen_iff_notMem_primeIdealOf (hWaff i) hyW c).mpr hc)
    have hbu : IsUnit (X.presheaf.germ (W i) y hyW (b i y)) :=
      (X.mem_basicOpen _ y hyW).mp (hb i y hy hyW)
    have h1 : X.presheaf.germ (W i) y hyW (A i) * X.presheaf.germ (W i) y hyW (b i y) =
        X.presheaf.germ (W i) y hyW (B i) * X.presheaf.germ (W i) y hyW (a i y) := by
      apply hcu.mul_left_cancel
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hcAB]
    rw [hab i y hy hyW, ← mul_assoc] at h1
    have h2 : X.presheaf.germ (W i) y hyW (A i) =
        X.presheaf.germ (W i) y hyW (B i) *
          (F i).coord y hyW (L.presheaf.germ (fr y).U y (hfr y) (fr y).q) :=
      hbu.mul_right_cancel h1
    rw [h2, mul_smul]
    congr 1
    exact ((F i).eq_coord_smul hyW _).symm
  -- the meromorphic section
  refine ⟨AlgebraicGeometry.Scheme.Modules.RegularMeromorphicSection.mk X W (fun x => ⟨x, hxW x⟩)
      (fun i => A i • q i) (fun i => B i)
      (fun i x hx => germ_mem_nonZeroDivisors (hWaff i) hx (hBnzd i))
      (fun i x hx c hc => ?_) (fun i j => ?_)⟩
  · change c • L.presheaf.germ (W i) x hx (A i • q i) = 0 at hc
    rw [CoherentFreeStalksAux.germ_smul', smul_smul] at hc
    have h1 := (F i).eq_zero_of_smul_germ_eq_zero hx hc
    exact (mem_nonZeroDivisors_iff.mp (germ_mem_nonZeroDivisors (hWaff i) hx (hAnzd i))).2 c h1
  · apply sub_eq_zero.mp
    apply D.section_eq_zero L
    intro y hy hyV
    have hyi : y ∈ W i := hyV.1
    have hyj : y ∈ W j := hyV.2
    rw [map_sub, sub_eq_zero]
    simp only [CoherentFreeStalksAux.germ_smul', TopCat.Presheaf.germ_res_apply, Scheme.Modules.map_smul]
    rw [hkey i y hy hyi, hkey j y hy hyj, smul_smul, smul_smul, mul_comm]

end GenericData

end AlgebraicGeometry.Scheme.Modules

end
