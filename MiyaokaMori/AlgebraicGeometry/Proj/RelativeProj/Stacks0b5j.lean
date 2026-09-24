import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.VeroneseAwayIso
import MiyaokaMori.RingTheory.GradedRing.VeroneseGradedRing
import MiyaokaMori.RingTheory.GradedRing.VeroneseAwayCompat
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks0b5j_AwayiBase

/-! # The Veronese subring has the same Proj (Stacks 0B5J)

The Veronese construction does not change Proj (Stacks 0B5J, the absolute version for a single graded ring): for
`d ≥ 1`, `Proj(S^{(d)}) ≅ Proj(S)`, with `D_+(f^d)` corresponding to `D_+(f)`. Used in Lemma 2.2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The proof follows Stacks 0B5J (constructions.tex, lemma-d-uple), split into commutative-algebra lemmas and a
   scheme-level assembly:
   1. the injective ring map `S' = S^{(d)} → S` induces `Spec(S) → Spec(S')`, sending a homogeneous prime `𝔭` to
      `𝔭' = S' ∩ 𝔭`;
   2. conversely `𝔭' ↦ 𝔭 = {g ∈ S | g^d ∈ 𝔭'}` (an ideal by the binomial theorem); the two are inverse, so
      `i : X → X'` is a homeomorphism;
   3. for homogeneous `f ∈ S_+`, `S_(f) ≅ S'_(f^d)`, compatibly with the restrictions on `D_+(f)`, so `i` is an
      isomorphism of schemes.
   Steps 1 and 2 are `veroneseHom_base_injective` and `veroneseHom_surjective` (at the level of points); the ring
   isomorphism of step 3 is `veroneseAwayEquiv`, and the compatibility is `veroneseAwayEquiv_awayMap`. -/

/-- The morphism `Spec S_(f) ≅ Spec S^{(d)}_(f^d) --awayι--> Proj S^{(d)}` on the chart `D_+(f)` (`f ∈ S_i`, `i > 0`). -/

noncomputable def AlgebraicGeometry.Proj.veroneseChart {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) (j : (Σ i : ℕ+, 𝒜 i)) :
    AlgebraicGeometry.Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 j.2.1)) ⟶
      AlgebraicGeometry.Proj (veroneseGrading 𝒜 d) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (veroneseAwayEquiv 𝒜 d hd j.2.2).toRingHom) ≫
    AlgebraicGeometry.Proj.awayι (m := (j.1 : ℕ)) (veroneseGrading 𝒜 d)
      (⟨j.2.1 ^ d, (veronese_pow_mem 𝒜 d hd j.2.2).1⟩ : veroneseSubring 𝒜 d)
      (veronese_pow_mem_grading 𝒜 d hd j.2.2) j.1.pos

/-- The ring isomorphism `veroneseAwayEquiv` is an isomorphism in `CommRingCat`. -/
theorem AlgebraicGeometry.Proj.isIso_veroneseAwayEquiv {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ}
    (hf : f ∈ 𝒜 m) :
    IsIso (CommRingCat.ofHom (veroneseAwayEquiv 𝒜 d hd hf).toRingHom) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (veroneseAwayEquiv 𝒜 d hd hf).bijective

theorem AlgebraicGeometry.Proj.veroneseChart_eq {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d)
    (j : (Σ i : ℕ+, 𝒜 i)) :
    AlgebraicGeometry.Proj.veroneseChart 𝒜 d hd j =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (veroneseAwayEquiv 𝒜 d hd j.2.2).toRingHom) ≫
        AlgebraicGeometry.Proj.awayι (m := (j.1 : ℕ)) (veroneseGrading 𝒜 d)
          (⟨j.2.1 ^ d, (veronese_pow_mem 𝒜 d hd j.2.2).1⟩ : veroneseSubring 𝒜 d)
          (veronese_pow_mem_grading 𝒜 d hd j.2.2) j.1.pos := rfl

theorem AlgebraicGeometry.Proj.veroneseChart_isOpenImmersion {A σ : Type*} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d)
    (j : (Σ i : ℕ+, 𝒜 i)) : IsOpenImmersion (AlgebraicGeometry.Proj.veroneseChart 𝒜 d hd j) := by
  have h1 : IsIso (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (veroneseAwayEquiv 𝒜 d hd j.2.2).toRingHom)) :=
    AlgebraicGeometry.isIso_SpecMap_iff.mpr (veroneseAwayEquiv 𝒜 d hd j.2.2).bijective
  rw [AlgebraicGeometry.Proj.veroneseChart_eq]
  exact AlgebraicGeometry.IsOpenImmersion.comp _ _

attribute [local instance] AlgebraicGeometry.Proj.veroneseChart_isOpenImmersion

/-- The image of the chart is exactly `D_+(f^d)` (`opensRange_awayι` + the preceding morphism is an isomorphism). -/
theorem AlgebraicGeometry.Proj.opensRange_veroneseChart {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d)
    (j : (Σ i : ℕ+, 𝒜 i)) :
    (AlgebraicGeometry.Proj.veroneseChart 𝒜 d hd j).opensRange =
      AlgebraicGeometry.Proj.basicOpen (veroneseGrading 𝒜 d)
        (⟨j.2.1 ^ d, (veronese_pow_mem 𝒜 d hd j.2.2).1⟩ : veroneseSubring 𝒜 d) := by
  have h1 : IsIso (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (veroneseAwayEquiv 𝒜 d hd j.2.2).toRingHom)) :=
    AlgebraicGeometry.isIso_SpecMap_iff.mpr (veroneseAwayEquiv 𝒜 d hd j.2.2).bijective
  exact (AlgebraicGeometry.Scheme.Hom.opensRange_comp_of_isIso _ _).trans
    (AlgebraicGeometry.Proj.opensRange_awayι _ _ _ _)

/-- The compatibility of step 3 of Stacks 0B5J (pure commutative algebra): the degree-zero localization
isomorphism of the Veronese subring commutes with the away restriction maps.

Source: Stacks 0B5J (constructions.tex, lemma-d-uple), end of the first paragraph of the proof ("Since these
isomorphisms are compatible with the restrictions mappings of Lemma standard-open").

Meaning: for homogeneous `f ∈ 𝒜 i`, `g ∈ 𝒜 j`, the two paths `S^{(d)}_(f^d) → S_(f) → S_(fg)` (isomorphism, then
restriction) and `S^{(d)}_(f^d) → S^{(d)}_((fg)^d) → S_(fg)` (restriction, then isomorphism) coincide.

Proof: by `Quotient.ind` an element of `HomogeneousLocalization.Away` is `mk ⟨n, a, (f^d)^k, _⟩`
(`a ∈ (S^{(d)})_{nk}`, i.e. `a ∈ S_{nkd}`). Upper path: `veroneseAwayEquiv` sends it verbatim to
`mk ⟨n*d, a, f^{dk}, _⟩ ∈ S_(f)` (`veroneseAwayEquiv.toNumDen`), and `HomogeneousLocalization.awayMap`
(`awayMap_mk`) multiplies by a power of `g`, giving `a·g^{dk} / (fg)^{dk}`. Lower path: `awayMap` first gives
`a·(g^d)^k / ((fg)^d)^k ∈ S^{(d)}_((fg)^d)`, and `veroneseAwayEquiv` reads it as `a·g^{dk} / (fg)^{dk} ∈ S_(fg)`.
The two `HomogeneousLocalization.val` are the same fraction in `Localization.Away (f*g)`, and
`HomogeneousLocalization.val_injective` concludes.

The statement holds for arbitrary degrees `i`, `j` (including `j = 0`), and for `d = 1` both sides are the
identity; the proof needs no case split. -/
theorem veroneseAwayEquiv_awayMap {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f g : A} {i j : ℕ}
    (hf : f ∈ 𝒜 i) (hg : g ∈ 𝒜 j) (hfg : f * g ∈ 𝒜 (i + j)) :
    ((HomogeneousLocalization.awayMap 𝒜 hg (x := f * g) rfl).comp
        (veroneseAwayEquiv 𝒜 d hd hf).toRingHom) =
      (veroneseAwayEquiv 𝒜 d hd hfg).toRingHom.comp
        (HomogeneousLocalization.awayMap (veroneseGrading 𝒜 d)
          (g := (⟨g ^ d, (veronese_pow_mem 𝒜 d hd hg).1⟩ : veroneseSubring 𝒜 d))
          (veronese_pow_mem_grading 𝒜 d hd hg)
          (x := (⟨(f * g) ^ d, (veronese_pow_mem 𝒜 d hd hfg).1⟩ : veroneseSubring 𝒜 d))
          (Subtype.ext (mul_pow f g d))) :=
  veroneseAwayEquiv_awayMap_general 𝒜 d hd hf hg rfl hfg

/-- The chart morphisms are compatible on the overlaps `D_+(f) ∩ D_+(g) = D_+(fg)` (the gluing condition in the
proof of Stacks 0B5J): both pass through `Spec S_(fg) ≅ Spec S^{(d)}_((fg)^d)`.

Proof: the pullback at the overlap is identified with `Spec (Away 𝒜 (f*g))` by Mathlib's
`Proj.pullbackAwayιIso 𝒜 hf hi hg hj (hx := rfl)`, and `pullbackAwayιIso_hom_SpecMap_awayMap_left/right` turn the
two `pullback.fst/snd` into `Spec.map (awayMap 𝒜 …)`; after cancelling the isomorphism (`Iso.cancel_iso_hom_left`)
both sides are `Spec.map (…) ≫ awayι ℬ ⟨f^d⟩`, and one step each with `veroneseAwayEquiv_awayMap` and Mathlib's
`Proj.SpecMap_awayMap_awayι` turns them into `Spec.map (ofHom (veroneseAwayEquiv 𝒜 d hd _)) ≫ awayι ℬ ⟨(f*g)^d⟩`;
the degree witnesses are `i+j` and `j+i`, and the value of `awayι` does not depend on the degree witness
(`basicOpenIsoSpec` is `asIso` of a degree-independent map and `IsIso` is a `Prop`), so the last step is
`congr` + `Subtype.ext (by ring)`. -/
theorem AlgebraicGeometry.Proj.veroneseChart_compat {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) (x y : (Σ i : ℕ+, 𝒜 i)) :
    CategoryTheory.Limits.pullback.fst
        ((AlgebraicGeometry.Proj.affineOpenCover 𝒜).openCover.f x)
        ((AlgebraicGeometry.Proj.affineOpenCover 𝒜).openCover.f y) ≫
        AlgebraicGeometry.Proj.veroneseChart 𝒜 d hd x =
      CategoryTheory.Limits.pullback.snd _ _ ≫ AlgebraicGeometry.Proj.veroneseChart 𝒜 d hd y := by
  change CategoryTheory.Limits.pullback.fst
      (AlgebraicGeometry.Proj.awayι 𝒜 x.2.1 x.2.2 x.1.pos)
      (AlgebraicGeometry.Proj.awayι 𝒜 y.2.1 y.2.2 y.1.pos) ≫
      AlgebraicGeometry.Proj.veroneseChart 𝒜 d hd x =
    CategoryTheory.Limits.pullback.snd
      (AlgebraicGeometry.Proj.awayι 𝒜 x.2.1 x.2.2 x.1.pos)
      (AlgebraicGeometry.Proj.awayι 𝒜 y.2.1 y.2.2 y.1.pos) ≫
      AlgebraicGeometry.Proj.veroneseChart 𝒜 d hd y
  rw [← AlgebraicGeometry.Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left 𝒜 x.2.2 x.1.pos y.2.2
      y.1.pos rfl,
    ← AlgebraicGeometry.Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right 𝒜 x.2.2 x.1.pos y.2.2
      y.1.pos rfl, Category.assoc, Category.assoc, Iso.cancel_iso_hom_left,
    AlgebraicGeometry.Proj.veroneseChart_eq, AlgebraicGeometry.Proj.veroneseChart_eq,
    ← Category.assoc, ← Category.assoc, ← AlgebraicGeometry.Spec.map_comp,
    ← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    veroneseAwayEquiv_awayMap_general 𝒜 d hd x.2.2 y.2.2 rfl
      (SetLike.mul_mem_graded x.2.2 y.2.2),
    veroneseAwayEquiv_awayMap_general 𝒜 d hd y.2.2 x.2.2 (rfl.trans (mul_comm _ _))
      (SetLike.mul_mem_graded x.2.2 y.2.2),
    CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, AlgebraicGeometry.Spec.map_comp,
    AlgebraicGeometry.Spec.map_comp, Category.assoc, Category.assoc,
    AlgebraicGeometry.Proj.SpecMap_awayMap_awayι, AlgebraicGeometry.Proj.SpecMap_awayMap_awayι]
  rfl

/-- `Proj S → Proj S^{(d)}`: the chart morphisms glued with `glueMorphisms`. -/

noncomputable def AlgebraicGeometry.Proj.veroneseHom {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) :
    AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj (veroneseGrading 𝒜 d) :=
  (AlgebraicGeometry.Proj.affineOpenCover 𝒜).openCover.glueMorphisms
    (AlgebraicGeometry.Proj.veroneseChart 𝒜 d hd) (AlgebraicGeometry.Proj.veroneseChart_compat 𝒜 d hd)

/-- The defining property of the gluing: on the chart `D_+(f)`, `veroneseHom` is `veroneseChart`. -/
@[reassoc]
theorem AlgebraicGeometry.Proj.awayι_comp_veroneseHom {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d)
    (j : (Σ i : ℕ+, 𝒜 i)) :
    (AlgebraicGeometry.Proj.affineOpenCover 𝒜).openCover.f j ≫
        AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd =
      AlgebraicGeometry.Proj.veroneseChart 𝒜 d hd j :=
  (AlgebraicGeometry.Proj.affineOpenCover 𝒜).openCover.ι_glueMorphisms _ _ j

/-- `veroneseHom` acts on **points** as the contraction: a homogeneous prime `𝔭` of `Proj S` is contracted along
the subring inclusion `veroneseSubring 𝒜 d ↪ A`.

Source: Stacks 0B5J (constructions.tex, lemma-d-uple), first sentence of the proof ("Given a graded prime ideal
`𝔭 ⊂ S` we see that `𝔭' = j(𝔭) = S' ∩ 𝔭` is a graded prime ideal of `S'`"), where `j : S' = S^{(d)} → S` is the
subring inclusion.

Since `veroneseHom` is glued with `glueMorphisms`, its description on points is not definitional; this lemma
provides it, and `veroneseHom_base_injective` and `veroneseHom_preimage_basicOpen` below both rest on it.

Proof:
1. Take a standard chart containing `𝔭`: from the `covers` of `Proj.affineOpenCover 𝒜` (or directly a homogeneous
   `h ∈ 𝒜_n`, `n > 0`, `h ∉ 𝔭`, which exists by `ProjectiveSpectrum.not_irrelevant_le`) we get an index
   `j = ⟨⟨n,_⟩, ⟨h,_⟩⟩` and a point `q ∈ Spec (Away 𝒜 h)` with `Proj.awayι 𝒜 h _ _ q = 𝔭` (the image of
   `opensRange_awayι` is `D₊(h)`).
2. `awayι_comp_veroneseHom`: `veroneseHom (awayι … q) = veroneseChart j q`, and `veroneseChart_eq` says
   `veroneseChart j = Spec.map (ofHom (veroneseAwayEquiv …)) ≫ awayι ℬ ⟨h^d⟩`. Hence
   `veroneseHom 𝔭 = awayι ℬ ⟨h^d⟩ (PrimeSpectrum.comap (veroneseAwayEquiv …) q)`.
3. The point map of `Proj.awayι`: `awayι = (basicOpenIsoSpec 𝒜 h _ _).inv ≫ (Proj.basicOpen 𝒜 h).ι` (definition
   of Mathlib's `Proj.awayι`), and the point map of `ProjectiveSpectrum.Proj.toSpec` has an explicit description
   in Mathlib (`ProjectiveSpectrum.Proj.FromSpec.toFun`: `𝔮 ↦ {a | every homogeneous component a_i satisfies
   a_i^{n}/h^{deg} ∈ 𝔮}`); both sides become preimages of primes in `HomogeneousLocalization.Away`.
4. What remains is a purely algebraic equality: for homogeneous `a ∈ S^{(d)}`,
   `a ∈ (veroneseAwayEquiv)⁻¹ 𝔮 ⟺ a/h^{…} ∈ 𝔮 ⟺ a ∈ 𝔭`, because `veroneseAwayEquiv` sends
   `a/(h^d)^k ∈ S^{(d)}_((h^d))` verbatim to `a/h^{dk} ∈ S_(h)` (`veroneseAwayEquiv.toNumDen`). A non-homogeneous
   `a` is determined by its homogeneous components (`HomogeneousIdeal`, `Ideal.homogeneous_mem_iff`).

**Edge cases**: if `Proj S = ∅` (`S_+ ⊆ nilradical`) there is no `𝔭` and the statement is vacuous; for `d = 1`,
`veroneseSubring 𝒜 1 = A` and both sides coincide; for `a = 0` both sides are true; for a unit `a` both are false. -/
theorem AlgebraicGeometry.Proj.veroneseHom_base_mem_asHomogeneousIdeal {A σ : Type*} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d)
    (𝔭 : AlgebraicGeometry.Proj 𝒜) (a : veroneseSubring 𝒜 d) :
    a ∈ ((AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).base 𝔭).asHomogeneousIdeal ↔
      (a : A) ∈ 𝔭.asHomogeneousIdeal := by
  -- a standard chart D₊(h) containing 𝔭, h := j.2.1 ∈ 𝒜 j.1
  have hex : ∃ (j : (Σ i : ℕ+, 𝒜 i))
      (q : AlgebraicGeometry.Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 j.2.1))),
      (AlgebraicGeometry.Proj.awayι 𝒜 j.2.1 j.2.2 j.1.pos).base q = 𝔭 :=
    (AlgebraicGeometry.Proj.affineOpenCover 𝒜).openCover.exists_eq 𝔭
  obtain ⟨j, q, hq⟩ := hex
  subst hq
  -- on this chart `veroneseHom` is `Spec.map (veroneseAwayEquiv) ≫ awayι ℬ ⟨h^d⟩`
  have e := (AlgebraicGeometry.Proj.awayι_comp_veroneseHom 𝒜 d hd j).trans
    (AlgebraicGeometry.Proj.veroneseChart_eq 𝒜 d hd j)
  have hvH : (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).base
        ((AlgebraicGeometry.Proj.awayι 𝒜 j.2.1 j.2.2 j.1.pos).base q) =
      (AlgebraicGeometry.Proj.awayι (veroneseGrading 𝒜 d)
          (⟨j.2.1 ^ d, (veronese_pow_mem 𝒜 d hd j.2.2).1⟩ : veroneseSubring 𝒜 d)
          (veronese_pow_mem_grading 𝒜 d hd j.2.2) j.1.pos).base
        (PrimeSpectrum.comap (veroneseAwayEquiv 𝒜 d hd j.2.2).toRingHom q) :=
    congrArg (fun φ : AlgebraicGeometry.Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 j.2.1)) ⟶
      AlgebraicGeometry.Proj (veroneseGrading 𝒜 d) => φ.base q) e
  rw [hvH]
  -- the homogeneous case is the contraction formula on the chart; the rest follows since homogeneous
  -- elements determine a homogeneous ideal
  exact veroneseSubring.mem_iff_of_homogeneous 𝒜 d _ _
    (fun b n hb => AlgebraicGeometry.Proj.mem_veroneseChart_base_iff 𝒜 d hd j.2.2 j.1.pos q b hb) a

/-- The "injective" half of steps 1–2 of Stacks 0B5J (at the level of points).

Source: Stacks 0B5J, first paragraph of the proof: "Given a graded prime ideal `𝔭 ⊂ S` we see that
`𝔭' = j(𝔭) = S' ∩ 𝔭` is a graded prime ideal of `S'`. Conversely, if `𝔭' ⊂ S'` is a graded prime ideal not
containing some homogeneous element `f ∈ S'_+`, then `𝔭 = {g ∈ S | g^d ∈ 𝔭'}` is a graded prime ideal of `S` not
containing `f` whose image under `j` is `𝔭'`. … In this way we see that `j` induces a homeomorphism `i : X → X'`."

Proof: let `x, y ∈ Proj S` be sent by `veroneseHom` to the same point `𝔭'`. It suffices to show that the
homogeneous primes `𝔭_x`, `𝔭_y` satisfy `𝔭_x ∩ S^{(d)} = 𝔭_y ∩ S^{(d)} ⇒ 𝔭_x = 𝔭_y`
(`veroneseHom_base_mem_asHomogeneousIdeal` describes the point map as this contraction). This is Stacks' inverse
construction: for homogeneous `g ∈ S`, `g ∈ 𝔭_x ⟺ g^d ∈ 𝔭_x ∩ S^{(d)}` (`𝔭_x` prime, `g^d ∈ S^{(d)}`), and the
right side depends only on `𝔭_x ∩ S^{(d)}`; homogeneous components determine the ideal (`HomogeneousIdeal.ext`,
`Ideal.IsPrime.pow_mem_iff`), so `𝔭_x = 𝔭_y`. -/
theorem AlgebraicGeometry.Proj.veroneseHom_base_injective {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) :
    Function.Injective (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd) := by
  intro x y hxy
  have hxy' : (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).base x =
      (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).base y := hxy
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro i g hg
  have h1 := AlgebraicGeometry.Proj.veroneseHom_base_mem_asHomogeneousIdeal 𝒜 d hd x
    ⟨g ^ d, (veronese_pow_mem 𝒜 d hd hg).1⟩
  have h2 := AlgebraicGeometry.Proj.veroneseHom_base_mem_asHomogeneousIdeal 𝒜 d hd y
    ⟨g ^ d, (veronese_pow_mem 𝒜 d hd hg).1⟩
  rw [hxy'] at h1
  have h3 : g ^ d ∈ x.asHomogeneousIdeal ↔ g ^ d ∈ y.asHomogeneousIdeal := h1.symm.trans h2
  exact ((x.isPrime.pow_mem_iff_mem d hd).symm.trans h3).trans (y.isPrime.pow_mem_iff_mem d hd)

/-- The "surjective" half of steps 1–2 of Stacks 0B5J (at the level of points).

Source: the "Conversely" part of the first paragraph of the proof of Stacks 0B5J.

Proof: let `𝔭' ∈ Proj S^{(d)}`, a homogeneous prime of `S^{(d)}` not containing `(S^{(d)})_+`. Take a homogeneous
`h ∈ (S^{(d)})_n` (`n > 0`) with `h ∉ 𝔭'`. Regarded as an element of `S`, `h` lies in `S_{nd}` with `nd > 0`, so
the index `⟨⟨n*d, _⟩, ⟨h, _⟩⟩ : Σ i : ℕ+, 𝒜 i` gives a chart whose image is `D_+(h^d)` (`opensRange_veroneseChart`).
Since `𝔭'` is prime and `h ∉ 𝔭'`, also `h^d ∉ 𝔭'`, i.e. `𝔭' ∈ D_+(h^d)`. So `𝔭'` lies in the image of a chart, in
particular in the image of `veroneseHom` (`awayι_comp_veroneseHom`).

Note that `affineOpenCoverOfIrrelevantLESpan` cannot be used here: the ideal spanned by `{f^d}` does in general
**not** contain `(S^{(d)})_+` (e.g. `S = F₂[x,y]`, `d = 2`: `xy ∈ (S^{(2)})_1` is not in the ideal generated by
squares), but the argument above only needs that the `D_+(h^d) = D_+(h)` cover, a topological statement. -/
theorem AlgebraicGeometry.Proj.veroneseHom_base_surjective {A σ : Type*} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) :
    Function.Surjective (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd) := by
  intro 𝔭'
  -- a standard chart D₊(h') of Proj S^{(d)} containing 𝔭', h' := j'.2.1 ∈ ℬ j'.1
  have hex : ∃ (j' : (Σ i : ℕ+, veroneseGrading 𝒜 d i))
      (q' : AlgebraicGeometry.Spec (CommRingCat.of
        (HomogeneousLocalization.Away (veroneseGrading 𝒜 d) j'.2.1))),
      (AlgebraicGeometry.Proj.awayι (veroneseGrading 𝒜 d) j'.2.1 j'.2.2 j'.1.pos).base q' = 𝔭' :=
    (AlgebraicGeometry.Proj.affineOpenCover (veroneseGrading 𝒜 d)).openCover.exists_eq 𝔭'
  obtain ⟨j', q', hq'⟩ := hex
  have hnot : j'.2.1 ∉ 𝔭'.asHomogeneousIdeal := by
    rw [← hq']
    exact AlgebraicGeometry.Proj.notMem_awayι_base (veroneseGrading 𝒜 d) j'.2.2 j'.1.pos q'
  -- h' as an element of S: degree j'.1 * d > 0, giving the chart D₊(h') of Proj S with image D₊(⟨h'^d⟩) ∋ 𝔭'
  have hhA : ((j'.2.1 : veroneseSubring 𝒜 d) : A) ∈ 𝒜 ((j'.1 : ℕ) * d) := j'.2.2.1
  let j : (Σ i : ℕ+, 𝒜 i) := ⟨⟨(j'.1 : ℕ) * d, Nat.mul_pos j'.1.pos hd⟩, ⟨_, hhA⟩⟩
  have hmem : 𝔭' ∈ (AlgebraicGeometry.Proj.veroneseChart 𝒜 d hd j).opensRange := by
    rw [AlgebraicGeometry.Proj.opensRange_veroneseChart, AlgebraicGeometry.Proj.mem_basicOpen]
    intro hmem
    apply hnot
    have e : (⟨((j'.2.1 : veroneseSubring 𝒜 d) : A) ^ d, (veronese_pow_mem 𝒜 d hd hhA).1⟩ :
        veroneseSubring 𝒜 d) = j'.2.1 ^ d :=
      Subtype.ext (SubmonoidClass.coe_pow _ _).symm
    rw [e] at hmem
    exact (𝔭'.isPrime.pow_mem_iff_mem d hd).mp hmem
  obtain ⟨q, hq⟩ := AlgebraicGeometry.Scheme.Hom.mem_opensRange.mp hmem
  refine ⟨(AlgebraicGeometry.Proj.awayι 𝒜 j.2.1 j.2.2 j.1.pos).base q, ?_⟩
  have e := congrArg (fun φ : AlgebraicGeometry.Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 j.2.1)) ⟶
      AlgebraicGeometry.Proj (veroneseGrading 𝒜 d) => φ.base q)
    (AlgebraicGeometry.Proj.awayι_comp_veroneseHom 𝒜 d hd j)
  exact e.trans hq

set_option backward.isDefEq.respectTransparency false in
/-- `veroneseHom` is an isomorphism (Stacks 0B5J). Proof: `IsOpenImmersion.of_openCover_source` (an affine open
cover of the source, injectivity of the underlying map, and an open immersion on every chart) gives an open
immersion; together with surjectivity of the underlying map, `isIso_iff_isOpenImmersion_and_surjective` concludes.
The two point-level properties are `veroneseHom_base_injective` and `veroneseHom_surjective`. (The inverse of
`veroneseIso` is obtained from this via `asIso`; inverses of isomorphisms are unique.) -/
theorem AlgebraicGeometry.Proj.veroneseHom_isIso {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) :
    CategoryTheory.IsIso (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd) := by
  refine (AlgebraicGeometry.isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨?_, ?_⟩
  · refine AlgebraicGeometry.IsOpenImmersion.of_openCover_source _
      (AlgebraicGeometry.Proj.affineOpenCover 𝒜).openCover
      (AlgebraicGeometry.Proj.veroneseHom_base_injective 𝒜 d hd) fun j => ?_
    have h := AlgebraicGeometry.Proj.awayι_comp_veroneseHom 𝒜 d hd j
    simp only [h]
    exact AlgebraicGeometry.Proj.veroneseChart_isOpenImmersion 𝒜 d hd j
  · exact ⟨AlgebraicGeometry.Proj.veroneseHom_base_surjective 𝒜 d hd⟩

noncomputable def AlgebraicGeometry.Proj.veroneseIso {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) :
    AlgebraicGeometry.Proj (veroneseGrading 𝒜 d) ≅ AlgebraicGeometry.Proj 𝒜 :=
  haveI : CategoryTheory.IsIso (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd) :=
    AlgebraicGeometry.Proj.veroneseHom_isIso 𝒜 d hd
  (CategoryTheory.asIso (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd)).symm

/-- The correspondence "`D_+(f)` ↔ `D_+(f^d)`" of Stacks 0B5J, in the form of a preimage under `veroneseHom`.

Source: Stacks 0B5J, first paragraph of the proof: "Moreover, if `f ∈ S_+` is homogeneous and `f ∉ 𝔭`, then
`f^d ∈ S'_+` and `f^d ∉ 𝔭'`", and its converse.

Proof: on points `veroneseHom` is `𝔭 ↦ 𝔭 ∩ S^{(d)}` (`veroneseHom_base_mem_asHomogeneousIdeal`). Hence for every
`𝔭 ∈ Proj S`: `veroneseHom 𝔭 ∈ D_+(f^d) ⟺ f^d ∉ 𝔭 ∩ S^{(d)} ⟺ f^d ∉ 𝔭 ⟺ f ∉ 𝔭 ⟺ 𝔭 ∈ D_+(f)`, the third `⟺`
using that `𝔭` is prime and `d ≥ 1`. **Note that `m` may be `0`** (the statement has no `0 < m`): the argument
only uses `f^d ∈ S^{(d)}` (`f` homogeneous ⇒ `f^d` has degree `md`, divisible by `d`), which holds for `m = 0` too. -/
theorem AlgebraicGeometry.Proj.veroneseHom_preimage_basicOpen {A σ : Type*} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d)
    (f : A) (m : ℕ) (hf : f ∈ 𝒜 m) :
    AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (veroneseGrading 𝒜 d)
          ⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ =
      AlgebraicGeometry.Proj.basicOpen 𝒜 f := by
  ext 𝔭
  change (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).base 𝔭 ∈
      AlgebraicGeometry.Proj.basicOpen (veroneseGrading 𝒜 d) ⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ ↔
    𝔭 ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 f
  rw [AlgebraicGeometry.Proj.mem_basicOpen, AlgebraicGeometry.Proj.mem_basicOpen,
    AlgebraicGeometry.Proj.veroneseHom_base_mem_asHomogeneousIdeal]
  exact not_congr (𝔭.isPrime.pow_mem_iff_mem d hd)

/-- Compatibility with standard opens: `D_+(f) ⊆ Proj S` corresponds to `D_+(f^d) ⊆ Proj S^{(d)}`.
Proof: `veroneseIso.hom = inv veroneseHom`; transport the preimage using `veroneseHom ≫ inv veroneseHom = 𝟙`, and
the content is `veroneseHom_preimage_basicOpen`. -/

theorem AlgebraicGeometry.Proj.veroneseIso_basicOpen {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) (f : A) (m : ℕ)
    (hf : f ∈ 𝒜 m) :
    (AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f =
      AlgebraicGeometry.Proj.basicOpen (veroneseGrading 𝒜 d) ⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ := by
  have hpre := AlgebraicGeometry.Proj.veroneseHom_preimage_basicOpen 𝒜 d hd f m hf
  have hcomp : (AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom ≫
      AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd =
      CategoryTheory.CategoryStruct.id _ := (AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom_inv_id
  calc (AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f
      = (AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom ⁻¹ᵁ
          (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd ⁻¹ᵁ
            AlgebraicGeometry.Proj.basicOpen (veroneseGrading 𝒜 d)
              ⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩) := by rw [hpre]
    _ = ((AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom ≫
          AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd) ⁻¹ᵁ
          AlgebraicGeometry.Proj.basicOpen (veroneseGrading 𝒜 d)
            ⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ := by
        rw [AlgebraicGeometry.Scheme.Hom.comp_preimage]
    _ = _ := by rw [hcomp]; rfl

end
