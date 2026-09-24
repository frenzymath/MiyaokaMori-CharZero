import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleSectionRing
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleZpowAddIso
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowIsos
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowSectionLocus
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks01q1_FrameChartBasicOpen
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.AmpleCanonicalProjMapOpenImmersion

/-! # An ample invertible sheaf gives an open immersion into Proj (Stacks 01Q1)

Stacks 01Q1 (with 01PY/09MP): if `L` is ample then `X` is separated, and the canonical morphism
`X → Proj Γ_*(X, L)` of Stacks 01PZ (where `Γ_*(X,L) = ⊕_{n≥0} Γ(X, L^{⊗n})`, characterized by
`f⁻¹D₊(s) = X_s` and `a/s^n ↦ a·s^{−n}`) is an open immersion with dense image.

Source: Stacks 01Q1 (properties-lemma-ample-immersion-into-proj); separatedness from 01PY
(properties-lemma-affine-s-opens-cover-quasi-separated) and 09MP.

Structure of the proof:

* `IsAffineOpen.inf_nonvanishingLocus` (Stacks 01PV), via the frame chart
  `IsFrame.inf_nonvanishingLocus_eq_basicOpen` and Mathlib's `isAffineOpen_of_isAffineOpen_basicOpen`;
* `AlgebraicGeometry.IsAmple.quasiSeparatedSpace` — the first paragraph of the proof of Stacks 01PY, from Mathlib's
  `Scheme.quasiSeparatedSpace_of_isOpenCover` and 01PV;
* `IsAmple.valuativeCriterion_uniqueness` (from the second paragraph of 01PY; see its docstring; the auxiliary
  lemmas `Spec_top_le_preimage_of_closedPoint_mem`, `Spec_apply_closedPoint_mem_basicOpen_iff`,
  `ΓSpecIso_appLE_SpecMap_comp`, `appLE_top_res`, `IsFrame.map_coord_eq_mul`,
  `Scheme.Modules.mem_nonvanishingLocus_of_comp_eq` are in this file). This gives `IsAmple.isSeparated`.
* The Proj half: `IsAmple.exists_canonicalProjMap` (01PZ), `IsAmple.isOpenImmersion_of_isCanonicalProjMap` (the
  body of 01Q1) and `IsAmple.dense_range_of_isCanonicalProjMap` (01Q0). The constructions and proofs live in six
  auxiliary modules: `Stacks01q1_GammaStarComponent` (sections of homogeneous elements of `Γ_*(X,L)`, product
  components, nonvanishing loci, multiplication of frame coordinates), `Stacks01q1_AwayRingHom` (the ring
  homomorphism `awayToSections : Γ_*(X,L)_{(x)} → Γ(U, O)`, `a/x^n ↦ a·x^{-n}`, compatible with restriction and
  `awayMap`), `Stacks01q1_CanonicalMapCharts` (the charts `X_s → D₊(s) ⊆ Proj`), `Stacks01q1_CanonicalMap`
  (gluing along `{X_s}` to `canonicalProjMap`, the characterization (1)(2) and uniqueness),
  `Stacks01q1_SectionRingLocalization` (the ring-isomorphism form of 01PW: `awayToSections` is bijective, from the
  two halves of 01PW via the bridge `tensorPowMulIso (s^{⊗n}) = (s^n)_{en}`), and
  `Stacks01q1_CanonicalMapOpenImmersion` (open immersion + dense image).

Together these give `IsAmple.exists_isOpenImmersion_proj`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## Part 1: ample ⇒ separated (Stacks 09MP / 01PY) -/

/-- **Stacks 01PV (`properties-lemma-affine-cap-s-open`): for an affine open `U` and `t ∈ Γ(X, M)` (`M`
invertible), `U ⊓ X_t` is affine.**

Source: Stacks 01PV: "Let `X` be a scheme. Let `L` be an invertible `O_X`-module. Let `s ∈ Γ(X, L)`. For any
affine `U ⊂ X` the intersection `U ∩ X_s` is affine."

Stacks' proof: reduce to commutative algebra with `U = Spec R`, `M|_U` an invertible `R`-module `N`, `t|_U` an
element `s ∈ N`; let `A` be the symmetric algebra of `N`, `B = A/(s − 1)A`; base change shows that `Spec B → Spec R`
factors through `V = {𝔭 | s ∉ 𝔭 N}` and is an isomorphism onto it, so `V = U ∩ X_t` is affine.

The formal proof takes the following alternative route (no symmetric algebra):
1. Let `S ⊆ Γ(X, U)` be the set of `g` such that `M` has a frame on the basic open `D(g) = X.basicOpen g`. Frames
   exist locally (`exists_frame_le`) and the basic opens of the affine open `U` form a basis
   (`IsAffineOpen.exists_basicOpen_le`), so `⨆_{g ∈ S} D(g) = U` and hence `Ideal.span S = ⊤`
   (`IsAffineOpen.iSup_basicOpen_eq_self_iff`).
2. Let `V = U ⊓ X_t` and `r : Γ(X, U) → Γ(X, V)` the restriction; `Ideal.span (r '' S) = ⊤` (`Ideal.map_span`).
3. For `g ∈ S` (with frame `e`): `V.basicOpen (r g) = V ⊓ D(g) = D(g) ⊓ X_t` (`Scheme.basicOpen_res`), and
   `D(g) ⊓ X_t = X.basicOpen (coord_e t)` (the chart description `IsFrame.inf_nonvanishingLocus_eq_basicOpen`,
   `Stacks01q1_FrameChartBasicOpen.lean`), a basic open of the affine open `D(g)` (`IsAffineOpen.basicOpen`),
   hence affine.
4. Mathlib's `isAffineOpen_of_isAffineOpen_basicOpen` (affineness is local, Stacks 01S7) gives that `V` is affine.
Edge cases: for `t = 0`, `X_t = ⊥`, `V = ⊥`, and `r '' S` generates the unit ideal of the zero ring `Γ(X, ⊥)`, so
the conclusion holds trivially; likewise for `U = ⊥`. -/
theorem AlgebraicGeometry.IsAffineOpen.inf_nonvanishingLocus {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) [M.IsLineBundle] (t : Γ(M, ⊤)) {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) :
    AlgebraicGeometry.IsAffineOpen (U ⊓ AlgebraicGeometry.Scheme.Modules.nonvanishingLocus M t) := by
  classical
  set V : X.Opens := U ⊓ AlgebraicGeometry.Scheme.Modules.nonvanishingLocus M t with hV
  -- `S`: the functions in `Γ(X, U)` on whose basic opens `M` has a frame
  set S : Set Γ(X, U) :=
    {g | ∃ e : Γ(M, X.basicOpen g), AlgebraicGeometry.Scheme.Modules.IsFrame M (X.basicOpen g) e}
    with hS
  -- these basic opens cover `U` (frames exist locally + basic opens of an affine open form a basis)
  have hcov : ⨆ g : S, X.basicOpen (g : Γ(X, U)) = U := by
    apply le_antisymm
    · exact iSup_le fun g => X.basicOpen_le _
    · intro x hx
      obtain ⟨W, hWU, hxW, e, he⟩ :=
        AlgebraicGeometry.Scheme.Modules.exists_frame_le M (U := U) (p := x) hx
      obtain ⟨g, hgW, hxg⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hx
      have hgS : g ∈ S := ⟨M.res hgW e, he.restrict hgW⟩
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hgS⟩, hxg⟩
  have hspan : Ideal.span S = ⊤ := hU.iSup_basicOpen_eq_self_iff.mp hcov
  -- after restriction to `V` they still generate the unit ideal
  let r : Γ(X, U) →+* Γ(X, V) := (X.presheaf.map (CategoryTheory.homOfLE (inf_le_left : V ≤ U)).op).hom
  have hspan' : Ideal.span (r '' S) = ⊤ := by
    rw [← Ideal.map_span r S, hspan, Ideal.map_top]
  refine AlgebraicGeometry.isAffineOpen_of_isAffineOpen_basicOpen V (r '' S) hspan' ?_
  rintro _ ⟨g, ⟨e, he⟩, rfl⟩
  -- `V ⊓ D(g) = D(g) ⊓ X_t = D(coord_e t)`, a basic open of the affine open `D(g)`
  have h1 : X.basicOpen (r g) = X.basicOpen g ⊓ AlgebraicGeometry.Scheme.Modules.nonvanishingLocus M t := by
    change X.basicOpen (X.presheaf.map (CategoryTheory.homOfLE (inf_le_left : V ≤ U)).op g) = _
    rw [AlgebraicGeometry.Scheme.basicOpen_res, inf_right_comm,
      inf_eq_right.mpr (X.basicOpen_le g)]
  rw [h1, AlgebraicGeometry.Scheme.Modules.IsFrame.inf_nonvanishingLocus_eq_basicOpen M t he]
  exact (hU.basicOpen g).basicOpen _

/-- **Ample ⇒ quasi-separated** (the first paragraph of the proof of Stacks 01PY).

Stacks: "We show first that `X` is quasi-separated. By assumption we can find a covering of `X` by affine opens of
the form `X_s`. By Lemma 01PV, the intersection of any two such sets is affine, so Schemes, Lemma 01KO implies
that `X` is quasi-separated."

Formalization: the second conjunct of `IsAmple L` gives, for every point `x`, some `m > 0` and `s ∈ Γ(X, L^{⊗m})`
with `x ∈ X_s` and `X_s` affine; indexed by the points of `X`, these `X_s` form an open cover whose pairwise
intersections are affine by `IsAffineOpen.inf_nonvanishingLocus`, hence quasi-compact; then apply Mathlib's
`AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_isOpenCover`. -/
theorem AlgebraicGeometry.IsAmple.quasiSeparatedSpace {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (hL : AlgebraicGeometry.IsAmple L) :
    QuasiSeparatedSpace X := by
  obtain ⟨_, hcov⟩ := hL
  choose m hm s hxs haff using hcov
  refine AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_isOpenCover
    (fun y : X => (AlgebraicGeometry.Scheme.Modules.tensorPow L (m y)).nonvanishingLocus (s y))
    ?_ haff ?_
  · refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun y _ => ?_)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hxs y⟩
  · intro i j
    have h := (haff i).inf_nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.tensorPow L (m j)) (s j)
    simpa using h.isCompact


/-! ### Auxiliary lemmas for the second paragraph of Stacks 01PY

The following lemmas reduce steps 2–5 of 01PY to computations with "the pullback of a function on an open
`V ⊆ X` along a morphism `l : Spec R → X` landing in `V`, as an element of `R`"
(`(ΓSpecIso R).hom (l.appLE V ⊤ _ f)`). -/

namespace AlgebraicGeometry

/-- **The spectrum of a local ring lands in any open containing the image of the closed point**: every point of
`Spec R` specializes to the closed point (`IsLocalRing.specializes_closedPoint`), continuous maps preserve
specialization, and opens are closed under generization. -/
theorem Spec_top_le_preimage_of_closedPoint_mem {X : AlgebraicGeometry.Scheme.{u}} {R : Type u}
    [CommRing R] [IsLocalRing R] (l : AlgebraicGeometry.Spec (.of R) ⟶ X) {V : X.Opens}
    (h : l (IsLocalRing.closedPoint R) ∈ V) : ⊤ ≤ l ⁻¹ᵁ V := by
  intro x _
  exact (IsLocalRing.specializes_closedPoint (R := R) x).mem_open (l ⁻¹ᵁ V).isOpen h

/-- **The image of the closed point lies in `D(f)` ⟺ the pullback of `f` along `l` to `R` is a unit** (`l` landing
in the domain `V` of `f`): `l⁻¹ D(f) = D(l^* f)` (`Scheme.basicOpen_appLE`), on `Spec R` one has
`D(r) = PrimeSpectrum.basicOpen r` (`basicOpen_eq_of_affine'`), and `𝔪_R ∌ r ⟺ r` is a unit. -/
theorem Spec_apply_closedPoint_mem_basicOpen_iff {X : AlgebraicGeometry.Scheme.{u}} {R : Type u}
    [CommRing R] [IsLocalRing R] (l : AlgebraicGeometry.Spec (.of R) ⟶ X) {V : X.Opens}
    (e : ⊤ ≤ l ⁻¹ᵁ V) (f : Γ(X, V)) :
    l (IsLocalRing.closedPoint R) ∈ X.basicOpen f ↔
      IsUnit ((AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).hom.hom ((l.appLE V ⊤ e).hom f)) := by
  have h1 : (AlgebraicGeometry.Spec (.of R)).basicOpen (l.appLE V ⊤ e f) = l ⁻¹ᵁ X.basicOpen f := by
    rw [AlgebraicGeometry.Scheme.basicOpen_appLE, top_inf_eq]
  have h2 : l (IsLocalRing.closedPoint R) ∈ X.basicOpen f ↔
      IsLocalRing.closedPoint R ∈ l ⁻¹ᵁ X.basicOpen f := Iff.rfl
  rw [h2, ← h1, AlgebraicGeometry.basicOpen_eq_of_affine']
  exact (PrimeSpectrum.mem_basicOpen _ _).trans IsLocalRing.notMem_maximalIdeal

/-- `f.appLE ⊤ ⊤ _ = f.appTop` (`⊤ = f⁻¹ᵁ ⊤` holds definitionally). -/
theorem appLE_top_top {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X) (e : ⊤ ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop :=
  (f.app_eq_appLE (U := ⊤)).symm

/-- **Further pullback along `Spec.map φ`**: `(ΓSpecIso K)((Spec.map φ ≫ l)^* f) = φ ((ΓSpecIso R)(l^* f))`
(`appLE_comp_appLE` + `ΓSpecIso_naturality`). -/
theorem ΓSpecIso_appLE_SpecMap_comp {X : AlgebraicGeometry.Scheme.{u}} {R K : Type u} [CommRing R]
    [CommRing K] (φ : R →+* K) (l : AlgebraicGeometry.Spec (.of R) ⟶ X) {V : X.Opens}
    (e : ⊤ ≤ l ⁻¹ᵁ V)
    (e' : ⊤ ≤ (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ) ≫ l) ⁻¹ᵁ V) (f : Γ(X, V)) :
    (AlgebraicGeometry.Scheme.ΓSpecIso (.of K)).hom.hom
        (((AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ) ≫ l).appLE V ⊤ e').hom f) =
      φ ((AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).hom.hom ((l.appLE V ⊤ e).hom f)) := by
  have h0 := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) l V ⊤ ⊤ e le_rfl
  have h2 : (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_rfl =
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)).appTop :=
    AlgebraicGeometry.appLE_top_top _ _
  have h1 : ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ) ≫ l).appLE V ⊤ e').hom f =
      ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)).appTop).hom ((l.appLE V ⊤ e).hom f) := by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← h2, h0]
  rw [h1]
  have h3 := ConcreteCategory.congr_hom
    (AlgebraicGeometry.Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)) ((l.appLE V ⊤ e).hom f)
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h3
  exact h3

/-- **Pullback is compatible with restriction**: for `V' ≤ V` and `l` landing in `V'`, `l^*(f|_{V'}) = l^* f`
(`map_appLE`). -/
theorem appLE_top_res {X Y : AlgebraicGeometry.Scheme.{u}} (l : Y ⟶ X) {V V' : X.Opens} (h : V' ≤ V)
    (e : ⊤ ≤ l ⁻¹ᵁ V) (e' : ⊤ ≤ l ⁻¹ᵁ V') (f : Γ(X, V)) :
    (l.appLE V' ⊤ e').hom ((X.presheaf.map (CategoryTheory.homOfLE h).op).hom f) =
      (l.appLE V ⊤ e).hom f := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, AlgebraicGeometry.Scheme.Hom.map_appLE]

/-- The pullback depends only on the morphism (not on the proof that it lands in `V`). -/
theorem appLE_top_congr {X Y : AlgebraicGeometry.Scheme.{u}} {l l' : Y ⟶ X} (hl : l = l')
    {V : X.Opens} (e : ⊤ ≤ l ⁻¹ᵁ V) (e' : ⊤ ≤ l' ⁻¹ᵁ V) (f : Γ(X, V)) :
    (l.appLE V ⊤ e).hom f = (l'.appLE V ⊤ e').hom f := by
  subst hl; rfl

namespace Scheme.Modules

/-- **Change of coordinates between two frames**: `e₂` a frame of `M` on `V`, `e₁` a frame on `V₁`, `σ ∈ Γ(M, ⊤)`;
on `W = V ⊓ V₁` one has `e₁ = w • e₂` (`w := coord_{e₂}(e₁|_W)`), hence
`coord_{e₂}(σ)|_W = coord_{e₁}(σ)|_W * w`. -/
theorem IsFrame.map_coord_eq_mul' {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} {V V₁ : X.Opens}
    {e₂ : Γ(M, V)} {e₁ : Γ(M, V₁)} (h₂ : IsFrame M V e₂) (h₁ : IsFrame M V₁ e₁) (σ : Γ(M, ⊤)) :
    X.presheaf.map (CategoryTheory.homOfLE (inf_le_left : V ⊓ V₁ ≤ V)).op
        (h₂.coord le_rfl (M.res le_top σ)) =
      X.presheaf.map (CategoryTheory.homOfLE (inf_le_right : V ⊓ V₁ ≤ V₁)).op
          (h₁.coord le_rfl (M.res le_top σ)) *
        h₂.coord inf_le_left (M.res inf_le_right e₁) := by
  rw [← h₂.coord_map inf_le_left le_rfl]
  apply h₂.coord_unique
  have hσ₁ := h₁.coord_smul_frame le_rfl (M.res le_top σ)
  rw [res_self] at hσ₁
  rw [mul_smul, h₂.coord_smul_frame, ← res_smul, hσ₁, res_res, res_res]

/-- `IsFrame.map_coord_eq_mul'` written with `.hom`. -/
theorem IsFrame.map_coord_eq_mul {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} {V V₁ : X.Opens}
    {e₂ : Γ(M, V)} {e₁ : Γ(M, V₁)} (h₂ : IsFrame M V e₂) (h₁ : IsFrame M V₁ e₁) (σ : Γ(M, ⊤)) :
    (X.presheaf.map (CategoryTheory.homOfLE (inf_le_left : V ⊓ V₁ ≤ V)).op).hom
        (h₂.coord le_rfl (M.res le_top σ)) =
      (X.presheaf.map (CategoryTheory.homOfLE (inf_le_right : V ⊓ V₁ ≤ V₁)).op).hom
          (h₁.coord le_rfl (M.res le_top σ)) *
        h₂.coord inf_le_left (M.res inf_le_right e₁) :=
  h₂.map_coord_eq_mul' h₁ σ

/-- **Steps 3–4 of the proof of Stacks 01PY (independent of valuation rings; only `R` local and `φ : R → K`
injective are used)**: `M` a line bundle, `σ, τ ∈ Γ(M, ⊤)`; `l₁, l₂ : Spec R → X` agree after composition with
`Spec.map φ`; if `l₁(closed point) ∈ X_σ` and `l₂(closed point) ∈ X_τ`, then `l₂(closed point) ∈ X_σ`.

Proof: take a frame `(V, e₂)` of `M` near `x₂ := l₂(closed point)` and a frame `(V₁, e₁)` near
`x₁ := l₁(closed point)`; `l₂` lands in `V` and `l₁` in `V₁` (`Spec_top_le_preimage_of_closedPoint_mem`). Let
`f_σ, f_τ ∈ Γ(X, V)` be the coordinates of `σ, τ` in `e₂`, and `g_σ, g_τ ∈ Γ(X, V₁)` those in `e₁`. The chart
description (`IsFrame.inf_nonvanishingLocus_eq_basicOpen` + `Spec_apply_closedPoint_mem_basicOpen_iff`) gives
`x₂ ∈ X_s ⟺ l₂^* f_s ∈ Rˣ` and `x₁ ∈ X_s ⟺ l₁^* g_s ∈ Rˣ`. So `l₁^* g_σ`, `l₂^* f_τ` are units, and we must show
that `l₂^* f_σ` is a unit. On `W = V ⊓ V₁`, `e₁ = w • e₂`, so `f_σ|_W = g_σ|_W · w` and `f_τ|_W = g_τ|_W · w`,
whence `f_σ|_W · g_τ|_W = g_σ|_W · f_τ|_W` (`IsFrame.map_coord_eq_mul`). Pulling back to `K` along
`j := Spec.map φ ≫ l₂ = Spec.map φ ≫ l₁` (landing in `W`), using `ΓSpecIso_appLE_SpecMap_comp` and
`appLE_top_res`, gives `φ(l₂^* f_σ) · φ(l₁^* g_τ) = φ(l₁^* g_σ) · φ(l₂^* f_τ)`; `φ` is injective, so
`l₂^* f_σ · l₁^* g_τ = l₁^* g_σ · l₂^* f_τ ∈ Rˣ`, hence `l₂^* f_σ ∈ Rˣ`.

Note: `σ, τ` must be sections of the **same** line bundle — for different line bundles the conclusion is false
(the affine line with doubled origin and two mutually inverse twisted line bundles give a counterexample); this is
why Stacks replaces `s, t` by `s^q, t^p`. -/
theorem mem_nonvanishingLocus_of_comp_eq {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules}
    [M.IsLineBundle] (σ τ : Γ(M, ⊤)) {R K : Type u} [CommRing R] [IsLocalRing R] [CommRing K]
    (φ : R →+* K) (hφ : Function.Injective φ) (l₁ l₂ : AlgebraicGeometry.Spec (.of R) ⟶ X)
    (hl : AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ) ≫ l₁ =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ) ≫ l₂)
    (h₁ : l₁ (IsLocalRing.closedPoint R) ∈ M.nonvanishingLocus σ)
    (h₂ : l₂ (IsLocalRing.closedPoint R) ∈ M.nonvanishingLocus τ) :
    l₂ (IsLocalRing.closedPoint R) ∈ M.nonvanishingLocus σ := by
  obtain ⟨V, hx₂, e₂, he₂⟩ := exists_frame M (l₂ (IsLocalRing.closedPoint R))
  obtain ⟨V₁, hx₁, e₁, he₁⟩ := exists_frame M (l₁ (IsLocalRing.closedPoint R))
  have eV : ⊤ ≤ l₂ ⁻¹ᵁ V := AlgebraicGeometry.Spec_top_le_preimage_of_closedPoint_mem l₂ hx₂
  have eV₁ : ⊤ ≤ l₁ ⁻¹ᵁ V₁ := AlgebraicGeometry.Spec_top_le_preimage_of_closedPoint_mem l₁ hx₁
  -- chart: the image of the closed point lies in `X_s` ⟺ the coordinate pulled back to `R` is a unit
  have chart : ∀ {W : X.Opens} {e : Γ(M, W)} (he : IsFrame M W e)
      (l : AlgebraicGeometry.Spec (.of R) ⟶ X) (hx : l (IsLocalRing.closedPoint R) ∈ W)
      (eW : ⊤ ≤ l ⁻¹ᵁ W) (s : Γ(M, ⊤)),
      l (IsLocalRing.closedPoint R) ∈ M.nonvanishingLocus s ↔
        IsUnit ((AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).hom.hom
          ((l.appLE W ⊤ eW).hom (he.coord le_rfl (M.res le_top s)))) := by
    intro W e he l hx eW s
    rw [← AlgebraicGeometry.Spec_apply_closedPoint_mem_basicOpen_iff l eW,
      ← he.inf_nonvanishingLocus_eq_basicOpen M s]
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  rw [chart he₂ l₂ hx₂ eV]
  have u₁ := (chart he₁ l₁ hx₁ eV₁ σ).mp h₁
  have u₂ := (chart he₂ l₂ hx₂ eV τ).mp h₂
  set ι := AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ) with hι
  -- `j := ι ≫ l₂` lands in `W = V ⊓ V₁`
  have eW : ⊤ ≤ (ι ≫ l₂) ⁻¹ᵁ (V ⊓ V₁) := by
    intro x _
    have hxV : l₂ (ι x) ∈ V := eV (show ι x ∈ (⊤ : (AlgebraicGeometry.Spec (.of R)).Opens) from trivial)
    have hxV₁ : l₁ (ι x) ∈ V₁ :=
      eV₁ (show ι x ∈ (⊤ : (AlgebraicGeometry.Spec (.of R)).Opens) from trivial)
    have hx : l₁ (ι x) = l₂ (ι x) := by
      rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, ← AlgebraicGeometry.Scheme.Hom.comp_apply, hl]
    change (ι ≫ l₂) x ∈ V ∧ (ι ≫ l₂) x ∈ V₁
    rw [AlgebraicGeometry.Scheme.Hom.comp_apply]
    exact ⟨hxV, hx ▸ hxV₁⟩
  have eW₂ : ⊤ ≤ (ι ≫ l₂) ⁻¹ᵁ V := eW.trans ((ι ≫ l₂).preimage_mono inf_le_left)
  have eW₁ : ⊤ ≤ (ι ≫ l₂) ⁻¹ᵁ V₁ := eW.trans ((ι ≫ l₂).preimage_mono inf_le_right)
  have eW₁' : ⊤ ≤ (ι ≫ l₁) ⁻¹ᵁ V₁ := by rw [hl]; exact eW₁
  -- write the four elements of `R`, via `φ`, as functions on `W` pulled back to `K` along `j`
  have p₂ : ∀ f : Γ(X, V),
      φ ((AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).hom.hom ((l₂.appLE V ⊤ eV).hom f)) =
        (AlgebraicGeometry.Scheme.ΓSpecIso (.of K)).hom.hom (((ι ≫ l₂).appLE (V ⊓ V₁) ⊤ eW).hom
          ((X.presheaf.map (CategoryTheory.homOfLE (inf_le_left : V ⊓ V₁ ≤ V)).op).hom f)) := by
    intro f
    rw [AlgebraicGeometry.appLE_top_res (ι ≫ l₂) inf_le_left eW₂ eW f,
      AlgebraicGeometry.ΓSpecIso_appLE_SpecMap_comp φ l₂ eV eW₂ f]
  have p₁ : ∀ g : Γ(X, V₁),
      φ ((AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).hom.hom ((l₁.appLE V₁ ⊤ eV₁).hom g)) =
        (AlgebraicGeometry.Scheme.ΓSpecIso (.of K)).hom.hom (((ι ≫ l₂).appLE (V ⊓ V₁) ⊤ eW).hom
          ((X.presheaf.map (CategoryTheory.homOfLE (inf_le_right : V ⊓ V₁ ≤ V₁)).op).hom g)) := by
    intro g
    rw [AlgebraicGeometry.appLE_top_res (ι ≫ l₂) inf_le_right eW₁ eW g,
      ← AlgebraicGeometry.appLE_top_congr hl eW₁' eW₁ g,
      AlgebraicGeometry.ΓSpecIso_appLE_SpecMap_comp φ l₁ eV₁ eW₁' g]
  have key : (AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).hom.hom
        ((l₂.appLE V ⊤ eV).hom (he₂.coord le_rfl (M.res le_top σ))) *
      (AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).hom.hom
        ((l₁.appLE V₁ ⊤ eV₁).hom (he₁.coord le_rfl (M.res le_top τ))) =
      (AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).hom.hom
        ((l₁.appLE V₁ ⊤ eV₁).hom (he₁.coord le_rfl (M.res le_top σ))) *
      (AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).hom.hom
        ((l₂.appLE V ⊤ eV).hom (he₂.coord le_rfl (M.res le_top τ))) := by
    apply hφ
    rw [map_mul, map_mul, p₂, p₂, p₁, p₁, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    rw [he₂.map_coord_eq_mul he₁ σ, he₂.map_coord_eq_mul he₁ τ]
    ring
  have hu : IsUnit ((AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).hom.hom
        ((l₂.appLE V ⊤ eV).hom (he₂.coord le_rfl (M.res le_top σ))) *
      (AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).hom.hom
        ((l₁.appLE V₁ ⊤ eV₁).hom (he₁.coord le_rfl (M.res le_top τ)))) := by
    rw [key]; exact u₁.mul u₂
  exact isUnit_of_mul_isUnit_left hu

end Scheme.Modules

end AlgebraicGeometry

/-- **Stacks 01PY, from the second paragraph of the proof: if `X` carries an invertible sheaf satisfying the ample
condition, then `X → Spec ℤ` satisfies the uniqueness part of the valuative criterion of separatedness.**

Source: Stacks 01PY (`properties-lemma-affine-s-opens-cover-quasi-separated`); the criterion itself is Stacks
01KZ/01L0 (Mathlib `AlgebraicGeometry.IsSeparated.of_valuativeCriterion`).

Stacks' proof: let `A` be a valuation ring with fraction field `K`, and `f, g : Spec A → X` two morphisms whose
composites `Spec K → Spec A → X` agree. (1) `A` is local, so the image of `Spec A` is contained in any open
containing the image of the closed point; choose `p, q ≥ 1`, `s ∈ Γ(X, L^{⊗p})`, `t ∈ Γ(X, L^{⊗q})` with `X_s`,
`X_t` affine, `f(Spec A) ⊆ X_s`, `g(Spec A) ⊆ X_t`. (2) Replace `s, t, L` by `s^q, t^p, L^{⊗pq}`, which does not
change `X_s`, `X_t`, so that `s, t` are sections of the same sheaf. (3)–(4) The pullbacks `f^*L`, `g^*L` are free
`A`-modules `M`, `N` of rank 1, identified after `⊗_A K`; the pullback `x` of `s` generates `M`, and the argument
symmetric in `s, t` shows that its image `y` generates `N`, so `g(Spec A) ⊆ X_s`. (5) `X_s` is affine, so `f, g`
are determined by ring maps `Γ(X_s, O) → A`, which agree after the injection `A → K`; hence `f = g`.

The formal proof follows this route, but steps 3–4 use **frame coordinates** throughout (so neither the freeness
of the pulled-back invertible sheaf over a local ring nor any property of valuation rings is needed — only `R`
local and `R → K` injective):
1. `X_s` (`s ∈ Γ(L^{⊗p})`) and `X_t` (`t ∈ Γ(L^{⊗q})`) containing the images of the closed point, from the second
   conjunct of `IsAmple`.
2. Pass to sections of the same line bundle `M := L^{⊗pq}`: `σ := (tensorPowMulIso L p q)(s^{⊗q})`,
   `τ := (tensorPowMulIso L q p ≪≫ eqToIso)(t^{⊗p})`, with `X_σ = X_s`, `X_τ = X_t`
   (`nonvanishingLocus_iso` + `nonvanishingLocus_tensorPowSection`).
3–4. `Scheme.Modules.mem_nonvanishingLocus_of_comp_eq` (this file): `l₁(closed point) ∈ X_σ`,
   `l₂(closed point) ∈ X_τ`, `l₁, l₂` agree on `Spec K` ⟹ `l₂(closed point) ∈ X_σ`. See its docstring (change
   of coordinates between two frames + pullback along `Spec K → X` and injectivity of `R → K`).
5. `l₁, l₂` both land in the affine open `U = X_s` (`Spec_top_le_preimage_of_closedPoint_mem`); lift them to `U`
   with `IsOpenImmersion.lift` and apply `ext_of_isAffine`: the two ring maps `Γ(U) → Γ(Spec R) ≅ R` agree after
   composition with `R → K` (`ΓSpecIso_appLE_SpecMap_comp` + agreement on `Spec K`), and `R → K` is injective.

Mathlib lemmas used: `ValuativeCriterion.Uniqueness`, `ValuativeCommSq`, `CommSq.LiftStruct.ext`,
`IsLocalRing.specializes_closedPoint`, `Scheme.basicOpen_appLE`, `basicOpen_eq_of_affine'`,
`Scheme.Hom.appLE_comp_appLE`, `Scheme.Hom.map_appLE`, `Scheme.ΓSpecIso_naturality`,
`IsOpenImmersion.lift`/`lift_fac`, `ext_of_isAffine`, `IsFractionRing.injective`. -/
theorem AlgebraicGeometry.IsAmple.valuativeCriterion_uniqueness
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle]
    (hL : AlgebraicGeometry.IsAmple L) :
    AlgebraicGeometry.ValuativeCriterion.Uniqueness
      (CategoryTheory.Limits.terminal.from X) := by
  rintro ⟨R, K, i₁, i₂, ⟨w⟩⟩
  constructor
  rintro ⟨l₁, hl₁, -⟩ ⟨l₂, hl₂, -⟩
  ext : 1
  dsimp only at hl₁ hl₂ ⊢
  have hl : AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l₁ =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l₂ := hl₁.trans hl₂.symm
  -- step 1: the affine `X_s`, `X_t` containing the images of the closed point
  obtain ⟨p, hp, s, hxs, haffs⟩ := hL.2 (l₁ (IsLocalRing.closedPoint R))
  obtain ⟨q, hq, t, hxt, -⟩ := hL.2 (l₂ (IsLocalRing.closedPoint R))
  -- step 2: pass to sections `σ = s^{⊗q}`, `τ = t^{⊗p}` of the same line bundle `M := L^{⊗(pq)}`
  obtain ⟨σ, hσdef⟩ : ∃ σ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (p * q), ⊤),
      σ = (AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L p q).hom.app ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection
          (s : ((AlgebraicGeometry.Scheme.Modules.tensorPow L p).val.obj (Opposite.op ⊤) : Type u)) q) :=
    ⟨_, rfl⟩
  obtain ⟨τ, hτdef⟩ : ∃ τ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (p * q), ⊤),
      τ = (AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L q p ≪≫
        CategoryTheory.eqToIso
          (congrArg (AlgebraicGeometry.Scheme.Modules.tensorPow L) (mul_comm q p))).hom.app ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection
          (t : ((AlgebraicGeometry.Scheme.Modules.tensorPow L q).val.obj (Opposite.op ⊤) : Type u)) p) :=
    ⟨_, rfl⟩
  have hσ : (AlgebraicGeometry.Scheme.Modules.tensorPow L (p * q)).nonvanishingLocus σ =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L p).nonvanishingLocus s := by
    rw [hσdef]
    exact (AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso
      (AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L p q) _).trans
      (AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_tensorPowSection _ s hq)
  have hτ : (AlgebraicGeometry.Scheme.Modules.tensorPow L (p * q)).nonvanishingLocus τ =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L q).nonvanishingLocus t := by
    rw [hτdef]
    exact (AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso
      (AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L q p ≪≫
        CategoryTheory.eqToIso
          (congrArg (AlgebraicGeometry.Scheme.Modules.tensorPow L) (mul_comm q p))) _).trans
      (AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_tensorPowSection _ t hp)
  -- steps 3–4: `l₂(closed point) ∈ X_σ = X_s`
  have h₁ : l₁ (IsLocalRing.closedPoint R) ∈
      (AlgebraicGeometry.Scheme.Modules.tensorPow L (p * q)).nonvanishingLocus σ := by
    rw [hσ]; exact hxs
  have h₂ : l₂ (IsLocalRing.closedPoint R) ∈
      (AlgebraicGeometry.Scheme.Modules.tensorPow L (p * q)).nonvanishingLocus τ := by
    rw [hτ]; exact hxt
  have h₂' : l₂ (IsLocalRing.closedPoint R) ∈
      (AlgebraicGeometry.Scheme.Modules.tensorPow L (p * q)).nonvanishingLocus σ :=
    AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_of_comp_eq σ τ (algebraMap R K)
      (IsFractionRing.injective R K) l₁ l₂ hl h₁ h₂
  rw [hσ] at h₁ h₂'
  -- step 5: `l₁, l₂` both factor through the affine open `U := X_s` and are determined by `Γ(U) → R → K`
  set U : X.Opens := (AlgebraicGeometry.Scheme.Modules.tensorPow L p).nonvanishingLocus s with hU
  have eU₁ : ⊤ ≤ l₁ ⁻¹ᵁ U := AlgebraicGeometry.Spec_top_le_preimage_of_closedPoint_mem l₁ h₁
  have eU₂ : ⊤ ≤ l₂ ⁻¹ᵁ U := AlgebraicGeometry.Spec_top_le_preimage_of_closedPoint_mem l₂ h₂'
  have hr₁ : Set.range l₁ ⊆ Set.range U.ι := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact eU₁ (show x ∈ (⊤ : (AlgebraicGeometry.Spec (.of R)).Opens) from trivial)
  have hr₂ : Set.range l₂ ⊆ Set.range U.ι := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact eU₂ (show x ∈ (⊤ : (AlgebraicGeometry.Spec (.of R)).Opens) from trivial)
  set l₁' := AlgebraicGeometry.IsOpenImmersion.lift U.ι l₁ hr₁ with hl₁'
  set l₂' := AlgebraicGeometry.IsOpenImmersion.lift U.ι l₂ hr₂ with hl₂'
  have hf₁ : l₁' ≫ U.ι = l₁ := AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  have hf₂ : l₂' ≫ U.ι = l₂ := AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  have : AlgebraicGeometry.IsAffine U.toScheme := haffs
  set ι := AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R K)) with hι
  have hl' : ι ≫ l₁' = ι ≫ l₂' := by
    rw [← CategoryTheory.cancel_mono U.ι, CategoryTheory.Category.assoc, CategoryTheory.Category.assoc,
      hf₁, hf₂]
    exact hl
  rw [← hf₁, ← hf₂]
  congr 1
  apply AlgebraicGeometry.ext_of_isAffine
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  -- `Γ(Spec R, ⊤) ≅ R ↪ K` is injective
  have hinj : Function.Injective (fun r : Γ(AlgebraicGeometry.Spec (.of R), ⊤) =>
      algebraMap R K ((AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).hom.hom r)) := by
    refine (IsFractionRing.injective R K).comp ?_
    intro r r' h
    have := congrArg (AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).inv.hom h
    simpa using this
  apply hinj
  have k₁ := AlgebraicGeometry.ΓSpecIso_appLE_SpecMap_comp (algebraMap R K) l₁' (V := ⊤) le_top le_top a
  have k₂ := AlgebraicGeometry.ΓSpecIso_appLE_SpecMap_comp (algebraMap R K) l₂' (V := ⊤) le_top le_top a
  have e₁ : l₁'.appLE ⊤ ⊤ le_top = l₁'.appTop := AlgebraicGeometry.appLE_top_top _ _
  have e₂ : l₂'.appLE ⊤ ⊤ le_top = l₂'.appTop := AlgebraicGeometry.appLE_top_top _ _
  rw [e₁] at k₁
  rw [e₂] at k₂
  dsimp only
  rw [← k₁, ← k₂]
  exact congrArg _ (AlgebraicGeometry.appLE_top_congr hl' le_top le_top a)

/- Ample ⇒ separated (Stacks 01PY + 09MP; the first sentence of the proof of 01Q1). -/

theorem AlgebraicGeometry.IsAmple.isSeparated {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (hL : AlgebraicGeometry.IsAmple L) : X.IsSeparated := by
  have hqs : AlgebraicGeometry.QuasiSeparated (CategoryTheory.Limits.terminal.from X) :=
    (AlgebraicGeometry.quasiSeparatedSpace_iff_quasiSeparated X).mp
      (AlgebraicGeometry.IsAmple.quasiSeparatedSpace L hL)
  exact ⟨AlgebraicGeometry.IsSeparated.of_valuativeCriterion _
    (AlgebraicGeometry.IsAmple.valuativeCriterion_uniqueness L hL)⟩

/-! ## Part 2: `X → Proj Γ_*(X, L)` is an open immersion with dense image (Stacks 01Q1) -/

/- Characterization of the canonical morphism `f : U → Proj Γ_*(X, L)` of 01PZ
   (`U = ⋃_{s homogeneous of positive degree} X_s`): (1) `f⁻¹(D₊(s)) = X_s`; (2) on `D₊(s)`, the pullback `φ` of a
   homogeneous fraction `a/s^n` (`a ∈ Γ(X, L^{⊗nd})`) satisfies `φ · s^n = a`. Condition (2) determines `φ` on
   `X_s` uniquely (`s^n` is nowhere vanishing on `X_s`), so a morphism satisfying (1)(2) is unique. -/

def AlgebraicGeometry.IsAmple.IsCanonicalProjMap {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle]
    (f : X ⟶ AlgebraicGeometry.Proj (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)) : Prop :=
  ∀ (d : ℕ) (_ : 0 < d) (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L d, ⊤)),
    f ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
        (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s) =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s ∧
    ∀ (n : ℕ) (a : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (n • d), ⊤)),
      let V := AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
        (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s)
      let φ : Γ(X, f ⁻¹ᵁ V) := (f.app V).hom
        ((AlgebraicGeometry.Proj.awayToSection (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
          (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s)).hom
          (HomogeneousLocalization.Away.mk (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
            (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L d s) n
            (AlgebraicGeometry.Scheme.Modules.gammaStarOf L (n • d) a)
            (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L (n • d) a)))
      φ • ((AlgebraicGeometry.Scheme.Modules.tensorPow L (n • d)).presheaf.map
          (CategoryTheory.homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)).op).hom
          (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L
            (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s ^ n) (n • d)) =
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L (n • d)).presheaf.map
          (CategoryTheory.homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)).op).hom a

/-- **Stacks 01PZ (`properties-lemma-map-into-proj`): the canonical morphism exists and is unique.**

Source: Stacks 01PZ. `S := Γ_*(X, L) = ⊕_{n ≥ 0} Γ(X, L^{⊗n})` (`Scheme.Modules.gammaStarGrading`). `L` ample ⟹
every point lies in some `X_s` (`s` homogeneous of positive degree), so the open `U = ⋃_{s} X_s` of 01PZ is all of
`X`.

Proof (Stacks 01PZ):
1. For every homogeneous `s ∈ S_d` (`d > 0`), `D₊(s) ⊆ Proj S` is an affine open with `Γ(D₊(s), O) = S_{(s)}`
   (the degree-`0` part of the homogeneous localization; Mathlib `Proj.awayι` / `Proj.basicOpenIsoSpec`).
2. Construct the ring map `S_{(s)} → Γ(X_s, O_X)`, `a/s^n ↦ a ⊗ s^{−n}`, where `a ∈ Γ(X, L^{⊗nd})` and `s^{−n}` is
   the inverse of `s^n` on `X_s` (`s` is nowhere vanishing on `X_s`, so `s^n` is an isomorphism
   `O_{X_s} ≅ L^{⊗nd}|_{X_s}`). The map is compatible with addition and multiplication of `S_{(s)}`, hence a ring
   map.
3. `X_s` and `D₊(s)` are affine (the former by ampleness, the latter by Proj), so the ring map gives
   `X_s → D₊(s)`; these morphisms are compatible on `X_s ∩ X_t = X_{st}` (both are determined by
   `S_{(st)} → Γ(X_{st}, O)`), hence glue to `f : X → Proj S` with `f⁻¹(D₊(s)) = X_s`.
4. Uniqueness: let `g` also satisfy (1)(2). For homogeneous `s` (degree `d > 0`), both `g` and `f` send `X_s` into
   the affine open `D₊(s) ≅ Spec S_{(s)}`, so each is determined by a ring map `S_{(s)} → Γ(X_s, O)`; condition (2)
   says this ring map sends `a/s^n` to the `φ` with `φ · s^n|_{X_s} = a|_{X_s}`, and multiplication by `s^n` is
   an isomorphism `O_{X_s} → L^{⊗nd}|_{X_s}`, so `φ` is unique. Hence `f` and `g` agree on every `X_s`, and the
   `X_s` cover `X`, so `g = f`.

In the formalization, `L^{⊗−n}` never appears: `a ⊗ s^{−n}` is written as the coordinate (`IsFrame.coord`) of
`a|_{X_s}` in the frame `s^n|_{X_s}` on `X_s`. The ring homomorphism `a/s^n ↦ coord_{s^n}(a)` is
`Scheme.Modules.awayToSections` (`Stacks01q1_AwayRingHom.lean`), whose ring-homomorphism axioms all follow from
the defining equation "coordinate × frame = section" and the bilinearity of the graded multiplication; the chart
`X_s → Spec Γ_*(X,L)_{(s)} → Proj` is `projChart` (`Stacks01q1_CanonicalMapCharts.lean`), glued along `{X_s}` by
Mathlib's `Scheme.OpenCover.glueMorphisms` into `canonicalProjMap` (`Stacks01q1_CanonicalMap.lean`); the
characterization (1)(2) is `isCanonicalProjMap'_canonicalProjMap` and uniqueness is
`eq_canonicalProjMap_of_isCanonicalProjMap'` (on each `X_s` both morphisms land in the affine open `D₊(s)` and are
determined by `ext_of_isAffine` and (2)). -/
theorem AlgebraicGeometry.IsAmple.exists_canonicalProjMap {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (hL : AlgebraicGeometry.IsAmple L) :
    ∃ f : X ⟶ AlgebraicGeometry.Proj (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L),
      AlgebraicGeometry.IsAmple.IsCanonicalProjMap L f ∧
      ∀ g : X ⟶ AlgebraicGeometry.Proj (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L),
        AlgebraicGeometry.IsAmple.IsCanonicalProjMap L g → g = f := by
  have hcov : ∀ p : X, ∃ (d : ℕ) (_ : 0 < d) (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L d, ⊤)),
      p ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s := fun p => by
    obtain ⟨m, hm, s, hp, -⟩ := hL.2 p
    exact ⟨m, hm, s, hp⟩
  exact ⟨AlgebraicGeometry.Scheme.Modules.canonicalProjMap L hcov,
    AlgebraicGeometry.Scheme.Modules.isCanonicalProjMap'_canonicalProjMap L hcov,
    fun g hg => AlgebraicGeometry.Scheme.Modules.eq_canonicalProjMap_of_isCanonicalProjMap' L hcov hg⟩

/-- **The body of Stacks 01Q1: the canonical morphism is an open immersion.**

Source: Stacks 01Q1 (`properties-lemma-ample-immersion-into-proj`).

Proof:
1. `X` is quasi-compact (the definition of ample includes `CompactSpace X`) and quasi-separated
   (`IsAmple.quasiSeparatedSpace`).
2. Take finitely many homogeneous `s_1, …, s_r ∈ S_+` of degrees `d_i > 0` with `X_{s_i}` affine and
   `X = ⋃_i X_{s_i}` (every point lies in some `X_s`; `X` quasi-compact, so take a finite subcover). By the
   canonical property (1), `f⁻¹(D₊(s_i)) = X_{s_i}`.
3. By Stacks 01PW (`Stacks01pw.lean`): for `X` quasi-compact and quasi-separated,
   `Γ_*(X, L)_{(s)} → Γ(X_s, O_X)`, `a/s^n ↦ a ⊗ s^{−n}`, is an isomorphism. By the construction of Proj the left
   side is `Γ(D₊(s_i), O_{Proj S})` (Mathlib `Proj.awayι` / `Proj.basicOpenIsoSpec`).
4. `X_{s_i}` and `D₊(s_i)` are affine and the ring map induced by `f` between them is an isomorphism (step 3), so
   `f|_{X_{s_i}} : X_{s_i} → D₊(s_i)` is an isomorphism.
5. The `X_{s_i}` cover `X` and each `f|_{X_{s_i}}` is an isomorphism onto an open subscheme, so `f` is an open
   immersion (Mathlib `IsOpenImmersion.of_openCover_source`; the same technique as in `Stacks0b5j.lean`).

In the formalization, uniqueness gives `f = canonicalProjMap`, reducing to `isOpenImmersion_canonicalProjMap`
(`Stacks01q1_CanonicalMapOpenImmersion.lean`): the ring-isomorphism form of step 3 is `awayToSections_bijective`
(`Stacks01q1_SectionRingLocalization.lean`), obtained from the two halves of 01PW
(`exists_sectionTensor_tensorPowSection_eq_zero`, `exists_tensorPow_section_restrict_eq`) via the bridge
`tensorPowMulIso_hom_app_tensorPowSection` (`(L^{⊗e})^{⊗n} ≅ L^{⊗en}` sends `s^{⊗n}` to the section `s^n`); steps
4–5 use `IsAffineOpen.isoSpec_hom`, `ConcreteCategory.isIso_iff_bijective` and Mathlib's
`IsOpenImmersion.of_openCover_source` (an open cover of the source + injectivity on points). -/
theorem AlgebraicGeometry.IsAmple.isOpenImmersion_of_isCanonicalProjMap
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle]
    (hL : AlgebraicGeometry.IsAmple L)
    (f : X ⟶ AlgebraicGeometry.Proj (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L))
    (hf : AlgebraicGeometry.IsAmple.IsCanonicalProjMap L f) :
    AlgebraicGeometry.IsOpenImmersion f := by
  have hcov : ∀ p : X, ∃ (d : ℕ) (_ : 0 < d) (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L d, ⊤)),
      p ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s := fun p => by
    obtain ⟨m, hm, s, hp, -⟩ := hL.2 p
    exact ⟨m, hm, s, hp⟩
  have : CompactSpace X := hL.1
  have : QuasiSeparatedSpace X := AlgebraicGeometry.IsAmple.quasiSeparatedSpace L hL
  rw [AlgebraicGeometry.Scheme.Modules.eq_canonicalProjMap_of_isCanonicalProjMap' L hcov hf]
  exact AlgebraicGeometry.Scheme.Modules.isOpenImmersion_canonicalProjMap L hcov hL.2

/-- **Stacks 01Q0 (`properties-lemma-map-into-proj-quasi-compact`): the canonical morphism has dense image.**

Source: Stacks 01Q0; the last sentence of 01Q1 ("the image is dense").

Proof:
1. Let `Z = closure (range f)`, a closed subset of `Proj S`; we show `Z = Proj S`.
2. The `D₊(s)` (`s ∈ S_+` homogeneous) form a basis of `Proj S`. Suppose `D₊(s) ≠ ∅`; we show
   `D₊(s) ∩ range f ≠ ∅`.
3. `D₊(s) ≠ ∅` ⟺ `s` is not nilpotent ⟺ `S_{(s)} ≠ 0`. By the canonical property (1), `f⁻¹(D₊(s)) = X_s`; by
   Stacks 01PW (`X` quasi-compact and quasi-separated), `S_{(s)} ≅ Γ(X_s, O_X)`. So `Γ(X_s, O_X) ≠ 0`, hence
   `X_s ≠ ∅` (the ring of global sections of the empty scheme is the zero ring), i.e. `f⁻¹(D₊(s)) ≠ ∅`, so `D₊(s)`
   meets the image.
4. Every nonempty open contains a nonempty `D₊(s)`, so the image meets every nonempty open, i.e. it is dense.

The formalization (`dense_range_canonicalProjMap`, `Stacks01q1_CanonicalMapOpenImmersion.lean`) avoids
"`S_{(s)} ≠ 0 ⟺ D₊(s) ≠ ∅`" and shows directly that `X_y = ∅ ⟹ y` nilpotent (`y_m|_{X_y} = 0` holds trivially and
01PW(1) gives `y·y^k = 0`), hence `D₊(y) = D₊(y^{k+1}) = ∅`; a nonempty open contains a nonempty `D₊(y)` with `y`
homogeneous of positive degree (basic opens form a basis + homogeneous components + `Proj.affineOpenCover`). -/
theorem AlgebraicGeometry.IsAmple.dense_range_of_isCanonicalProjMap
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle]
    (hL : AlgebraicGeometry.IsAmple L)
    (f : X ⟶ AlgebraicGeometry.Proj (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L))
    (hf : AlgebraicGeometry.IsAmple.IsCanonicalProjMap L f) :
    Dense (Set.range f.base) := by
  have hcov : ∀ p : X, ∃ (d : ℕ) (_ : 0 < d) (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L d, ⊤)),
      p ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s := fun p => by
    obtain ⟨m, hm, s, hp, -⟩ := hL.2 p
    exact ⟨m, hm, s, hp⟩
  have : CompactSpace X := hL.1
  rw [AlgebraicGeometry.Scheme.Modules.eq_canonicalProjMap_of_isCanonicalProjMap' L hcov hf]
  exact AlgebraicGeometry.Scheme.Modules.dense_range_canonicalProjMap L hcov

/- Stacks 01Q1: if `L` is ample, the canonical morphism of 01PZ is defined on all of `X` (`U = X`) and is an
   open immersion `X → Proj Γ_*(X, L)` with dense image; canonicity is expressed as uniqueness of morphisms
   satisfying `IsCanonicalProjMap`. -/

theorem AlgebraicGeometry.IsAmple.exists_isOpenImmersion_proj {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (hL : AlgebraicGeometry.IsAmple L) :
    ∃ f : X ⟶ AlgebraicGeometry.Proj (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L),
      AlgebraicGeometry.IsAmple.IsCanonicalProjMap L f ∧
      (∀ g : X ⟶ AlgebraicGeometry.Proj (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L),
        AlgebraicGeometry.IsAmple.IsCanonicalProjMap L g → g = f) ∧
      AlgebraicGeometry.IsOpenImmersion f ∧ Dense (Set.range f.base) := by
  obtain ⟨f, hf, huniq⟩ := AlgebraicGeometry.IsAmple.exists_canonicalProjMap L hL
  exact ⟨f, hf, huniq,
    AlgebraicGeometry.IsAmple.isOpenImmersion_of_isCanonicalProjMap L hL f hf,
    AlgebraicGeometry.IsAmple.dense_range_of_isCanonicalProjMap L hL f hf⟩

end
