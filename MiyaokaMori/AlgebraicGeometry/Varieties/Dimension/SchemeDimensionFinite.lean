import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.DimensionOpenCoverSup
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0a213

/-! # Finiteness of the dimension of schemes over a field

Finiteness of the dimension for schemes (not packaged as a `Variety k`) and the conversion to
`Scheme.dimension`:
(1) a finitely generated commutative `k`-algebra `A` has finite Krull dimension, `ringKrullDim A ≠ ⊤`;
(2) if `X` is a `k`-scheme whose structure morphism is locally of finite type and `U` is an affine
    open, then `topologicalKrullDim U ≠ ⊤`;
(3) if moreover `X` is irreducible, then `topologicalKrullDim X ≠ ⊤`;
(4) if moreover `X` is quasi-compact (`CompactSpace X`), then `topologicalKrullDim X ≠ ⊤`;
(5) consequently `IsProperOver k X` implies `topologicalKrullDim X ≠ ⊤`;
(6) conversion: if `X` is nonempty then `topologicalKrullDim X ≠ ⊥`; if `X` is nonempty of finite
    dimension then `topologicalKrullDim X = (X.dimension : WithBot ℕ∞)`, and in particular
    `X.dimension = 0` gives `topologicalKrullDim X = 0`;
(7) if `X` is irreducible with `topologicalKrullDim X = 0`, its underlying space is a single point
    (`Subsingleton X`), hence `IsAffine X` and `CompactSpace X`.

Proof sketch:
1. `A` finitely generated gives a surjective `k`-algebra map `k[x_1,…,x_n] → A`
   (`Algebra.FiniteType.iff_quotient_mvPolynomial''`); `ringKrullDim_le_of_surjective` gives
   `ringKrullDim A ≤ ringKrullDim k[x_1..x_n] = n < ⊤`
   (`MvPolynomial.ringKrullDim_of_isNoetherianRing`, `ringKrullDim_eq_zero_of_field`).
2. `U ≅ Spec Γ(X,U)` (`IsAffineOpen.isoSpec`, a homeomorphism), and
   `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` converts to `ringKrullDim Γ(X,U)`; the
   structure morphism being locally of finite type makes `Γ(X,U)` a finitely generated `k`-algebra
   (`Scheme.Hom.finiteType_appLE`); apply (1).
3. `X` irreducible: any nonempty affine open `U` has `topologicalKrullDim U = topologicalKrullDim X`
   (Stacks 0A21 (3)); apply (2). If `X` is empty the dimension is `⊥ ≠ ⊤`.
4. `X` quasi-compact: take a finite subcover of the affine open cover (`iSup_affineOpens_eq_top`);
   `topologicalKrullDim X = ⨆ i, topologicalKrullDim U_i` over a finite index, each term `≠ ⊤` by (2).
5. `IsProperOver k X = IsProper (X ↘ Spec k)` gives `LocallyOfFiniteType` and `UniversallyClosed`
   (hence `QuasiCompact`); `Spec k` is compact so `CompactSpace X`
   (`QuasiCompact.compactSpace_of_compactSpace`); apply (4).
6. `topologicalKrullDim` is the Krull dimension of `IrreducibleCloseds X`; `X` nonempty makes this
   order nonempty (schemes are sober, `irreducibleSetEquivPoints`), so it is `≠ ⊥`
   (`Order.krullDim_ne_bot_iff`); then `Scheme.dimension_spec`.
7. The Krull dimension of the specialization order equals the topological Krull dimension
   (`irreducibleSetEquivPoints` is an order isomorphism); dimension `0` means there is no `x < y`;
   `X` irreducible has a generic point `ξ` with `ξ ⤳ x`, i.e. `ξ ≤ x`, so `x = ξ`. A one-point
   scheme is affine: an affine open neighbourhood of the point is the whole space.

Sources: Stacks 00OW (Noether normalization), Stacks 0A21 (3).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## (1) Finitely generated algebras over a field have finite Krull dimension -/

/-- A finitely generated commutative `k`-algebra `A` has finite Krull dimension. -/
theorem ringKrullDim_ne_top_of_finiteType (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] : ringKrullDim A ≠ ⊤ := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType k A›
  have hle : ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin n) k) :=
    ringKrullDim_le_of_surjective f.toRingHom hf
  have hpoly : ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field k]
    simp
  have hntop : ((n : ℕ) : WithBot ℕ∞) ≠ ⊤ := by
    intro h
    rw [show ((n : ℕ) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) by norm_cast] at h
    exact absurd (WithBot.coe_injective h) (ENat.natCast_ne_top n)
  rw [hpoly] at hle
  intro htop
  rw [htop] at hle
  exact hntop (top_le_iff.mp hle)

/-! ## (2) Affine opens have finite dimension -/

/-- When the structure morphism is locally of finite type, the section ring of an affine open is a
finitely generated `k`-algebra. -/
private theorem finiteType_sections {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (U : X.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) :
    (((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appLE ⊤ U le_top).hom).FiniteType := by
  have h1 : ((X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appLE ⊤ U le_top).hom.FiniteType :=
    (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).finiteType_appLE
      (AlgebraicGeometry.isAffineOpen_top _) hU _
  have h2 : ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective
  exact h1.comp h2

/-- An affine open of a scheme locally of finite type over a field `k` has finite dimension. -/
theorem AlgebraicGeometry.topologicalKrullDim_affineOpen_ne_top {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (U : X.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) :
    topologicalKrullDim U ≠ ⊤ := by
  let φ : k →+* Γ(X, U) :=
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appLE ⊤ U le_top).hom
  have hφ : φ.FiniteType := finiteType_sections (k := k) X U hU
  let _ : Algebra k Γ(X, U) := φ.toAlgebra
  have : Algebra.FiniteType k Γ(X, U) := hφ
  rw [IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph]
  erw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)]
  exact ringKrullDim_ne_top_of_finiteType k Γ(X, U)

/-! ## (3) The irreducible case -/

/-- An irreducible scheme locally of finite type over a field `k` has finite dimension. -/
theorem AlgebraicGeometry.topologicalKrullDim_ne_top_of_irreducibleSpace {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [IrreducibleSpace X] : topologicalKrullDim X ≠ ⊤ := by
  obtain ⟨x⟩ := (inferInstance : IrreducibleSpace X).toNonempty
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [← AlgebraicGeometry.topologicalKrullDim_opens_eq_of_irreducible (k := k) X U ⟨x, hxU⟩]
  exact AlgebraicGeometry.topologicalKrullDim_affineOpen_ne_top (k := k) X U hU

/-! ## (4) The quasi-compact case -/

private theorem iSup_ne_top_of_finite {ι : Type*} [Finite ι] (g : ι → WithBot ℕ∞)
    (hg : ∀ i, g i ≠ ⊤) : (⨆ i, g i) ≠ ⊤ := by
  cases nonempty_fintype ι
  have hsup : (⨆ i, g i) = Finset.univ.sup g := by
    rw [Finset.sup_eq_iSup]
    simp
  rw [← lt_top_iff_ne_top, hsup, Finset.sup_lt_iff (bot_lt_top)]
  exact fun i _ => lt_top_iff_ne_top.mpr (hg i)

/-- A quasi-compact scheme locally of finite type over a field `k` has finite dimension. -/
theorem AlgebraicGeometry.topologicalKrullDim_ne_top_of_compactSpace {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [CompactSpace X] : topologicalKrullDim X ≠ ⊤ := by
  -- the affine opens cover `X`; take a finite subcover
  have hcover : (Set.univ : Set X) ⊆ ⋃ V : X.affineOpens, (V.1 : Set X) := by
    intro x _
    have htop := AlgebraicGeometry.iSup_affineOpens_eq_top X
    have hx : x ∈ (⊤ : X.Opens) := trivial
    rw [← htop] at hx
    simpa using hx
  obtain ⟨s, hs⟩ :=
    isCompact_univ.elim_finite_subcover (fun V : X.affineOpens => (V.1 : Set X))
      (fun V => V.1.2) hcover
  have hsup : (⨆ i : {V : X.affineOpens // V ∈ s}, (i.1.1 : X.Opens)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx := hs (Set.mem_univ x)
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨V, hVs, hxV⟩ := hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hVs⟩, hxV⟩
  have : Finite (X.openCoverOfIsOpenCover
      (fun i : {V : X.affineOpens // V ∈ s} => (i.1.1 : X.Opens)) hsup).I₀ :=
    inferInstanceAs (Finite {V : X.affineOpens // V ∈ s})
  rw [topologicalKrullDim_eq_iSup_openCover
    (X.openCoverOfIsOpenCover (fun i : {V : X.affineOpens // V ∈ s} => (i.1.1 : X.Opens)) hsup)]
  exact iSup_ne_top_of_finite _ fun i =>
    AlgebraicGeometry.topologicalKrullDim_affineOpen_ne_top (k := k) X i.1.1 i.1.2

/-! ## (5) The proper case -/

/-- A scheme proper over `k` has finite dimension. -/
theorem AlgebraicGeometry.topologicalKrullDim_ne_top_of_isProperOver {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) : topologicalKrullDim X ≠ ⊤ := by
  have hprop : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hX
  have hft : AlgebraicGeometry.LocallyOfFiniteType
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hprop.toLocallyOfFiniteType
  have huc : AlgebraicGeometry.UniversallyClosed
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hprop.toUniversallyClosed
  have hqc : AlgebraicGeometry.QuasiCompact
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := inferInstance
  have : CompactSpace X :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  exact AlgebraicGeometry.topologicalKrullDim_ne_top_of_compactSpace (k := k) X

/-! ## (6) Conversion to `Scheme.dimension` -/

/-- The topological Krull dimension of a nonempty scheme is not `⊥`. -/
theorem AlgebraicGeometry.topologicalKrullDim_ne_bot (X : AlgebraicGeometry.Scheme.{u})
    [Nonempty X] : topologicalKrullDim X ≠ ⊥ := by
  have : Nonempty (IrreducibleCloseds X) :=
    ⟨(@irreducibleSetEquivPoints X _ _ _).symm (Classical.arbitrary X)⟩
  exact Order.krullDim_ne_bot_iff.mpr this

/-- For a nonempty scheme of finite dimension, `X.dimension` records `topologicalKrullDim X`
faithfully. -/
theorem AlgebraicGeometry.Scheme.topologicalKrullDim_eq_dimension
    (X : AlgebraicGeometry.Scheme.{u}) [Nonempty X] (h : topologicalKrullDim X ≠ ⊤) :
    topologicalKrullDim X = (X.dimension : WithBot ℕ∞) :=
  X.dimension_spec (AlgebraicGeometry.topologicalKrullDim_ne_bot X) h

/-- For a nonempty scheme of finite dimension, `X.dimension = 0` implies that the topological Krull
dimension is `0`. -/
theorem AlgebraicGeometry.Scheme.topologicalKrullDim_eq_zero_of_dimension_eq_zero
    (X : AlgebraicGeometry.Scheme.{u}) [Nonempty X] (h : topologicalKrullDim X ≠ ⊤)
    (hd : X.dimension = 0) : topologicalKrullDim X = 0 := by
  rw [AlgebraicGeometry.Scheme.topologicalKrullDim_eq_dimension X h, hd]
  simp

/-! ## (7) A zero-dimensional irreducible scheme is a one-point affine scheme -/

/-- The Krull dimension of the underlying space of a scheme (with the specialization order) is
the topological Krull dimension. -/
theorem AlgebraicGeometry.krullDim_eq_topologicalKrullDim (X : AlgebraicGeometry.Scheme.{u}) :
    Order.krullDim X = topologicalKrullDim X :=
  (Order.krullDim_eq_of_orderIso
    (@irreducibleSetEquivPoints X _ _ _ : IrreducibleCloseds X ≃o X)).symm

/-- An irreducible zero-dimensional scheme has a single point. -/
theorem AlgebraicGeometry.subsingleton_of_topologicalKrullDim_eq_zero
    (X : AlgebraicGeometry.Scheme.{u}) [IrreducibleSpace X]
    (h : topologicalKrullDim X = 0) : Subsingleton X := by
  have hk : Order.krullDim (X : Type u) = 0 := by
    rw [AlgebraicGeometry.krullDim_eq_topologicalKrullDim X, h]
  have hmax : ∀ x : X, IsMax x := Order.krullDim_nonpos_iff_forall_isMax.mp hk.le
  have hgen : ∀ x : X, x = genericPoint X := by
    intro x
    -- `x ≤ genericPoint X` is `genericPoint X ⤳ x` (specialization preorder: `a ≤ b ↔ b ⤳ a`)
    have hle : x ≤ genericPoint X := genericPoint_specializes x
    have hge : genericPoint X ≤ x := hmax x hle
    exact (Specializes.antisymm (hge : x ⤳ genericPoint X)
      (hle : genericPoint X ⤳ x)).eq
  exact ⟨fun a b => (hgen a).trans (hgen b).symm⟩

/-- A one-point scheme is affine: an affine open neighbourhood of the point is the whole space. -/
theorem AlgebraicGeometry.isAffine_of_subsingleton (X : AlgebraicGeometry.Scheme.{u})
    [Subsingleton X] [Nonempty X] : AlgebraicGeometry.IsAffine X := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hUtop : U = ⊤ := by
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun y => ?_)
    rwa [Subsingleton.elim y x]
  have htop : AlgebraicGeometry.IsAffineOpen (⊤ : X.Opens) := hUtop ▸ hU
  have : AlgebraicGeometry.IsAffine (⊤ : X.Opens).toScheme := htop
  exact AlgebraicGeometry.IsAffine.of_isIso (AlgebraicGeometry.Scheme.topIso X).inv

end
