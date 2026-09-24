import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.SeedBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceRestrictToZeroSection
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetConeCoordinate
import MiyaokaMori.AlgebraicGeometry.Morphisms.FiberPolynomialExtensionDegreeP1Extension
import MiyaokaMori.AlgebraicGeometry.Morphisms.FiberRestrictComp
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ThickeningSectionsTruncated
import MiyaokaMori.AlgebraicGeometry.Morphisms.IsProjectiveOverIsProper

/-! # Extension of a fibre-polynomial map to the whole `P¹` and its degree

Statement: let a tuple of homogeneous coordinate sections on the total space have `ξ`-degree bounded by
`r₀`, with restrictions to the zero section and to the jet neighbourhood equal to the seed coordinates
and to the given jet, respectively. If it induces a nonconstant morphism on an open subset of the ruled
fibre over a closed point `y`, then this morphism extends to the whole `P¹`; the extension has
`O_X(1)`-degree in `[1, r₀]` and agrees with the original morphism on a nonempty open subset.

Proof (the top level is assembled from the following pieces):
1. `totalSpaceOpenFiberToRuledFiber` (module `FiberPolynomialExtensionDegreeP1Extension`): the fibre
   `U_y` of `U ⊆ Tot(L) → C̃` over `y` maps by an open immersion `θ` into the ruled fibre `W_y`,
   compatibly with the fibre embeddings; `U_y ≠ ∅` because `U` contains the zero section.
2. `fiber_restriction_extends_to_p1`: `e : W_y ≅ P¹`, `g : P¹ → P^N`, `m ≤ r₀` with `deg g^*O(1) = m`,
   `1 ≤ m` if `g` is nonconstant, and `(U_y → U → X → P^N) = θ ≫ e.hom ≫ g`. (In the paper: homogenize
   the fibre polynomials and remove the common factor; Theorem 4.2 / Lemma 4.1.)
3. `g` is nonconstant: otherwise `θ ≫ e.hom ≫ g = (U_y → X) ≫ emb` would be constant, and `emb` is
   injective on points, so `fiberRestrict Φ₀ q y` would be constant, contradicting `hnonconstant`.
4. `g` factors through `X`: its image agrees with `Φ₀ ≫ emb` on the dense open `θ ≫ e.hom` of the
   irreducible `P¹` (`range_subset_of_agree_on_dense_range`), and a morphism from a reduced scheme whose
   image lies in a closed subscheme lifts through the closed immersion
   (`exists_lift_isClosedImmersion_of_range_subset`, Stacks Project, Tag 01R8 / Hartshorne II Ex. 3.11(d)):
   `Φ' : P¹ → X`, `Φ' ≫ emb = g`. Put `Φy := e.hom ≫ Φ'`, `O := θ.opensRange`,
   `j := θ.isoOpensRange.inv ≫ q.fiberι y`; the two compatibilities follow from steps 1 and 2 after
   cancelling the monomorphism `emb`.
5. Degree: `(e.inv ≫ Φy)^*O_X(1) = Φ'^*O_X(1)` has the degree of `LineBundle.ofModules (g^*O(1))`
   (`LineBundle.degree_pullback_OX_one`, via `Modules.pullbackComp`), i.e. `m ∈ [1, r₀]`.

Reference: Theorem 4.2 / Lemma 4.1 of the paper (nonconstancy
on a general fibre and the degree bound `r₀`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Precomposition preserves constancy. -/
theorem IsConstantMorphism.comp_left {A B Z : AlgebraicGeometry.Scheme.{u}}
    (a : A ⟶ B) {b : B ⟶ Z} (h : IsConstantMorphism b) : IsConstantMorphism (a ≫ b) := by
  obtain ⟨z, hz⟩ := h
  exact ⟨z, fun x ↦ by simp [hz]⟩

/-- If `a ≫ b` is constant and `b` is injective on points, then `a` is constant
(`B` nonempty so that the empty-source case has a value). -/
theorem IsConstantMorphism.of_comp_injective {A B Z : AlgebraicGeometry.Scheme.{u}}
    [Nonempty B] (a : A ⟶ B) (b : B ⟶ Z) (hb : Function.Injective b.base)
    (h : IsConstantMorphism (a ≫ b)) : IsConstantMorphism a := by
  obtain ⟨z, hz⟩ := h
  by_cases hA : Nonempty A
  · obtain ⟨x₀⟩ := hA
    refine ⟨a.base x₀, fun x ↦ hb ?_⟩
    have h1 := hz x
    have h2 := hz x₀
    rw [AlgebraicGeometry.Scheme.Hom.comp_apply] at h1 h2
    rw [h1, h2]
  · exact ⟨Classical.arbitrary _, fun x ↦ (hA ⟨x⟩).elim⟩

/-- If `g : S ⟶ T` agrees with a morphism into `Z` on a dense subset (the image of `a`), and
`ι : Z ⟶ T` has closed image, then the whole image of `g` lies in the image of `ι`. -/
theorem range_subset_of_agree_on_dense_range {A S Z T : AlgebraicGeometry.Scheme.{u}}
    (a : A ⟶ S) (g : S ⟶ T) (ι : Z ⟶ T) (h : A ⟶ Z) (hd : Dense (Set.range a.base))
    (hι : IsClosed (Set.range ι.base)) (hcomm : a ≫ g = h ≫ ι) :
    Set.range g.base ⊆ Set.range ι.base := by
  have h1 : g.base '' Set.range a.base ⊆ Set.range ι.base := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨h.base x, ?_⟩
    have hx := congrArg (fun φ : A ⟶ T ↦ φ.base x) hcomm
    simpa [AlgebraicGeometry.Scheme.Hom.comp_apply] using hx.symm
  have h2 : Set.range g.base ⊆ closure (g.base '' Set.range a.base) := by
    rw [← Set.image_univ, ← hd.closure_eq]
    exact image_closure_subset_closure_image g.base.hom.continuous
  exact h2.trans (hι.closure_subset_iff.mpr h1)

/-- A quasi-compact morphism from a reduced scheme whose image lies in a closed subscheme factors
through the closed immersion (Stacks 01R8, Hartshorne II Ex. 3.11(d): the scheme-theoretic image of
a morphism from a reduced scheme is the reduced induced structure on the closure of its image).
Proof: the kernel ideal sheaf of `g` is radical (its sections are kernels of ring maps into reduced
rings), so `g.ker = vanishingIdeal (closure (range g))`; `ι.ker ≤ vanishingIdeal (range ι)` and
`closure (range g) ⊆ range ι` give `ι.ker ≤ g.ker`, and `IsClosedImmersion.lift` does the rest. -/
theorem exists_lift_isClosedImmersion_of_range_subset {S Z T : AlgebraicGeometry.Scheme.{u}}
    (g : S ⟶ T) (ι : Z ⟶ T) [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsReduced S]
    [AlgebraicGeometry.QuasiCompact g] (h : Set.range g.base ⊆ Set.range ι.base) :
    ∃ Φ : S ⟶ Z, Φ ≫ ι = g := by
  have hrad : g.ker.radical = g.ker := by
    ext U : 2
    rw [AlgebraicGeometry.Scheme.IdealSheafData.radical_ideal, AlgebraicGeometry.Scheme.Hom.ker_apply]
    apply Ideal.radical_eq_iff.mpr
    intro x hx
    rw [Ideal.mem_radical_iff] at hx
    obtain ⟨n, hn⟩ := hx
    rw [RingHom.mem_ker, map_pow] at hn
    exact RingHom.mem_ker.mpr (IsNilpotent.eq_zero ⟨n, hn⟩)
  have hsupp : g.ker.support ≤ ι.ker.support := by
    change (g.ker.support : Set T) ⊆ ι.ker.support
    rw [AlgebraicGeometry.Scheme.Hom.support_ker]
    refine (closure_mono h).trans ?_
    rw [ι.isClosedEmbedding.isClosed_range.closure_eq]
    exact ι.range_subset_ker_support
  have hle : ι.ker ≤ g.ker := by
    calc ι.ker ≤ ι.ker.radical := AlgebraicGeometry.Scheme.IdealSheafData.le_radical _
      _ = AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ι.ker.support :=
          AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_support.symm
      _ ≤ AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal g.ker.support :=
          AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_antimono hsupp
      _ = g.ker.radical := AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_support
      _ = g.ker := hrad
  exact ⟨AlgebraicGeometry.IsClosedImmersion.lift ι g hle,
    AlgebraicGeometry.IsClosedImmersion.lift_fac ι g hle⟩

/-- Degree bookkeeping: `Φ^*O_X(1)` has the same degree as the pullback of `O_{P^N}(1)` along
`Φ ≫ emb` (`O_X(1) = emb^*O(1)` by definition, and `Modules.pullbackComp`). -/
theorem LineBundle.degree_pullback_OX_one {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {C : SmoothProjectiveCurve k} (Φ : C.toScheme ⟶ X.toScheme) :
    (LineBundle.pullback (X := C.toVariety) Φ (X.OX 1)).degree =
      (LineBundle.ofModules (X := C.toVariety)
        ((AlgebraicGeometry.Scheme.Modules.pullback (Φ ≫ X.embedding.emb)).obj
          (projectiveSpaceTwist k X.embDim 1))).degree :=
  LineBundle.degree_congr
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp Φ X.embedding.emb).app
      (projectiveSpaceTwist k X.embDim 1))

/-- A smooth projective curve is a Noetherian scheme (it is proper over a field;
`AlgebraicGeometry.Intersection.properFieldScheme_isNoetherian`). -/
theorem SmoothProjectiveCurve.isNoetherian {k : Type u} [Field k] (C : SmoothProjectiveCurve k) :
    AlgebraicGeometry.IsNoetherian C.toScheme :=
  haveI : AlgebraicGeometry.IsProper
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    IsProjectiveOver.isProper C.projective
  AlgebraicGeometry.Intersection.properFieldScheme_isNoetherian
    (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

/-- **Extension of the fibre map to `P¹` with a degree bound.** If the tuple `P` of coordinate sections
of `ξ`-degree `≤ r₀` induces (via `Φ₀`) a nonconstant morphism on the fibre of `U` over the closed point
`y`, then there are an isomorphism `e` of the ruled fibre over `y` with `P¹`, a morphism `Φy` from that
fibre to `X` agreeing with `Φ₀` on a nonempty open `O`, and the degree of `(e.inv ≫ Φy)^*O_X(1)` lies in
`[1, r₀]`. -/
theorem fiber_polynomial_extension_degree {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ r₀ : ℕ} (jet : BasedJet f ρ L κ)
    (P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (seedBundlePullback f ρ).toModules).val.obj
          (Opposite.op ⊤) : Type u))
    (hP : ∀ ℓ, xiDegree L (seedBundlePullback f ρ) (P ℓ) ≤ (r₀ : WithBot ℕ))
    (hjet : ∀ ℓ, BasedJet.coneCoordinate jet ℓ =
      restrictToThickening L (seedBundlePullback f ρ) κ (P ℓ))
    (hzero : ∀ ℓ, AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules (P ℓ) =
      seedCoordPullback f ρ (D.coord ℓ))
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens)
    (Φ₀ : U.toScheme ⟶ X.toScheme) (hΦ : IsTupleProjectivization _ P U Φ₀)
    (hU0 : Set.range (AlgebraicGeometry.Scheme.zeroSection L.toModules).base ⊆
      (U : Set (AlgebraicGeometry.Scheme.totalSpace L.toModules).left))
    (y : ρ.source.toScheme) (hy : IsClosed ({y} : Set ρ.source.toScheme))
    (hnonconstant : ¬ IsConstantMorphism
      (fiberRestrict Φ₀ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom) y)) :
    ∃ (e : ((ruledSurface.π L).fiber y) ≅
          (ProjectiveLine.asSmoothProjectiveCurve k).toScheme)
        (Φy : ((ruledSurface.π L).fiber y) ⟶ X.toScheme)
        (O : ((ruledSurface.π L).fiber y).Opens) (_ : O ≠ ⊥)
        (j : O.toScheme ⟶ U.toScheme),
      j ≫ U.ι ≫ ruledSurface.totalSpaceIncl L =
          O.ι ≫ (ruledSurface.π L).fiberι y ∧
        j ≫ Φ₀ = O.ι ≫ Φy ∧
        1 ≤ (LineBundle.pullback
          (X := (ProjectiveLine.asSmoothProjectiveCurve k).toVariety)
          (e.inv ≫ Φy) (X.OX 1)).degree ∧
        (LineBundle.pullback
          (X := (ProjectiveLine.asSmoothProjectiveCurve k).toVariety)
          (e.inv ≫ Φy) (X.OX 1)).degree ≤ (r₀ : ℤ) := by
  -- jet, hjet, hzero are not needed for this lemma (the seed data enters only through hΦ and hU0)
  clear hjet hzero jet
  obtain ⟨e, g, m, hm, hnc, hdeg, heq⟩ :=
    fiber_restriction_extends_to_p1 L (seedBundlePullback f ρ) P hP U Φ₀ hΦ hU0 y hy
  set q := U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom with hq
  set θ := totalSpaceOpenFiberToRuledFiber L U y with hθ
  have hθo : AlgebraicGeometry.IsOpenImmersion θ :=
    totalSpaceOpenFiberToRuledFiber_isOpenImmersion L U y
  have hne : Nonempty (q.fiber y) := totalSpaceOpenFiber_nonempty L U hU0 y
  have hXint : AlgebraicGeometry.IsIntegral X.toScheme := X.toVariety.integral
  have hP1int : AlgebraicGeometry.IsIntegral (ProjectiveLine.asSmoothProjectiveCurve k).toScheme :=
    SmoothProjectiveCurve.isIntegral _
  have hP1noeth :
      AlgebraicGeometry.IsNoetherian (ProjectiveLine.asSmoothProjectiveCurve k).toScheme :=
    SmoothProjectiveCurve.isNoetherian _
  -- g is nonconstant, since it agrees with Φ₀ ≫ emb on the (nonempty) fiber of U
  have hgnc : ¬ IsConstantMorphism g := by
    intro hg
    apply hnonconstant
    have h1 : IsConstantMorphism ((q.fiberι y ≫ Φ₀) ≫ X.embedding.emb) := by
      rw [Category.assoc, heq]
      exact IsConstantMorphism.comp_left _ (IsConstantMorphism.comp_left _ hg)
    exact IsConstantMorphism.of_comp_injective (q.fiberι y ≫ Φ₀) X.embedding.emb
      X.embedding.emb.isClosedEmbedding.injective h1
  -- g factors through X
  have hdense : Dense (Set.range (θ ≫ e.hom).base) := by
    apply IsOpen.dense
    · exact (θ ≫ e.hom).isOpenEmbedding.isOpen_range
    · obtain ⟨x⟩ := hne
      exact ⟨_, x, rfl⟩
  have hrange : Set.range g.base ⊆ Set.range X.embedding.emb.base :=
    range_subset_of_agree_on_dense_range (θ ≫ e.hom) g X.embedding.emb (q.fiberι y ≫ Φ₀) hdense
      X.embedding.emb.isClosedEmbedding.isClosed_range (by rw [Category.assoc, ← heq, Category.assoc])
  obtain ⟨Φ', hΦ'⟩ := exists_lift_isClosedImmersion_of_range_subset g X.embedding.emb hrange
  have hOne : θ.opensRange ≠ ⊥ := by
    rw [TopologicalSpace.Opens.ne_bot_iff_nonempty]
    obtain ⟨x⟩ := hne
    exact ⟨θ.base x, x, rfl⟩
  have hcomp : θ ≫ (ruledSurface.π L).fiberι y = q.fiberι y ≫ U.ι ≫ ruledSurface.totalSpaceIncl L :=
    totalSpaceOpenFiberToRuledFiber_comp_fiberι L U y
  refine ⟨e, e.hom ≫ Φ', θ.opensRange, hOne, θ.isoOpensRange.inv ≫ q.fiberι y, ?_, ?_, ?_, ?_⟩
  · rw [← AlgebraicGeometry.Scheme.Hom.isoOpensRange_inv_comp θ]
    simp only [Category.assoc]
    rw [hcomp]
  · have : Mono X.embedding.emb := inferInstance
    rw [← cancel_mono X.embedding.emb, ← AlgebraicGeometry.Scheme.Hom.isoOpensRange_inv_comp θ]
    simp only [Category.assoc, hΦ']
    rw [heq]
  · rw [Iso.inv_hom_id_assoc, LineBundle.degree_pullback_OX_one, hΦ', hdeg]
    exact_mod_cast hnc hgnc
  · rw [Iso.inv_hom_id_assoc, LineBundle.degree_pullback_OX_one, hΦ', hdeg]
    exact_mod_cast hm

end
