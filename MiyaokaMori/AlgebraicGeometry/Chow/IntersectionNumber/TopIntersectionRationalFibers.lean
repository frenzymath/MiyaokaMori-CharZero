import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOver
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopIntersectionDeformationInvariant
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01wc

/-! # Top self-intersections of the fibers of a family over the affine line

Let `f : 𝒴 → A¹_k` be flat and projective, `L` an invertible sheaf on `𝒴`, and `t₁, t₂ ∈ k`. Let `Y_i`
(`i = 1, 2`) be proper schemes over `k` with invertible sheaves `L_i`, and `e_i` isomorphisms from the
fiber of `f` at `λ = t_i` to `Y_i`, compatible with the structure morphisms to `Spec k`, such that the
restriction of `L` to the fiber is isomorphic to `e_i^* L_i`. If `dim Y₁ = dim Y₂`, then
`(L₁^{dim}) = (L₂^{dim})`.

Proof:
1. `A¹_k = Spec k[λ]` (`AffineSpace.isoOfIsAffine` / `SpecIso`): `k[λ]` is Noetherian, so `A¹_k` is
   locally Noetherian; `k[λ]` is a domain, so `A¹_k` is irreducible, hence connected.
2. `point k t` is the image of `sectionAt t`, and the residue field `κ(point k t)` is isomorphic to `k`
   via the stalk map of `sectionAt t`: `σ_t : κ(point k t) ≃+* k` (`k → κ` from the structure
   morphism, `κ → k` induced by `sectionAt t`, the composite is the identity; `κ = k[λ]/(λ − t)`, so it
   is an isomorphism), and `Spec κ → A¹_k → Spec k` equals `Spec(σ_t.symm)`.
3. By 2 and the hypothesis `he_i` (`e_i ≫ (Y_i ↘ Spec k) = fiberι ≫ f ≫ toBase`), the `κ`-structure
   `f.fiberOverSpecResidueField` of the fiber satisfies the compatibility condition of
   `topSelfIntersection_eq_of_iso`: `e_i.hom ≫ (Y_i ↘ Spec k) = (fiber ↘ Spec κ) ≫ Spec(σ.symm)`
   (the fiber square commutes: `fiberι ≫ f = fiberToSpecResidueField ≫ fromSpecResidueField`).
4. The fiber is proper over `κ`: by the equation of 3, `fiber → Spec κ = e_i ≫ (Y_i → Spec k) ≫ Spec(σ)`,
   a composite of an isomorphism and proper morphisms (or: `f` projective ⇒ proper, base change). The
   fiber dimensions agree: `e_i` is a homeomorphism, so `dim fiber_i = dim Y_i`, then use `hdim`.
5. `topSelfIntersection_constant_in_flat_family` (with `t₁ t₂ := point k t_i`): the top
   self-intersections of the restrictions of `L` to the two fibers agree; on each side one application of
   `topSelfIntersection_eq_of_iso` (`L₀ = fiberι^*L`, `hL_i`) converts to the top self-intersection of
   `L_i` on `Y_i`.

Source: the deformation invariance of the top self-intersection in a flat projective family (proof of
Proposition 2.4 of the paper), transported to schemes over `k`.

Implementation notes. The five steps above are formalized as:
* step 1: `affineLineOver.isLocallyNoetherian_spec` (A¹_k → Spec k is locally of finite type and
  Spec k is locally Noetherian) and `affineLineOver.connectedSpace_spec` (A¹_k ≅ Spec k[λ], and
  Spec of a domain is irreducible, hence connected);
* step 2: `affineLineOver.exists_residueField_point_equiv`, via Mathlib's
  `Scheme.SpecToEquivOfField` applied to the section `sectionAt t : Spec k ⟶ A¹_k`;
* step 4: `Scheme.Hom.isProperOver_fiber` (properness is stable under base change) and
  `Scheme.dimension_eq_of_iso` (Krull dimension is a homeomorphism invariant);
* steps 3 and 5: the main theorem `topSelfIntersection_eq_of_rational_fibers`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

-- `Scheme.dimension_eq_of_iso` (Krull dimension is an iso invariant) is provided by the
-- imported `TopSelfIntersectionIsoInvariant`.

/-- The fiber `f.fiber t` of a proper morphism, viewed as a `κ(t)`-scheme via
`f.fiberOverSpecResidueField t`, is proper over `κ(t)`: its structure morphism is
`pullback.snd f (T.fromSpecResidueField t)`, and properness is stable under base change
(Stacks 01W4 / Mathlib `IsProper.isStableUnderBaseChange`). -/
theorem Scheme.Hom.isProperOver_fiber {Y T : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ T)
    [AlgebraicGeometry.IsProper f] (t : T) :
    letI := f.fiberOverSpecResidueField t
    IsProperOver (T.residueField t) (f.fiber t) := by
  let := f.fiberOverSpecResidueField t
  change AlgebraicGeometry.IsProper (pullback.snd f (T.fromSpecResidueField t))
  infer_instance

namespace Scheme.affineLineOver

/-- `A¹_k` is locally Noetherian: `A¹_k ↘ Spec k` is locally of finite type
(`AffineSpace` over a base with finitely many coordinates is locally of finite presentation)
and `Spec k` is locally Noetherian (`k` is a Noetherian ring). Stacks 01T6. -/
theorem isLocallyNoetherian_spec (k : Type u) [Field k] :
    AlgebraicGeometry.IsLocallyNoetherian
      (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))) := by
  -- Elaborate with `𝔸(…)` spelled out: `affineLineOver` is a `def`, and if it is hidden in the
  -- implicit arguments of `↘`, the `AffineSpace` instances are not found at reducible transparency.
  have h : AlgebraicGeometry.IsLocallyNoetherian
      (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) (AlgebraicGeometry.Spec (CommRingCat.of k))) :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) (AlgebraicGeometry.Spec (CommRingCat.of k)) ↘
        AlgebraicGeometry.Spec (CommRingCat.of k))
  exact h

/-- `A¹_k` is connected: `A¹_k ≅ Spec k[λ]` (`AffineSpace.SpecIso`), `k[λ]` is a domain, so its
prime spectrum is irreducible (`PrimeSpectrum.irreducibleSpace`), hence connected; connectedness
is transported along the homeomorphism. -/
theorem connectedSpace_spec (k : Type u) [Field k] :
    ConnectedSpace
      (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))) := by
  let e := AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)
  have : ConnectedSpace
      (AlgebraicGeometry.Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) k))) :=
    inferInstanceAs (ConnectedSpace (PrimeSpectrum (MvPolynomial (ULift.{u} (Fin 1)) k)))
  exact e.hom.homeomorph.connectedSpace_iff.mpr this

/-- The section `λ = t` of `A¹_k → Spec k`, with the `Over` structure `⟨𝟙⟩` on `Spec k` used in
the definition of `point k t`. -/
private def sectionAtSpec (k : Type u) [Field k] (t : k) :
    AlgebraicGeometry.Spec (CommRingCat.of k) ⟶
      AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  letI : (AlgebraicGeometry.Spec (CommRingCat.of k)).Over
      (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨CategoryTheory.CategoryStruct.id _⟩
  AlgebraicGeometry.Scheme.affineLineOver.sectionAt (k := k)
    (AlgebraicGeometry.Spec (CommRingCat.of k)) t

private theorem point_eq_sectionAtSpec (k : Type u) [Field k] (t : k) :
    AlgebraicGeometry.Scheme.affineLineOver.point k t =
      (sectionAtSpec k t).base (IsLocalRing.closedPoint k) := by
  show (sectionAtSpec k t).base (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) =
    (sectionAtSpec k t).base (IsLocalRing.closedPoint k)
  congr 1
  exact Subsingleton.elim (α := PrimeSpectrum k) _ _

private theorem sectionAtSpec_comp_toBase (k : Type u) [Field k] (t : k) :
    sectionAtSpec k t ≫
        AlgebraicGeometry.Scheme.affineLineOver.toBase (AlgebraicGeometry.Spec (CommRingCat.of k)) =
      CategoryTheory.CategoryStruct.id _ :=
  AlgebraicGeometry.AffineSpace.homOfVector_over _ _

/-- The residue field of the `k`-rational point `point k t ∈ A¹_k` is `k`, compatibly with the
structure morphism: there is `σ : κ(point k t) ≃+* k` with
`Spec κ(point k t) → A¹_k → Spec k = Spec (σ.symm)`.

Proof: `point k t` is the image of the closed point of `Spec k` under the section
`s = sectionAt t`. By `Scheme.SpecToEquivOfField`, `s = Spec φ ≫ fromSpecResidueField x` for the
induced `φ : κ(x) → k`. Let `ψ : k → κ(x)` be the ring map with
`Spec ψ = fromSpecResidueField x ≫ toBase` (`Spec` is fully faithful). Then
`Spec (ψ ≫ φ) = Spec φ ≫ Spec ψ = s ≫ toBase = 𝟙`, so `φ ∘ ψ = id`. Hence `φ` is surjective, and
it is injective as a ring map between fields; `σ := φ` is the required isomorphism, with
`σ.symm = ψ`. -/
theorem exists_residueField_point_equiv (k : Type u) [Field k] (t : k) :
    ∃ σ : (AlgebraicGeometry.Scheme.affineLineOver
        (AlgebraicGeometry.Spec (CommRingCat.of k))).residueField
          (AlgebraicGeometry.Scheme.affineLineOver.point k t) ≃+* k,
      (AlgebraicGeometry.Scheme.affineLineOver
          (AlgebraicGeometry.Spec (CommRingCat.of k))).fromSpecResidueField
            (AlgebraicGeometry.Scheme.affineLineOver.point k t) ≫
          AlgebraicGeometry.Scheme.affineLineOver.toBase (AlgebraicGeometry.Spec (CommRingCat.of k)) =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (σ.symm : k →+*
          (AlgebraicGeometry.Scheme.affineLineOver
            (AlgebraicGeometry.Spec (CommRingCat.of k))).residueField
              (AlgebraicGeometry.Scheme.affineLineOver.point k t))) := by
  rw [point_eq_sectionAtSpec]
  set X := AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))
    with hX
  set s := sectionAtSpec k t with hs_def
  set x := s.base (IsLocalRing.closedPoint k) with hx
  let φ : X.residueField x ⟶ CommRingCat.of k :=
    X.descResidueField (AlgebraicGeometry.Scheme.stalkClosedPointTo s)
  have hs : AlgebraicGeometry.Spec.map φ ≫ X.fromSpecResidueField x = s :=
    AlgebraicGeometry.Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X s
  let ψ : CommRingCat.of k ⟶ X.residueField x :=
    AlgebraicGeometry.Spec.preimage (X.fromSpecResidueField x ≫
      AlgebraicGeometry.Scheme.affineLineOver.toBase (AlgebraicGeometry.Spec (CommRingCat.of k)))
  have hψ : AlgebraicGeometry.Spec.map ψ = X.fromSpecResidueField x ≫
      AlgebraicGeometry.Scheme.affineLineOver.toBase (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    AlgebraicGeometry.Spec.map_preimage _
  have hcomp : ψ ≫ φ = CategoryTheory.CategoryStruct.id (CommRingCat.of k) := by
    apply AlgebraicGeometry.Spec.map_injective
    rw [AlgebraicGeometry.Spec.map_comp, AlgebraicGeometry.Spec.map_id, hψ, ← Category.assoc, hs]
    exact sectionAtSpec_comp_toBase k t
  have hφψ : ∀ y : k, φ (ψ y) = y := by
    intro y
    have := congrArg (fun h : CommRingCat.of k ⟶ CommRingCat.of k => h y) hcomp
    simpa using this
  have hinj : Function.Injective φ.hom := φ.hom.injective
  have hsurj : Function.Surjective φ.hom := fun y => ⟨ψ y, hφψ y⟩
  let σ : X.residueField x ≃+* k := RingEquiv.ofBijective φ.hom ⟨hinj, hsurj⟩
  refine ⟨σ, ?_⟩
  have hσ : CommRingCat.ofHom (σ.symm : k →+* X.residueField x) = ψ := by
    ext y
    show σ.symm y = ψ y
    rw [RingEquiv.symm_apply_eq]
    exact (hφψ y).symm
  rw [hσ, hψ]

end Scheme.affineLineOver

end AlgebraicGeometry

theorem topSelfIntersection_eq_of_rational_fibers {k : Type u} [Field k]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)))
    [AlgebraicGeometry.IsProjectiveMorphism f] [AlgebraicGeometry.Flat f]
    (L : Y.Modules) [L.IsLineBundle] (t₁ t₂ : k)
    {Y₁ Y₂ : AlgebraicGeometry.Scheme.{u}}
    [Y₁.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Y₂.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (h₁ : IsProperOver k Y₁) (h₂ : IsProperOver k Y₂)
    (L₁ : Y₁.Modules) [L₁.IsLineBundle] (L₂ : Y₂.Modules) [L₂.IsLineBundle]
    (e₁ : f.fiber (AlgebraicGeometry.Scheme.affineLineOver.point k t₁) ≅ Y₁)
    (he₁ : e₁.hom ≫ (Y₁ ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      f.fiberι (AlgebraicGeometry.Scheme.affineLineOver.point k t₁) ≫ f ≫
        AlgebraicGeometry.Scheme.affineLineOver.toBase (AlgebraicGeometry.Spec (CommRingCat.of k)))
    (hL₁ : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
        (f.fiberι (AlgebraicGeometry.Scheme.affineLineOver.point k t₁))).obj L ≅
      (AlgebraicGeometry.Scheme.Modules.pullback e₁.hom).obj L₁))
    (e₂ : f.fiber (AlgebraicGeometry.Scheme.affineLineOver.point k t₂) ≅ Y₂)
    (he₂ : e₂.hom ≫ (Y₂ ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      f.fiberι (AlgebraicGeometry.Scheme.affineLineOver.point k t₂) ≫ f ≫
        AlgebraicGeometry.Scheme.affineLineOver.toBase (AlgebraicGeometry.Spec (CommRingCat.of k)))
    (hL₂ : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
        (f.fiberι (AlgebraicGeometry.Scheme.affineLineOver.point k t₂))).obj L ≅
      (AlgebraicGeometry.Scheme.Modules.pullback e₂.hom).obj L₂))
    (hdim : Y₁.dimension = Y₂.dimension) :
    AlgebraicGeometry.topSelfIntersection Y₁ h₁ L₁ =
      AlgebraicGeometry.topSelfIntersection Y₂ h₂ L₂ := by
  -- Step 1: the base A¹_k is locally Noetherian and connected.
  have := AlgebraicGeometry.Scheme.affineLineOver.isLocallyNoetherian_spec k
  have := AlgebraicGeometry.Scheme.affineLineOver.connectedSpace_spec k
  have : AlgebraicGeometry.IsProper f := AlgebraicGeometry.IsProjectiveMorphism.isProper f
  -- Step 2: κ(point k tᵢ) ≃+* k.
  obtain ⟨σ₁, hσ₁⟩ := AlgebraicGeometry.Scheme.affineLineOver.exists_residueField_point_equiv k t₁
  obtain ⟨σ₂, hσ₂⟩ := AlgebraicGeometry.Scheme.affineLineOver.exists_residueField_point_equiv k t₂
  -- Step 4: the fibers as κ-schemes are proper, and have the dimensions of Y₁, Y₂.
  let := f.fiberOverSpecResidueField (AlgebraicGeometry.Scheme.affineLineOver.point k t₁)
  let := f.fiberOverSpecResidueField (AlgebraicGeometry.Scheme.affineLineOver.point k t₂)
  have hf₁ := f.isProperOver_fiber (AlgebraicGeometry.Scheme.affineLineOver.point k t₁)
  have hf₂ := f.isProperOver_fiber (AlgebraicGeometry.Scheme.affineLineOver.point k t₂)
  have hdim' : (f.fiber (AlgebraicGeometry.Scheme.affineLineOver.point k t₁)).dimension =
      (f.fiber (AlgebraicGeometry.Scheme.affineLineOver.point k t₂)).dimension := by
    rw [AlgebraicGeometry.Scheme.dimension_eq_of_iso e₁,
      AlgebraicGeometry.Scheme.dimension_eq_of_iso e₂, hdim]
  -- Step 5: deformation invariance between the two fibers.
  have hmid := topSelfIntersection_constant_in_flat_family f L
    (AlgebraicGeometry.Scheme.affineLineOver.point k t₁)
    (AlgebraicGeometry.Scheme.affineLineOver.point k t₂) hf₁ hf₂ hdim'
  -- Step 3: transport each fiber to Yᵢ along eᵢ.
  have hcompat₁ : e₁.hom ≫ (Y₁ ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (f.fiber (AlgebraicGeometry.Scheme.affineLineOver.point k t₁) ↘
          AlgebraicGeometry.Spec (CommRingCat.of ((AlgebraicGeometry.Scheme.affineLineOver
            (AlgebraicGeometry.Spec (CommRingCat.of k))).residueField
              (AlgebraicGeometry.Scheme.affineLineOver.point k t₁)))) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (σ₁.symm : k →+* _)) := by
    rw [he₁, ← hσ₁]
    exact AlgebraicGeometry.Scheme.Hom.fiber_fac_assoc f _ _
  have hcompat₂ : e₂.hom ≫ (Y₂ ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (f.fiber (AlgebraicGeometry.Scheme.affineLineOver.point k t₂) ↘
          AlgebraicGeometry.Spec (CommRingCat.of ((AlgebraicGeometry.Scheme.affineLineOver
            (AlgebraicGeometry.Spec (CommRingCat.of k))).residueField
              (AlgebraicGeometry.Scheme.affineLineOver.point k t₂)))) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (σ₂.symm : k →+* _)) := by
    rw [he₂, ← hσ₂]
    exact AlgebraicGeometry.Scheme.Hom.fiber_fac_assoc f _ _
  have h1 := topSelfIntersection_eq_of_iso σ₁ e₁ hcompat₁ hf₁ h₁ L₁ _ hL₁
  have h2 := topSelfIntersection_eq_of_iso σ₂ e₂ hcompat₂ hf₂ h₂ L₂ _ hL₂
  rw [← h1, ← h2]
  exact hmid

end
