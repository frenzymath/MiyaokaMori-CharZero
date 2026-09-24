import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks00p1
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.LocalDimensionOpenEmbedding
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.PointClosureDimensionTrdeg

/-! # Local dimension of a fiber at a point

Stacks Project, Tag 02FX: for `f : X → S` locally of finite type, `x ∈ X` and `s = f(x)`, the local
dimension of the fiber `X_s` at `x` is `dim_x(X_s) = dim O_{X_s,x} + trdeg_{κ(s)} κ(x)`; for
`S = Spec k` this is Stacks 0A21 (10). The algebraic core is Stacks 00P1.

## Route (Stacks 02FX)

Write `s = f x`, `κ(s) = S.residueField s`, `X_s = f.fiber s = X ×_S Spec κ(s)`,
`π = f.fiberToSpecResidueField s : X_s → Spec κ(s)` (locally of finite type: base change of `f`,
Mathlib instance for `pullback.snd`), `x' = f.asFiber x`.

1. **Base field case** (`iInf_topologicalKrullDim_opens_eq_stalk_add_trdeg_pointBaseMap`, Stacks
   0A21(10)): for `π : Z → Spec k` locally of finite type over a field and `z ∈ Z`, with `κ(z)` a
   `k`-algebra via the canonical map `pointBaseMap π z = Spec.preimage (Spec κ(z) → Z → Spec k)`
   (`AlgebraicGeometry.Intersection.pointBaseMap`), `⨅_{U ∋ z} dim U = dim 𝒪_{Z,z} + trdeg_k κ(z)`.
   Proof: take an affine open `V ∋ z`, `A = Γ(Z, V)`, a finite type `k`-algebra
   (`HasRingHomProperty.Spec_iff` for `Spec A → Spec k`), `y = hV.primeIdealOf z`.
   The untruncated local dimension is invariant under the open embedding `Spec A → Z`
   (`Topology.IsOpenEmbedding.iInf_topologicalKrullDim_opens_eq`); `𝒪_{Z,z} = A_y`
   (`IsAffineOpen.isLocalization_stalk`, dimensions compared through
   `IsLocalization.AtPrime.ringKrullDim_eq_height`); `κ(z) ≅ κ(y)` as `k`-algebras
   (`residueFieldMap_trdeg_eq_of_eq` for the open immersion `Spec A → Z` over `k`, then
   `AlgebraicGeometry.Intersection.specResidueField_trdeg_eq`). Then Stacks 00P1 (`stacks_00P1`):
   `dim_y Spec A = dim A_y + trdeg_k κ(y)`.
2. **Transfer to the fibre.** Apply step 1 to `π` at the point `g q`, where
   `g = f.asFiberHom x : Spec κ(x) → X_s` and `q` is the unique point; `g q = x'` because
   `g ≫ fiberι = X.fromSpecResidueField x` and `fiberι` is injective.
3. **Residue fields.** `δ = descResidueField (stalkClosedPointTo g) : κ_{X_s}(x') → κ_X(x)` satisfies
   `pointBaseMap π x' ≫ δ = f.residueFieldMap x` (apply `Spec.map`, which is injective, and use
   `g ≫ π = Spec.map (f.residueFieldMap x)`). It is surjective because `g ≫ fiberι` is a
   preimmersion (`surjective_stalkClosedPointTo_of_comp`), hence a `κ(s)`-algebra isomorphism, so the
   two transcendence degrees agree (`AlgEquiv.trdeg_eq`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- **Stacks 0A21(10) / 00P1 in scheme form, over an honest base field.** For `π : Z → Spec k`
locally of finite type and `z ∈ Z`, with `κ(z)` a `k`-algebra via the canonical map
`pointBaseMap π z = Spec.preimage (Spec κ(z) → Z → Spec k)`:
`⨅_{U ∋ z} dim U = dim 𝒪_{Z,z} + trdeg_k κ(z)`. -/
theorem iInf_topologicalKrullDim_opens_eq_stalk_add_trdeg_pointBaseMap {k : Type u} [Field k]
    {Z : Scheme.{u}} (π : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType π] (z : Z) :
    letI : Algebra k (Z.residueField z) := (AlgebraicGeometry.Intersection.pointBaseMap π z).hom.toAlgebra
    (⨅ U ∈ {U : Z.Opens | z ∈ U}, topologicalKrullDim U) =
      ringKrullDim (Z.presheaf.stalk z) +
        (Cardinal.toENat (Algebra.trdeg k (Z.residueField z)) : WithBot ℕ∞) := by
  let _ : Algebra k (Z.residueField z) := (AlgebraicGeometry.Intersection.pointBaseMap π z).hom.toAlgebra
  -- an affine open neighbourhood `V ≅ Spec A` of `z`
  obtain ⟨_, ⟨V, hV0, rfl⟩, hzV, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hV : IsAffineOpen V := hV0
  let fA : Spec Γ(Z, V) ⟶ Spec (CommRingCat.of k) := hV.fromSpec ≫ π
  let _ : Algebra k Γ(Z, V) := (Spec.preimage fA).hom.toAlgebra
  have hft : Algebra.FiniteType k Γ(Z, V) := by
    have hlft : LocallyOfFiniteType (Spec.map (Spec.preimage fA)) := by
      rw [Spec.map_preimage]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hlft
  let y : PrimeSpectrum Γ(Z, V) := hV.primeIdealOf ⟨z, hzV⟩
  have hy : hV.fromSpec y = z := hV.fromSpec_primeIdealOf ⟨z, hzV⟩
  -- local dimension is computed on `Spec A`
  have hinf := hV.fromSpec.isOpenEmbedding.iInf_topologicalKrullDim_opens_eq y
  rw [hy] at hinf
  -- the stalk is `A_y`
  let _ : Algebra Γ(Z, V) (Z.presheaf.stalk z) := Z.presheaf.algebra_section_stalk ⟨z, hzV⟩
  have hloc : IsLocalization.AtPrime (Z.presheaf.stalk z) y.asIdeal :=
    hV.isLocalization_stalk ⟨z, hzV⟩
  have hstalk : ringKrullDim (Z.presheaf.stalk z) =
      ringKrullDim (Localization.AtPrime y.asIdeal) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height y.asIdeal (Z.presheaf.stalk z),
      IsLocalization.AtPrime.ringKrullDim_eq_height y.asIdeal (Localization.AtPrime y.asIdeal)]
  -- the residue field is `κ(y)`, as a `k`-algebra
  have htr : Algebra.trdeg k (Z.residueField z) = Algebra.trdeg k y.asIdeal.ResidueField := by
    let Y : AlgebraicGeometry.Proj.SchemeOver k := ⟨Z, π⟩
    let X' : AlgebraicGeometry.Proj.SchemeOver k := ⟨Spec Γ(Z, V), fA⟩
    let j : X'.scheme ⟶ Y.scheme := hV.fromSpec
    have hj : j ≫ Y.toBase = X'.toBase := rfl
    have hopen : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
    have : IsIso (j.residueFieldMap y) :=
      AlgebraicGeometry.Intersection.residueFieldMap_isIso_of_isOpenImmersion hV.fromSpec y
    have h1 := MiyaokaMori.PointClosureTrdeg.residueFieldMap_trdeg_eq_of_eq j hj y z hy
    have h2 := AlgebraicGeometry.Intersection.specResidueField_trdeg_eq Γ(Z, V) fA y
    exact h1.trans h2
  rw [hstalk, htr]
  exact hinf.symm.trans (stacks_00P1 (k := k) Γ(Z, V) y)

/-- If `g ≫ h` is a preimmersion (e.g. `g ≫ h = X.fromSpecResidueField x`), the induced map
`𝒪_{Y, g(𝔪)} → R` on the stalk at the closed point is surjective. -/
theorem surjective_stalkClosedPointTo_of_comp {R : CommRingCat.{u}} [IsLocalRing R]
    {Y W : Scheme.{u}} (g : Spec R ⟶ Y) (h : Y ⟶ W) [IsPreimmersion (g ≫ h)] :
    Function.Surjective (Scheme.stalkClosedPointTo g) := by
  have h2 : Function.Surjective (g.stalkMap (IsLocalRing.closedPoint R)) := by
    have h1 := (g ≫ h).stalkMap_surjective (IsLocalRing.closedPoint R)
    have hc := Scheme.Hom.stalkMap_comp g h (IsLocalRing.closedPoint R)
    intro t
    obtain ⟨a, ha⟩ := h1 t
    refine ⟨h.stalkMap _ a, ?_⟩
    erw [hc, CommRingCat.comp_apply] at ha
    exact ha
  intro t
  obtain ⟨a, ha⟩ := h2 ((stalkClosedPointIso R).inv t)
  refine ⟨a, ?_⟩
  change (g.stalkMap _ ≫ (stalkClosedPointIso R).hom) a = t
  rw [CommRingCat.comp_apply, ha]
  simp

end AlgebraicGeometry

/-- **Stacks 02FX**: local dimension of the fibre at a point. -/
theorem AlgebraicGeometry.iInf_topologicalKrullDim_fiber_eq_stalk_add_trdeg {X S : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType f] (x : X) :
    letI : Algebra (S.residueField (f.base x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
    (⨅ U ∈ {U : (f.fiber (f.base x)).Opens | f.asFiber x ∈ U}, topologicalKrullDim U) =
      ringKrullDim ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x)) +
        (Cardinal.toENat (Algebra.trdeg (S.residueField (f.base x)) (X.residueField x)) : WithBot ℕ∞) := by
  let _ : Algebra (S.residueField (f.base x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  -- the fibre as a scheme over `Spec κ(s)`, locally of finite type
  let π : f.fiber (f.base x) ⟶ Spec (S.residueField (f.base x)) := f.fiberToSpecResidueField (f.base x)
  have hπ : LocallyOfFiniteType π :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField (f.base x))))
  -- the `κ(x)`-point of the fibre corresponding to `x`
  let g : Spec (X.residueField x) ⟶ f.fiber (f.base x) := f.asFiberHom x
  let q : Spec (X.residueField x) := IsLocalRing.closedPoint (X.residueField x)
  have hgq : g q = f.asFiber x := by
    apply (f.fiberι (f.base x)).isEmbedding.injective
    rw [Scheme.Hom.fiberι_asFiber]
    change (g ≫ f.fiberι (f.base x)) q = x
    rw [Scheme.Hom.asFiberHom_fiberι]
    exact Scheme.fromSpecResidueField_apply x q
  rw [← hgq]
  have core := iInf_topologicalKrullDim_opens_eq_stalk_add_trdeg_pointBaseMap
    (k := S.residueField (f.base x)) π (g q)
  refine core.trans ?_
  -- compare the two `κ(s)`-algebra structures: `κ_{X_s}(x') ≅ κ_X(x)` over `κ(s)`
  let δ : (f.fiber (f.base x)).residueField (g q) ⟶ X.residueField x :=
    Scheme.descResidueField (K := X.residueField x) (Scheme.stalkClosedPointTo g)
  have hδ : AlgebraicGeometry.Intersection.pointBaseMap π (g q) ≫ δ = f.residueFieldMap x := by
    apply Spec.map_injective
    have hpb : Spec.map (AlgebraicGeometry.Intersection.pointBaseMap π (g q)) =
        (f.fiber (f.base x)).fromSpecResidueField (g q) ≫ π := Spec.map_preimage _
    have hg : Spec.map δ ≫ (f.fiber (f.base x)).fromSpecResidueField (g q) = g :=
      Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField (X.residueField x) _ g
    rw [Spec.map_comp, hpb]
    erw [← Category.assoc, hg]
    exact Scheme.Hom.asFiberHom_fiberToSpecResidueField f x
  have hpre : IsPreimmersion (g ≫ f.fiberι (f.base x)) := by
    rw [Scheme.Hom.asFiberHom_fiberι]; infer_instance
  have hsurj : Function.Surjective δ := by
    intro t
    obtain ⟨a, ha⟩ := surjective_stalkClosedPointTo_of_comp g (f.fiberι (f.base x)) t
    refine ⟨(f.fiber (f.base x)).residue _ a, ?_⟩
    rw [← ha]
    exact congrArg (fun m : (f.fiber (f.base x)).presheaf.stalk (g q) ⟶ X.residueField x => m a)
      (Scheme.residue_descResidueField (K := X.residueField x) (Scheme.stalkClosedPointTo g))
  let e : (f.fiber (f.base x)).residueField (g q) ≃+* X.residueField x :=
    RingEquiv.ofBijective δ.hom ⟨δ.hom.injective, hsurj⟩
  let _ : Algebra (S.residueField (f.base x)) ((f.fiber (f.base x)).residueField (g q)) :=
    (AlgebraicGeometry.Intersection.pointBaseMap π (g q)).hom.toAlgebra
  let e' : (f.fiber (f.base x)).residueField (g q) ≃ₐ[S.residueField (f.base x)] X.residueField x :=
    AlgEquiv.ofRingEquiv (f := e) fun t =>
      congrArg (fun m : S.residueField (f.base x) ⟶ X.residueField x => m.hom t) hδ
  exact congrArg (fun c : Cardinal.{u} => ringKrullDim ((f.fiber (f.base x)).presheaf.stalk (g q)) +
    ((Cardinal.toENat c : ℕ∞) : WithBot ℕ∞)) e'.trdeg_eq

end
