import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalFunctionsSheafSheafify
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalFunctionsSheafInjective

/-! # The image of `O_X` in `𝒦_X` is a subsheaf

Let `X` be a scheme and `q ∈ 𝒦_X(W)`. If every point of `W` has a neighbourhood `V ⊆ W` such that `q|_V`
lies in the image of `O_X(V) → 𝒦_X(V)`, then `q` lies in the image of `O_X(W) → 𝒦_X(W)`.

Proof: take local preimages `a_x ∈ O_X(V_x)`; since `O_X → 𝒦_X` is injective on every open
(`toRationalFunctionsSheaf_app_injective`), the `a_x` agree on overlaps and glue to `a ∈ O_X(W)` by the
sheaf condition; the image of `a` agrees locally with `q`, hence globally by separatedness of `𝒦_X`.
This is an implicit step in the proof of Hartshorne II.6.13.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- Composition of restriction maps of `𝒦_X` (elementwise form). -/
theorem rationalFunctionsSheaf_map_map (X : Scheme.{u}) {W V V' : X.Opens} (hVW : V ≤ W)
    (hV'V : V' ≤ V) (q : X.rationalFunctionsSheaf.obj.obj (op W)) :
    (X.rationalFunctionsSheaf.obj.map (homOfLE hV'V).op).hom
        ((X.rationalFunctionsSheaf.obj.map (homOfLE hVW).op).hom q) =
      (X.rationalFunctionsSheaf.obj.map (homOfLE (hV'V.trans hVW)).op).hom q := by
  have heq : X.rationalFunctionsSheaf.obj.map (homOfLE (hV'V.trans hVW)).op =
      X.rationalFunctionsSheaf.obj.map (homOfLE hVW).op ≫
        X.rationalFunctionsSheaf.obj.map (homOfLE hV'V).op := by
    rw [← Functor.map_comp]; rfl
  exact (congrArg (fun φ => φ.hom q) heq).symm

/-- `O_X → 𝒦_X` commutes with restriction (elementwise form). -/
theorem toRationalFunctionsSheaf_res (X : Scheme.{u}) {V V' : X.Opens} (hV'V : V' ≤ V)
    (a : Γ(X, V)) :
    (X.toRationalFunctionsSheaf.hom.app (op V')).hom ((X.presheaf.map (homOfLE hV'V).op).hom a) =
      (X.rationalFunctionsSheaf.obj.map (homOfLE hV'V).op).hom
        ((X.toRationalFunctionsSheaf.hom.app (op V)).hom a) :=
  congrArg (fun φ => φ.hom a) (X.toRationalFunctionsSheaf.hom.naturality (homOfLE hV'V).op)

/-- The image of `O_X` in `𝒦_X` is a subsheaf: a section that lies locally in the image lies in the image. -/
theorem mem_range_toRationalFunctionsSheaf_of_locally (X : Scheme.{u}) (W : X.Opens)
    (q : X.rationalFunctionsSheaf.obj.obj (op W))
    (hq : ∀ x ∈ W, ∃ (V : X.Opens) (_ : x ∈ V) (hVW : V ≤ W),
      (X.rationalFunctionsSheaf.obj.map (homOfLE hVW).op).hom q ∈
        Set.range (X.toRationalFunctionsSheaf.hom.app (op V)).hom) :
    q ∈ Set.range (X.toRationalFunctionsSheaf.hom.app (op W)).hom := by
  classical
  choose V hxV hVW a ha using hq
  let Vi : W → X.Opens := fun x => V x.1 x.2
  let ai : ∀ x : W, X.sheaf.obj.obj (op (Vi x)) := fun x => a x.1 x.2
  have hcover : W ≤ iSup Vi := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj Vi ai := by
    intro x y
    apply X.toRationalFunctionsSheaf_app_injective (Vi x ⊓ Vi y)
    have h1 := X.toRationalFunctionsSheaf_res (inf_le_left : Vi x ⊓ Vi y ≤ Vi x) (ai x)
    have h2 := X.toRationalFunctionsSheaf_res (inf_le_right : Vi x ⊓ Vi y ≤ Vi y) (ai y)
    refine h1.trans (Eq.trans ?_ h2.symm)
    rw [ha x.1 x.2, ha y.1 y.2, rationalFunctionsSheaf_map_map, rationalFunctionsSheaf_map_map]
  obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' Vi W
    (fun x => homOfLE (hVW x.1 x.2)) hcover ai hcompat
  refine ⟨b, ?_⟩
  apply X.rationalFunctionsSheaf.eq_of_locally_eq' Vi W (fun x => homOfLE (hVW x.1 x.2)) hcover
  intro x
  refine (X.toRationalFunctionsSheaf_res (hVW x.1 x.2) b).symm.trans ?_
  exact (congrArg (X.toRationalFunctionsSheaf.hom.app (op (Vi x))).hom (hb x)).trans (ha x.1 x.2)

end AlgebraicGeometry.Scheme

end
