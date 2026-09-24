import MiyaokaMori.Prelude

/-! # Precomposing a rational map with a dominant morphism

Precomposition of a rational map along a dominant morphism, and the predicate "regular on an open
`U`" (Corollary 4.3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable def AlgebraicGeometry.Scheme.RationalMap.precomp
    {X Y Z : AlgebraicGeometry.Scheme.{u}} [PreirreducibleSpace X] [Nonempty Y]
    (φ : Y ⤏ Z) (g : X ⟶ Y) [AlgebraicGeometry.IsDominant g] : X ⤏ Z :=
  g.toRationalMap.comp φ

def IsRegularOn {X Y : AlgebraicGeometry.Scheme.{u}} (φ : X ⤏ Y) (U : X.Opens) : Prop :=
  U ≤ φ.domain

theorem precomp_domain_le {X Y Z : AlgebraicGeometry.Scheme.{u}} [PreirreducibleSpace X] [Nonempty Y]
    (φ : Y ⤏ Z) (g : X ⟶ Y) [AlgebraicGeometry.IsDominant g] (U : Y.Opens) (hU : IsRegularOn φ U) :
    IsRegularOn (φ.precomp g) ((TopologicalSpace.Opens.map g.base).obj U) := by
  intro x hx
  rw [AlgebraicGeometry.Scheme.RationalMap.mem_domain]
  have hx' : g.base x ∈ φ.domain := hU hx
  rw [AlgebraicGeometry.Scheme.RationalMap.mem_domain] at hx'
  obtain ⟨f, hxf, hf⟩ := hx'
  refine ⟨g.toPartialMap.comp f, ?_, ?_⟩
  · let x' : (⊤ : X.Opens).toScheme := ⟨x, trivial⟩
    apply ((⊤ : X.Opens).mem_ι_image_iff (x := x')).2
    change (g.toPartialMap.hom).base x' ∈ f.domain
    change g.base x ∈ f.domain
    exact hxf
  · rw [← hf]
    exact (AlgebraicGeometry.Scheme.RationalMap.toRationalMap_comp g.toPartialMap f).symm

end
