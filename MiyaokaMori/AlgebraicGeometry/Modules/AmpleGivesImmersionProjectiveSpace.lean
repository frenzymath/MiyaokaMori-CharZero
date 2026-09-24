import MiyaokaMori.AlgebraicGeometry.Modules.AmpleFiniteProjectivizationImmersion

/-! # An ample line bundle gives an immersion into projective space

Some positive power of an ample invertible sheaf `L` on a scheme `X` of finite type over a field gives
a `k`-immersion into some `P^N_k` (Stacks 01VU: finite type + ample ⇒ some `L^{⊗d}` is relatively very
ample; 01VR: over an affine base, relatively very ample means an immersion into projective space).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.exists_immersion_projectiveSpace_of_isAmple (k : Type u) [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [CompactSpace X] (L : X.Modules) [L.IsLineBundle] (hL : AlgebraicGeometry.IsAmple L) :
    ∃ (N : ℕ) (i : X ⟶ ProjectiveSpace N k),
      AlgebraicGeometry.IsImmersion i ∧ i.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  obtain ⟨n, N, _hn, P, hP, hi⟩ :=
    hL.exists_projectivizationMorphism_isImmersion k X L
  exact ⟨N,
    projectivizationMorphism (k := k)
      (AlgebraicGeometry.Scheme.Modules.tensorPow L n) P hP,
    hi, projectivizationMorphism_isOver _ P hP⟩

end
