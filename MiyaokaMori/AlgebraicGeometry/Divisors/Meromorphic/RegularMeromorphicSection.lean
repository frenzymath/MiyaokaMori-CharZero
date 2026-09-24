import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle

/-! # Regular meromorphic sections of a line bundle

A regular meromorphic section of an invertible sheaf `L` (Stacks 02OX), given by a local fraction
representation: an open cover `{U_i}` with `s|_{U_i} = a_i / b_i`, where `a_i ∈ Γ(U_i, L)` is regular on
every stalk (`O_x → L_x`, `1 ↦ a_i` injective), `b_i ∈ Γ(U_i, O)` is a nonzerodivisor on every stalk, and
`b_j a_i = b_i a_j` on overlaps (i.e. `a_i/b_i = a_j/b_j` in `𝒦_X(L)`).
Source: Stacks 02OX (`divisors-definition-regular-meromorphic-section`); the local fraction form is the
first paragraph of the proof of 02P0.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The local fraction representation of a regular meromorphic section (Stacks 02OX; `𝒦_X` is the
sheafification of `U ↦ S(U)^{-1}O(U)` with `S(U)` the sections that are nonzerodivisors on all stalks, so
sections of `𝒦_X(L)` are locally `a/b` with `b ∈ S(U)`; `s` is regular iff `a` may be taken regular on
stalks as well, first paragraph of the proof of 02P0). The same `s` has many representations; two
representations `(a_i/b_i)`, `(a'_j/b'_j)` define the same section iff `b'_j a_i = b_i a'_j` on overlaps. -/

structure AlgebraicGeometry.Scheme.Modules.RegularMeromorphicSection {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] where
  ι : Type u
  U : ι → X.Opens
  cover : ∀ x : X, ∃ i, x ∈ U i
  num : ∀ i, Γ(L, U i)
  den : ∀ i, Γ(X, U i)
  den_mem_nonZeroDivisors : ∀ i (x : X) (hx : x ∈ U i),
    X.presheaf.germ (U i) x hx (den i) ∈ nonZeroDivisors (X.presheaf.stalk x)
  num_regular : ∀ i (x : X) (hx : x ∈ U i) (c : X.presheaf.stalk x),
    c • (show (L.stalk x : Type u) from TopCat.Presheaf.germ L.presheaf (U i) x hx (num i)) = 0 → c = 0
  compat : ∀ i j,
    X.presheaf.map (CategoryTheory.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (den j) •
        L.presheaf.map (CategoryTheory.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (num i) =
      X.presheaf.map (CategoryTheory.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (den i) •
        L.presheaf.map (CategoryTheory.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (num j)

end
