import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase

/-! # Evaluating a homogeneous polynomial at sections of a line bundle

Evaluating a homogeneous polynomial `F` of degree `e` at `N+1` global sections of a line bundle `A` gives a
global section of `A^{⊗e}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Monomial section: `g : Fin e → Fin (N+1)` lists the indices of the factors (following the right-recursion
    of `tensorPow`): `f_{g 0} ⊗ ⋯ ⊗ f_{g (e-1)} := ((1 ⊗ f_{g 0}) ⊗ ⋯) ⊗ f_{g (e-1)} ∈ Γ(X, A^{⊗e})`. -/

noncomputable def evalHomogeneousAtSections.monomial {X : AlgebraicGeometry.Scheme.{u}} (A : X.Modules) {N : ℕ}
    (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u)) :
    (e : ℕ) → (Fin e → Fin (N + 1)) →
      ((AlgebraicGeometry.Scheme.Modules.tensorPow A e).val.obj (Opposite.op ⊤) : Type u)
  | 0, _ => (1 : X.ringCatSheaf.obj.obj (Opposite.op ⊤))
  | e + 1, g => sectionTensor (evalHomogeneousAtSections.monomial A f e (fun i => g i.castSucc)) (f (g (Fin.last e)))

/-- An exponent `α` (of total degree `e`) expanded, in increasing order of the indices, into a list of
indices of length `e`. -/

noncomputable def evalHomogeneousAtSections.indices {N e : ℕ} (α : Fin (N + 1) →₀ ℕ) (hα : Finsupp.weight 1 α = e) :
    Fin e → Fin (N + 1) :=
  fun i => (α.toMultiset.sort (· ≤ ·)).get (i.cast (by
    rw [Multiset.length_sort, Finsupp.card_toMultiset, ← hα, Finsupp.weight_apply]
    simp [Finsupp.sum]))

noncomputable def evalHomogeneousAtSections {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : X.Modules) [A.IsLineBundle]
    {N e : ℕ} (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous e)
    (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u)) :
    ((AlgebraicGeometry.Scheme.Modules.tensorPow A e).val.obj (Opposite.op ⊤) : Type u) :=
  -- k → Γ(X, O_X): the structure morphism through Γ–Spec
  let φ : k →+* Γ(X, ⊤) := ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom
  ∑ α ∈ F.support.attach,
    (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from φ (F.coeff α.1)) •
      evalHomogeneousAtSections.monomial A f e
        (evalHomogeneousAtSections.indices α.1 (hF (MvPolynomial.mem_support_iff.mp α.2)))

end
