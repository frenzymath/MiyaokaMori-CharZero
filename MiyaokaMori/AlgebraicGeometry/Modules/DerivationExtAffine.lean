import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentials

/-! # Derivations on an affine scheme are determined by their global sections

Statement: let `X` be an affine scheme, `f : X → S` any morphism and `F` any `O_X`-module
(not necessarily quasi-coherent). Two `f⁻¹O_S`-derivations `D₁, D₂ : O_X → F` with values in `F`
(`PresheafOfModules.Derivation'`) that agree on the global sections `Γ(X, ⊤)` are equal. (This is
the injectivity part of Stacks 01UO, "in the affine case derivations are determined by derivations
of the ring", valid for an arbitrary sheaf `F`.)

Proof:
1. First on a basic open `D(s)`, `s ∈ Γ(X, ⊤)`: `Γ(X, D(s)) = Γ(X, ⊤)_s`
   (`IsAffineOpen.isLocalization_of_eq_basicOpen`), so every `a ∈ Γ(X, D(s))` satisfies
   `a·t = b|_{D(s)}` with `b ∈ Γ(X, ⊤)` and `t = m|_{D(s)}` (`m` a power of `s`) a unit of
   `Γ(X, D(s))` (`IsLocalization.surj`, `map_units`).
2. Leibniz: `D_i(a·t) = a·D_i(t) + t·D_i(a)`, so `t·D_i(a) = D_i(b|) − a·D_i(t) = (D_i b)| − a·(D_i m)|`
   (derivations commute with restriction, `d_map`); the right-hand side is the same for `i = 1, 2`
   by hypothesis, and `t` is a unit, so `D₁ a = D₂ a`.
3. A general open `W` is covered by basic opens contained in it (`isBasis_basicOpen`), and
   `(D_i a)|_{D(s)} = D_i(a|_{D(s)})` agree by step 2; `F` is a sheaf, hence separated
   (`TopCat.Sheaf.eq_of_locally_eq'`), so `D₁ a = D₂ a`.

Reference: the injectivity part of Stacks 01UO.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

theorem Omega.derivation_ext_of_isAffine {X S : Scheme.{u}} [IsAffine X] (f : X ⟶ S) {F : X.Modules}
    (D₁ D₂ : (F.val).Derivation' (Scheme.inverseImageStructureMap f))
    (h : ∀ a : Γ(X, ⊤), D₁.d (X := op ⊤) a = D₂.d (X := op ⊤) a) : D₁ = D₂ := by
  -- on a basic open
  have hb : ∀ (s : Γ(X, ⊤)) (a : Γ(X, X.basicOpen s)),
      D₁.d (X := op (X.basicOpen s)) a = D₂.d (X := op (X.basicOpen s)) a := by
    intro s a
    let i : X.basicOpen s ⟶ ⊤ := homOfLE le_top
    let alg : Algebra Γ(X, ⊤) Γ(X, X.basicOpen s) := (X.presheaf.map i.op).hom.toAlgebra
    have loc : IsLocalization.Away s Γ(X, X.basicOpen s) :=
      (isAffineOpen_top X).isLocalization_of_eq_basicOpen s i rfl
    obtain ⟨⟨b, m⟩, hbm⟩ := IsLocalization.surj (Submonoid.powers s) a
    have ht : IsUnit (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen s) m) :=
      IsLocalization.map_units Γ(X, X.basicOpen s) m
    have key : ∀ D : (F.val).Derivation' (Scheme.inverseImageStructureMap f),
        (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen s) m) •
            (show Γ(F, X.basicOpen s) from D.d (X := op (X.basicOpen s)) a) =
          F.presheaf.map i.op (D.d (X := op ⊤) b) -
            a • F.presheaf.map i.op (D.d (X := op ⊤) (m : Γ(X, ⊤))) := by
      intro D
      have h1 : (show Γ(F, X.basicOpen s) from D.d (X := op (X.basicOpen s))
            (a * algebraMap Γ(X, ⊤) Γ(X, X.basicOpen s) m)) =
          a • (show Γ(F, X.basicOpen s) from D.d (X := op (X.basicOpen s))
            (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen s) m)) +
          (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen s) m) •
            (show Γ(F, X.basicOpen s) from D.d (X := op (X.basicOpen s)) a) :=
        D.d_mul (X := op (X.basicOpen s)) a (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen s) m)
      have h2 : (show Γ(F, X.basicOpen s) from D.d (X := op (X.basicOpen s))
            (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen s) b)) =
          F.presheaf.map i.op (D.d (X := op ⊤) b) := D.d_map i.op b
      have h3 : (show Γ(F, X.basicOpen s) from D.d (X := op (X.basicOpen s))
            (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen s) m)) =
          F.presheaf.map i.op (D.d (X := op ⊤) (m : Γ(X, ⊤))) := D.d_map i.op _
      rw [← h2, ← h3, ← hbm, h1]
      abel
    have e12 := (key D₁).trans ((by rw [h b, h m]) : _ = _) |>.trans (key D₂).symm
    exact (IsUnit.smul_left_cancel (α := Γ(X, X.basicOpen s)) (β := Γ(F, X.basicOpen s)) ht).mp e12
  ext W a
  obtain ⟨W⟩ := W
  have hcov : ∀ x : W, ∃ s : Γ(X, ⊤), X.basicOpen s ≤ W ∧ x.1 ∈ X.basicOpen s := by
    intro x
    obtain ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, h₁, h₂⟩ :=
      (isBasis_basicOpen X).exists_subset_of_mem_open x.2 W.isOpen
    exact ⟨s, h₂, h₁⟩
  choose s hs hx using hcov
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨_, F.isSheaf⟩ (fun x : W => X.basicOpen (s x)) W
    (fun x => homOfLE (hs x)) (fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hx ⟨y, hy⟩⟩) _ _ ?_
  intro x
  exact ((D₁.d_map (homOfLE (hs x)).op a).symm.trans (hb (s x) _)).trans
    (D₂.d_map (homOfLE (hs x)).op a)

end AlgebraicGeometry
