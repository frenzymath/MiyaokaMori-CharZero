import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.FreeSheaf

/-! # Matrix cocycles and trivialization cocycles

Matrix cocycles and trivialization cocycles: matrices `g_{αα'}` on a family of opens `U_α` (with
coefficients in `Γ(U_α ∩ U_α')`) that are invertible and satisfy the cocycle condition
`g_{αα'}g_{α'α''} = g_{αα''}` (restricted to triple overlaps); `IsTrivializationCocycle V U g` says
that `V` has a frame `e_α` on each `U_α` (`V|_{U_α} ≅ O^r` sending the standard basis to `e_α`) with
`e_{α'} = e_α · g_{αα'}` on the overlaps (adapted frames give upper triangular transition matrices).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped AlgebraicGeometry

def IsMatrixCocycle {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} {r : ℕ} (U : ι → X.Opens)
    (g : ∀ α α' : ι, Matrix (Fin r) (Fin r) Γ(X, U α ⊓ U α')) : Prop :=
  (∀ α α', IsUnit (g α α').det) ∧
  ∀ α α' α'',
    (g α α').map (X.presheaf.map (CategoryTheory.homOfLE
        (le_trans inf_le_left le_rfl : U α ⊓ U α' ⊓ U α'' ≤ U α ⊓ U α')).op).hom *
      (g α' α'').map (X.presheaf.map (CategoryTheory.homOfLE
        (le_inf (le_trans inf_le_left inf_le_right) inf_le_right : U α ⊓ U α' ⊓ U α'' ≤ U α' ⊓ U α'')).op).hom =
    (g α α'').map (X.presheaf.map (CategoryTheory.homOfLE
        (le_inf (le_trans inf_le_left inf_le_left) inf_le_right : U α ⊓ U α' ⊓ U α'' ≤ U α ⊓ U α'')).op).hom

/-- A frame: a family of sections `e : Fin r → Γ(V, W)` on an open `W` whose restriction to every
  open subset `W'` of `W` is a basis of the `Γ(X, W')`-module `Γ(V, W')`. Equivalently, the map
  `O_W^r → V|_W` given by `e` via `freeHomEquiv` is an isomorphism (a morphism of sheaves is an
  isomorphism iff it is an isomorphism on sections over every open). -/

def AlgebraicGeometry.Scheme.Modules.IsFrameOn {X : AlgebraicGeometry.Scheme.{u}} {r : ℕ}
    (V : X.Modules) (W : X.Opens) (e : Fin r → Γ(V, W)) : Prop :=
  ∀ (W' : X.Opens) (h : W' ≤ W),
    LinearIndependent Γ(X, W') (fun i => V.presheaf.map (CategoryTheory.homOfLE h).op (e i)) ∧
      Submodule.span Γ(X, W') (Set.range fun i => V.presheaf.map (CategoryTheory.homOfLE h).op (e i)) = ⊤

/-- `V` has a frame `e_α` on each `U_α`, and on the overlap `U_α ⊓ U_α'` one has
`e_{α',j} = Σ_i (g_{αα'})_{ij} · e_{α,i}`, i.e. `e_{α'} = e_α · g_{αα'}`. -/

def IsTrivializationCocycle {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} {r : ℕ} (V : X.Modules)
    (U : ι → X.Opens) (g : ∀ α α' : ι, Matrix (Fin r) (Fin r) Γ(X, U α ⊓ U α')) : Prop :=
  ∃ e : ∀ α, Fin r → Γ(V, U α), (∀ α, AlgebraicGeometry.Scheme.Modules.IsFrameOn V (U α) (e α)) ∧
    ∀ α α' (j : Fin r),
      V.presheaf.map (CategoryTheory.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α')).op (e α' j) =
        ∑ i, g α α' i j •
          V.presheaf.map (CategoryTheory.homOfLE (inf_le_left : U α ⊓ U α' ≤ U α)).op (e α i)

end
