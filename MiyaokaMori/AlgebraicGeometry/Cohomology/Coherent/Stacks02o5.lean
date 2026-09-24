import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.ClosedSubspaceCohomology
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.FiniteTypeOfFiniteAffineSections
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Cone.AmpleOXOne
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.CohomologyLongExactSequence
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensorPower
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.ProperPushforwardFiniteAffineSections
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01y1
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01y6
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01yi
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.Stacks01ys
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.Stacks02o4
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks0b5t
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.Stacks01f6
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.Stacks02uv
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks02ol
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks02om
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks01pu
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01lc

/-! # Proper pushforward preserves coherence (Stacks 02O5)

Proper pushforward preserves coherence (Stacks 02O5): if `f : X → Y` is proper, `Y` locally Noetherian
and `F` coherent, then `f_*F` is coherent.

Source: Stacks 02O5.

Assembly: `f_*F` is quasi-coherent (Stacks 01LC) and its sections over every affine open `V ⊆ Y` form a
finite `Γ(Y, V)`-module (`finite_sections_pushforward_of_isProper`, Stacks 02O5 in degree 0); a
quasi-coherent module with finite sections on an affine open neighbourhood of every point is of finite
type (`isFiniteType_of_finite_affine_sections`, Stacks 01PB).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 02O5 (coherent-proposition-proper-pushforward-coherent; EGA III 3.2.1), the `R^0` case:
`f : X → Y` proper, `Y` locally Noetherian, `F` coherent ⇒ `f_*F` coherent. (`IsCoherent` is
"quasi-coherent + finite type"; `Y` locally Noetherian and `f` of finite type
make `X` locally Noetherian, so on both sides this agrees with the usual notion. The higher direct images
`R^i f_*F` of the Stacks statement are not objects of this library and are not part of the signature.)

**Proof.**
1. `f` is proper, hence quasi-compact (`UniversallyClosed → QuasiCompact`) and quasi-separated
   (`IsSeparated → QuasiSeparated`), so `f_*F` is quasi-coherent: Stacks 01LC
   (`isQuasicoherent_pushforward`).
2. Every `y : Y` has an affine open neighbourhood `V` (Mathlib `Scheme.isBasis_affineOpens`), and
   `Γ(f_*F, V)` is a finite `Γ(Y, V)`-module: `finite_sections_pushforward_of_isProper`, which is
   Stacks 02O5 in degree `0`, proved through Stacks 02O6 applied to `f⁻¹V → Spec Γ(Y, V)`.
3. A quasi-coherent module whose sections over an affine open neighbourhood of every point are finite is
   of finite type: `isFiniteType_of_finite_affine_sections` (Stacks 01PB "⇐" made local). -/
theorem AlgebraicGeometry.pushforward_isCoherent_of_isProper {X Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian Y] (f : X ⟶ Y) [AlgebraicGeometry.IsProper f]
    (F : X.Modules) [F.IsCoherent] :
    ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj F).IsCoherent := by
  have : F.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
  have hqc : ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward f F
  refine ⟨hqc, ?_⟩
  apply AlgebraicGeometry.Scheme.Modules.isFiniteType_of_finite_affine_sections
  intro y
  obtain ⟨V, hV, hy, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
      (show y ∈ (⊤ : Y.Opens) from trivial)
  exact ⟨V, hV, hy, AlgebraicGeometry.finite_sections_pushforward_of_isProper f F V hV⟩

end
