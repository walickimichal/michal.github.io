/-
  Parity-safe digraphs with countably many ends are kernel-perfect —
  proof of Theorem 1.2 of count-parity-safe.tex.

  Every lemma of the paper used in the proof is stated and proved in Lean;
  see the map and the STATUS below.

  Self-contained: the definitions of `count-parity-safe.lean` are repeated
  verbatim in §0, so the main theorem here is literally the statement there.

  Uses Mathlib.  NOT yet compiled: written without access to a Lean toolchain,
  so expect small API/name mismatches.

  Map to the paper (compiled numbering of count-parity-safe.tex):

    Lemma 2.1 (parity principle)          ↦ `closedWalk_even`, `exists_compColouring`
    Lemma 2.2 (Neumann-Lara)              ↦ `semikernel_sUnion_chain`, `semikernel_of_succClosed`,
                                             `semikernel_union`
    Proposition 2.3                        ↦ `kernel_of_semikernels`
    Corollary 2.4                          ↦ `exists_core`, `core_succClosed`
    Lemma 2.5 (two pieces)                 ↦ `two_pieces`
    Lemma 2.6 (canonical kernels)          ↦ `kappa_isKernel`, `kappa_mono`, `bipartite_kernelPerfectOn`
    Lemma 3.2 (parity cut criterion)       ↦ `parityDominates_iff_cut`
    Lemma 3.5 (feeding)                    ↦ `feeds_tails`, `feeds_refl`, `feeds_trans`,
                                             `tail_mem_endOf`
    Lemma 4.2 (finite-port regions)        ↦ `finitePort_union`, `finitePort_univ`, `cone_finitePort`
    Lemma 4.5 (sign rule)                  ↦ `sign_rule`
    Lemma 4.6 (layered solving)            ↦ `layered_solving` (via `layered_aux`,
                                             `layer_eq`, `layer_causal`, `layer_mono`)
    Lemma 4.7 (good solvers)               ↦ `good_solver_exists`
    Lemma 4.8 (adding a region)            ↦ `adding_region` (Step 2: `fix_solve`,
                                             `fix_aux`, largest fixed points `gfpF`)
    Lemma 1.3 (finite-port cover)          ↦ `cover` (via `exhaust_step`, `konig`,
                                             `limit_kernel`, `exhaust`)
    Lemma 5.1 (collision)                  ↦ `collision`
    Lemma 5.3 (essential vertices)         ↦ `essential_of_restrict`, `essential_cone`,
                                             `exists_essential`
    Lemma 5.5 (tails, splicing)            ↦ `isLadderRay_tail`, `isLadderRay_splice`
    Lemma 5.6 (ladder step)                ↦ `ladder_step` (paths as functions: `IsPathF`,
                                             `exists_pathF`, `concatF_path`)
    Proposition 5.7 (ladder rays exist)    ↦ `ladderRays_exist` (via `ladder_extend`)
    Lemma 6.1 (gate)                       ↦ `gate` (with `walk_path_parity`, Lemma 2.1(2))
    Lemma 6.2 (diagonal comb)              ↦ `diagonal_comb` (via `CombInv`, `comb_step`)
    Theorem 6.3 (ladder ends)              ↦ `uncountable_ladderEnds`
    Theorem 1.2                            ↦ `kernelPerfect_of_paritySafe_of_countable_ends`,
                                             `kernelPerfect_of_safe_of_countable_ends`

  STATUS
    proved:  everything; no `sorry` remains.

  Dependency of the proved part:
    Thm 1.2  ⇐  `exists_essential` (⇐ Lemma 1.3)  +  Thm 6.3
    Thm 6.3  ⇐  Prop 5.7  +  Lemma 6.2  +  tails (5.5(1), 3.5(3))
-/
import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Relation Set
open scoped Classical

open Lean.Parser.Tactic in
macro "push_neg" cfg:optConfig loc:(location)? : tactic =>
  `(tactic| push $cfg:optConfig Not $[$loc]?)

namespace ParitySafe

/-- `WalkN E u w n`: a walk of length `n` from `u` to `w`. -/
inductive WalkN {V : Type*} (E : V → V → Prop) : V → V → ℕ → Prop
  | nil (v : V) : WalkN E v v 0
  | cons {u v w : V} {n : ℕ} : E u v → WalkN E v w n → WalkN E u w (n + 1)

variable {V : Type*} (E : V → V → Prop)

/-! ## §0. Definitions of `count-parity-safe.lean` (verbatim) -/

def IsCycle (v : V) (p : List V) : Prop :=
  p ≠ [] ∧ List.IsChain E (v :: p) ∧ p.getLast? = some v ∧ p.Nodup

def NoOddCycle : Prop :=
  ∀ (v : V) (p : List V), IsCycle E v p → Even p.length

def IsKernelOf (X K : Set V) : Prop :=
  K ⊆ X ∧
  (∀ u ∈ K, ∀ w ∈ K, ¬ E u w) ∧
  (∀ v ∈ X, v ∉ K → ∃ w ∈ K, E v w)

def KernelPerfect : Prop :=
  ∀ X : Set V, ∃ K : Set V, IsKernelOf E X K

def IsRay (r : ℕ → V) : Prop :=
  Function.Injective r ∧ ∀ n : ℕ, E (r n) (r (n + 1))

def IsFan (v : V) (R : ℕ → V) (P : ℕ → List V) (k : ℕ → ℕ) : Prop :=
  (∀ n : ℕ,
    P n ≠ [] ∧ List.IsChain E (v :: P n) ∧ (v :: P n).Nodup ∧
    (P n).getLast? = some (R (k n))) ∧
  (∀ m n : ℕ, m ≠ n → List.Disjoint (P m) (P n))

def Dominates (v : V) (R : ℕ → V) : Prop :=
  ∃ (P : ℕ → List V) (k : ℕ → ℕ), IsFan E v R P k

def ParityDominates (v : V) (R : ℕ → V) : Prop :=
  ∃ (P : ℕ → List V) (k : ℕ → ℕ), IsFan E v R P k ∧
    {n : ℕ | Even ((P n).length + k n)}.Infinite ∧
    {n : ℕ | Odd ((P n).length + k n)}.Infinite

def Safe : Prop :=
  NoOddCycle E ∧
  ∀ R : ℕ → V, IsRay E R → ¬ {n : ℕ | Dominates E (R n) R}.Infinite

def IsParitySafe : Prop :=
  NoOddCycle E ∧
  ∀ R : ℕ → V, IsRay E R → ¬ {n : ℕ | ParityDominates E (R n) R}.Infinite

def ReachAvoiding (F : Finset V) (u w : V) : Prop :=
  u ∉ F ∧ ReflTransGen (fun a b => E a b ∧ b ∉ F) u w

def Feeds (R R' : ℕ → V) : Prop :=
  ∀ F : Finset V, ∃ m n : ℕ, ReachAvoiding E F (R m) (R' n)

def endOf (R : ℕ → V) : Set (ℕ → V) :=
  {R' | IsRay E R' ∧ Feeds E R R' ∧ Feeds E R' R}

def Ends : Set (Set (ℕ → V)) :=
  {S | ∃ R : ℕ → V, IsRay E R ∧ S = endOf E R}

/-! ## §1. Further definitions used in the proof -/

/-- The edge relation of the induced subgraph `G[Z]`. -/
def restrict (Z : Set V) : V → V → Prop :=
  fun a b => E a b ∧ a ∈ Z ∧ b ∈ Z

/-- Vertices reachable from `v` in `G[Z]` (by a path of length ≥ 0). -/
def reachIn (Z : Set V) (v : V) : Set V :=
  {w | ReflTransGen (restrict E Z) v w}

/-- `u ≺ v` (a *collision*): walks of both parities from `u` to `v`.
    By Lemma 2.1(2) this is the same as paths of both parities. -/
def Prec (u v : V) : Prop :=
  (∃ n, Even n ∧ WalkN E u v n) ∧ ∃ n, Odd n ∧ WalkN E u v n

/-- `G[Z]` is kernel-perfect. -/
def KernelPerfectOn (Z : Set V) : Prop :=
  ∀ X ⊆ Z, ∃ K : Set V, IsKernelOf E X K

/-- `S` is a semikernel of `G[X]`. -/
def IsSemikernelOf (X S : Set V) : Prop :=
  S ⊆ X ∧
  (∀ u ∈ S, ∀ w ∈ S, ¬ E u w) ∧
  (∀ u ∈ S, ∀ w ∈ X, E u w → ∃ s ∈ S, E w s)

/-- `G[X]` is a core: nonempty, without a nonempty semikernel. -/
def IsCore (X : Set V) : Prop :=
  X.Nonempty ∧ ∀ S, IsSemikernelOf E X S → S = ∅

/-- `D` is successor-closed in `G[X]`. -/
def SuccClosedIn (X D : Set V) : Prop :=
  ∀ u ∈ D, ∀ w ∈ X, E u w → w ∈ D

/-- The ports `∂U = post(U) \ U`. -/
def ports (U : Set V) : Set V :=
  {w | w ∉ U ∧ ∃ u ∈ U, E u w}

/-- Definition 4.1: a finite-port region. -/
def FinitePort (U : Set V) : Prop :=
  (ports E U).Finite

/-- Definition 5.2: `v` is essential: no finite-port region containing `v`
    induces a kernel-perfect graph. -/
def Essential (v : V) : Prop :=
  ∀ U : Set V, FinitePort E U → v ∈ U → ¬ KernelPerfectOn E U

/-- A ray lies in `Z`. -/
def LiesIn (R : ℕ → V) (Z : Set V) : Prop :=
  ∀ n, R n ∈ Z

/-- Definition 5.4: a ladder ray, with checkpoints `R (b i)`. -/
def IsLadderRay (R : ℕ → V) : Prop :=
  IsRay E R ∧ ∃ b : ℕ → ℕ, StrictMono b ∧
    (∀ i, Essential E (R (b i))) ∧
    ∀ i j, i < j → Prec E (R (b i)) (R (b j))

/-- Definition 5.8: the ladder ends living in `Z`. -/
def LadderEndsIn (Z : Set V) : Set (Set (ℕ → V)) :=
  {S | ∃ R, IsLadderRay E R ∧ LiesIn R Z ∧ S = endOf E R}

/-- A path of positive length `v :: P` in `G − F`, ending at `R k`. -/
def IsPathToRay (F : Finset V) (v : V) (R : ℕ → V) (P : List V) (k : ℕ) : Prop :=
  P ≠ [] ∧ List.IsChain E (v :: P) ∧ (v :: P).Nodup ∧
  P.getLast? = some (R k) ∧ ∀ x ∈ P, x ∉ F

/-! ### Strong components and the sign order (§4) -/

/-- The strong component of `s`. -/
def comp (s : V) : Set V :=
  {w | ReflTransGen E s w ∧ ReflTransGen E w s}

/-- `c` 2-colours every strong component: edges inside a component change colour. -/
def IsCompColouring (c : V → Bool) : Prop :=
  ∀ u v, E u v → ReflTransGen E v u → c u ≠ c v

/-- `a ≤_v b`: the usual order if `c v = false` (colour 0), reversed otherwise. -/
def leAt (c : V → Bool) (v : V) (a b : Bool) : Prop :=
  (c v = false → a = true → b = true) ∧ (c v = true → a = false → b = false)

/-- `a ⊑_S a'` on `Y`. -/
def SignLE (c : V → Bool) (S Y : Set V) (a a' : V → Bool) : Prop :=
  ∀ v ∈ Y, (v ∈ S → leAt c v (a v) (a' v)) ∧ (v ∉ S → a v = a' v)

/-- `α` on `U`, `β` elsewhere. -/
noncomputable def glue (U : Set V) (α β : V → Bool) : V → Bool :=
  fun v => if v ∈ U then α v else β v

/-- The kernel equation at `v` for the assignment `x`. -/
def KernelEqAt (x : V → Bool) (v : V) : Prop :=
  x v = true ↔ ∀ w, E v w → x w = false

/-- `1` iff `a` is `0` on all of `Y`. -/
noncomputable def allFalse (Y : Set V) (a : V → Bool) : Bool :=
  decide (∀ w ∈ Y, a w = false)

/-- A good (causal, monotone) solver for the finite-port region `U`.
    Port patterns are total maps `β : V → Bool`, of which only `β|∂U` is used. -/
def IsGoodSolver (c : V → Bool) (U : Set V) (σ : (V → Bool) → V → Bool) : Prop :=
  (∀ β, ∀ u ∈ U, KernelEqAt E (glue U (σ β) β) u) ∧
  (∀ β β', ∀ u ∈ U, (∀ b ∈ ports E U, ReflTransGen E u b → β b = β' b) →
      σ β u = σ β' u) ∧
  (∀ s β β', SignLE c (comp E s) (ports E U) β β' →
      SignLE c (comp E s) (U ∩ comp E s) (σ β) (σ β'))

/-- `τ` (a solver for `H ⊇ U`) extends `σ` (a solver for `U`). -/
def Extends (U H : Set V) (σ τ : (V → Bool) → V → Bool) : Prop :=
  ∀ β, ∀ u ∈ U, τ β u = σ (glue H (τ β) β) u

/-! ## §2. Kernels, semikernels and strong components -/

/-! ### Walks: basic facts -/

/-- A walk, as a function `f` with `f 0 = u`, `f n = w` and edges `f t → f (t+1)`. -/
lemma walkN_fun {u w : V} {n : ℕ} (h : WalkN E u w n) :
    ∃ f : ℕ → V, f 0 = u ∧ f n = w ∧ ∀ t < n, E (f t) (f (t + 1)) := by
  induction h with
  | nil v => exact ⟨fun _ => v, rfl, rfl, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  | @cons u v w n huv _ ih =>
    obtain ⟨f, hf0, hfn, hfe⟩ := ih
    refine ⟨fun t => if t = 0 then u else f (t - 1), ?_, ?_, ?_⟩
    · simp
    · show (if n + 1 = 0 then u else f (n + 1 - 1)) = w
      rw [ite_eq_right (Nat.succ_ne_zero n), Nat.add_sub_cancel]
      exact hfn
    · intro t ht
      show E (if t = 0 then u else f (t - 1)) (if t + 1 = 0 then u else f (t + 1 - 1))
      rw [ite_eq_right (Nat.succ_ne_zero t), Nat.add_sub_cancel]
      rcases t with _ | t
      · rw [ite_eq_left rfl, hf0]
        exact huv
      · rw [ite_eq_right (Nat.succ_ne_zero t), Nat.add_sub_cancel]
        exact hfe t (by omega)

/-- Concatenation of walks. -/
lemma walkN_append {u v w : V} {a b : ℕ} (h1 : WalkN E u v a) :
    WalkN E v w b → WalkN E u w (a + b) := by
  induction h1 with
  | nil x =>
    intro h2
    simpa using h2
  | cons huv _ ih =>
    intro h2
    rw [Nat.add_right_comm]
    exact WalkN.cons huv (ih h2)

/-- Reachability gives a walk. -/
lemma walkN_of_rtg {u w : V} (h : ReflTransGen E u w) : ∃ n, WalkN E u w n := by
  induction h with
  | refl => exact ⟨0, WalkN.nil _⟩
  | tail _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, walkN_append E hn (WalkN.cons hbc (WalkN.nil _))⟩

/-- A walk gives reachability. -/
lemma rtg_of_walkN {u w : V} {n : ℕ} (h : WalkN E u w n) : ReflTransGen E u w := by
  induction h with
  | nil v => exact ReflTransGen.refl
  | cons huv _ ih => exact ReflTransGen.head huv ih

/-- The list `f (s+1), …, f (s+k)`. -/
def pathList (f : ℕ → V) : ℕ → ℕ → List V
  | _, 0 => []
  | s, k + 1 => f (s + 1) :: pathList f (s + 1) k

lemma pathList_length (f : ℕ → V) : ∀ s k, (pathList f s k).length = k
  | _, 0 => rfl
  | s, k + 1 => by simp [pathList, pathList_length f (s + 1) k]

lemma pathList_mem (f : ℕ → V) :
    ∀ s k x, x ∈ pathList f s k → ∃ t, 1 ≤ t ∧ t ≤ k ∧ x = f (s + t)
  | _, 0, x, h => by simp [pathList] at h
  | s, k + 1, x, h => by
    have h' : x ∈ f (s + 1) :: pathList f (s + 1) k := h
    rcases List.mem_cons.mp h' with hx | hx
    · exact ⟨1, le_rfl, by omega, hx⟩
    · obtain ⟨t, ht1, htk, hxt⟩ := pathList_mem f (s + 1) k x hx
      refine ⟨t + 1, by omega, by omega, ?_⟩
      rw [hxt, show s + 1 + t = s + (t + 1) by omega]

lemma pathList_nodup (f : ℕ → V) :
    ∀ s k, (∀ i j, s < i → i ≤ s + k → s < j → j ≤ s + k → f i = f j → i = j) →
      (pathList f s k).Nodup
  | _, 0, _ => List.nodup_nil
  | s, k + 1, hinj => by
    have hdef : pathList f s (k + 1) = f (s + 1) :: pathList f (s + 1) k := rfl
    rw [hdef, List.nodup_cons]
    refine ⟨fun hmem => ?_, pathList_nodup f (s + 1) k
      (fun i j hi hi' hj hj' hij => hinj i j (by omega) (by omega) (by omega) (by omega) hij)⟩
    obtain ⟨t, ht1, htk, hxt⟩ := pathList_mem f (s + 1) k (f (s + 1)) hmem
    have := hinj (s + 1) (s + 1 + t) (by omega) (by omega) (by omega) (by omega) hxt
    omega

lemma pathList_chain (R : V → V → Prop) (f : ℕ → V) :
    ∀ s k, (∀ t < k, R (f (s + t)) (f (s + t + 1))) → List.IsChain R (f s :: pathList f s k)
  | s, 0, _ => List.IsChain.singleton (f s)
  | s, k + 1, h => by
    have hdef : (f s :: pathList f s (k + 1)) = f s :: f (s + 1) :: pathList f (s + 1) k := rfl
    rw [hdef]
    refine List.IsChain.cons_cons ?_ (pathList_chain R f (s + 1) k ?_)
    · simpa using h 0 (Nat.succ_pos k)
    · intro t ht
      have h' := h (t + 1) (by omega)
      rw [show s + (t + 1) = s + 1 + t by omega] at h'
      exact h'

lemma pathList_getLast (f : ℕ → V) :
    ∀ s k, (pathList f s (k + 1)).getLast? = some (f (s + k + 1))
  | s, 0 => by simp [pathList]
  | s, k + 1 => by
    have h1 : pathList f s (k + 1 + 1) = f (s + 1) :: pathList f (s + 1) (k + 1) := rfl
    have h2 : pathList f (s + 1) (k + 1) = f (s + 1 + 1) :: pathList f (s + 1 + 1) k := rfl
    have ih := pathList_getLast f (s + 1) k
    rw [h2] at ih
    rw [h1, h2, List.getLast?_cons_cons, ih, show s + (k + 1) + 1 = s + 1 + k + 1 by omega]

/-- Lemma 2.1(1): every closed walk has even length.
    A shortest odd closed walk repeats no vertex, so it is an odd cycle. -/
lemma closedWalk_even (hodd : NoOddCycle E) {v : V} {n : ℕ} (h : WalkN E v v n) :
    Even n := by
  by_contra hn
  have hn' : Odd n := Nat.not_even_iff_odd.mp hn
  obtain ⟨f, hf0, hfn, hfe⟩ := walkN_fun E h
  have hex : ∃ n, ∃ f : ℕ → V, f n = f 0 ∧ (∀ t < n, E (f t) (f (t + 1))) ∧ Odd n :=
    ⟨n, f, by rw [hfn, hf0], hfe, hn'⟩
  obtain ⟨g, hg0, hge, hgodd⟩ := Nat.find_spec hex
  set N := Nat.find hex with hN
  -- a shortest odd closed walk visits no vertex twice among positions `1, …, N`
  have key : ∀ a b, 0 < a → a < b → b ≤ N → g a = g b → False := by
    intro a b ha hab hbN hgab
    rcases Nat.even_or_odd (b - a) with he | ho
    · -- cut out the closed walk from position `a` to `b`: the rest is shorter and odd
      apply Nat.find_min hex (show N - (b - a) < N by omega)
      refine ⟨fun t => if t < a then g t else g (t + (b - a)), ?_, ?_, ?_⟩
      · show (if N - (b - a) < a then g (N - (b - a)) else g (N - (b - a) + (b - a))) =
            (if 0 < a then g 0 else g (0 + (b - a)))
        rw [ite_eq_right (show ¬ (N - (b - a) < a) by omega), ite_eq_left ha,
          show N - (b - a) + (b - a) = N by omega, hg0]
      · intro t ht
        show E (if t < a then g t else g (t + (b - a)))
          (if t + 1 < a then g (t + 1) else g (t + 1 + (b - a)))
        by_cases h1 : t + 1 < a
        · rw [ite_eq_left (show t < a by omega), ite_eq_left h1]
          exact hge t (by omega)
        · by_cases h2 : t < a
          · rw [ite_eq_left h2, ite_eq_right h1, show t + 1 + (b - a) = b by omega, ← hgab,
              show a = t + 1 by omega]
            exact hge t (by omega)
          · rw [ite_eq_right h2, ite_eq_right h1, show t + 1 + (b - a) = t + (b - a) + 1 by omega]
            exact hge _ (by omega)
      · obtain ⟨r, hr⟩ := he
        obtain ⟨q, hq⟩ := hgodd
        exact ⟨q - r, by omega⟩
    · -- the closed walk from position `a` to `b` is shorter and odd
      apply Nat.find_min hex (show b - a < N by omega)
      refine ⟨fun t => g (a + t), ?_, ?_, ho⟩
      · show g (a + (b - a)) = g (a + 0)
        rw [show a + (b - a) = b by omega, Nat.add_zero, hgab]
      · intro t ht
        exact hge (a + t) (by omega)
  have hinj : ∀ i j, 0 < i → i ≤ 0 + N → 0 < j → j ≤ 0 + N → g i = g j → i = j := by
    intro i j hi hiN hj hjN hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key i j hi h (by omega) hij
    · exact key j i hj h (by omega) hij.symm
  obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := by
    obtain ⟨q, hq⟩ := hgodd
    exact ⟨2 * q, hq⟩
  have hcyc : IsCycle E (g 0) (pathList g 0 N) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hM]
      exact List.cons_ne_nil _ _
    · exact pathList_chain E g 0 N (fun t ht => by simpa using hge t ht)
    · rw [hM, pathList_getLast g 0 M, show 0 + M + 1 = N by omega, hg0]
    · exact pathList_nodup g 0 N hinj
  have hev := hodd (g 0) (pathList g 0 N) hcyc
  rw [pathList_length] at hev
  exact Nat.not_even_iff_odd.mpr hgodd hev

/-- Lemma 2.1(3), core fact: walks between two vertices of one strong component
    all have the same parity. -/
lemma walk_parity (hodd : NoOddCycle E) {u w : V} {a b : ℕ}
    (ha : WalkN E u w a) (hb : WalkN E u w b) (hwu : ReflTransGen E w u) :
    (Even a ↔ Even b) := by
  obtain ⟨k, hk⟩ := walkN_of_rtg E hwu
  have h1 := closedWalk_even E hodd (walkN_append E ha hk)
  have h2 := closedWalk_even E hodd (walkN_append E hb hk)
  rw [Nat.even_add] at h1 h2
  exact h1.trans h2.symm

lemma oddWalk_iff (hodd : NoOddCycle E) {r x : V} {m : ℕ} (hm : WalkN E r x m)
    (hxr : ReflTransGen E x r) :
    (∃ n, Odd n ∧ WalkN E r x n) ↔ Odd m := by
  constructor
  · rintro ⟨n, hn, hw⟩
    have hp := walk_parity E hodd hw hm hxr
    rcases Nat.even_or_odd m with hme | hmo
    · exact absurd (hp.mpr hme) (Nat.not_even_iff_odd.mpr hn)
    · exact hmo
  · intro hmo
    exact ⟨m, hmo, hm⟩

/-- A chosen representative of the strong component of `v`. -/
noncomputable def rep (v : V) : V :=
  @Classical.epsilon V ⟨v⟩ (fun r => r ∈ comp E v)

lemma rep_mem (v : V) : rep E v ∈ comp E v := by
  show (@Classical.epsilon V ⟨v⟩ (fun r => r ∈ comp E v)) ∈ comp E v
  exact Classical.epsilon_spec ⟨v, ReflTransGen.refl, ReflTransGen.refl⟩

/-- Lemma 2.1(3): every strong component has a proper 2-colouring:
    colour `v` by the parity of the walks from the representative of its component. -/
lemma exists_compColouring (hodd : NoOddCycle E) :
    ∃ c : V → Bool, IsCompColouring E c := by
  refine ⟨fun v => decide (∃ n, Odd n ∧ WalkN E (rep E v) v n), ?_⟩
  intro u v huv hvu hc
  have huv' : ReflTransGen E u v := ReflTransGen.single huv
  have hcomp : comp E u = comp E v := by
    ext w
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hvu.trans h1, h2.trans huv'⟩
    · rintro ⟨h1, h2⟩
      exact ⟨huv'.trans h1, h2.trans hvu⟩
  have hrep : rep E u = rep E v := by
    show @Classical.epsilon V ⟨u⟩ (fun r => r ∈ comp E u) =
      @Classical.epsilon V ⟨v⟩ (fun r => r ∈ comp E v)
    rw [hcomp]
  have hru : rep E u ∈ comp E u := rep_mem E u
  rw [hrep] at hru
  -- `hru.1 : u ⟶* rep v`, `hru.2 : rep v ⟶* u`
  obtain ⟨m, hm⟩ := walkN_of_rtg E hru.2
  have hmv : WalkN E (rep E v) v (m + 1) := walkN_append E hm (WalkN.cons huv (WalkN.nil v))
  have h1 := oddWalk_iff E hodd hm hru.1
  have h2 := oddWalk_iff E hodd hmv (hvu.trans hru.1)
  have hc' : decide (∃ n, Odd n ∧ WalkN E (rep E u) u n) =
      decide (∃ n, Odd n ∧ WalkN E (rep E v) v n) := hc
  rw [hrep] at hc'
  have hiff := decide_eq_decide.mp hc'
  have hkey : Odd m ↔ Odd (m + 1) := h1.symm.trans (hiff.trans h2)
  rw [Nat.odd_add_one] at hkey
  exact iff_not_self hkey

lemma isSemikernelOf_of_isKernelOf {X K : Set V} (h : IsKernelOf E X K) :
    IsSemikernelOf E X K :=
  ⟨h.1, h.2.1, fun u hu w hw huw => h.2.2 w hw (fun hwK => h.2.1 u hu w hwK huw)⟩

lemma kernel_nonempty {X K : Set V} (h : IsKernelOf E X K) (hX : X.Nonempty) :
    K.Nonempty := by
  obtain ⟨x, hx⟩ := hX
  by_cases hxK : x ∈ K
  · exact ⟨x, hxK⟩
  · obtain ⟨w, hw, -⟩ := h.2.2 x hx hxK
    exact ⟨w, hw⟩

/-- Lemma 2.2(1): the union of a chain of semikernels is a semikernel. -/
lemma semikernel_sUnion_chain (X : Set V) (C : Set (Set V))
    (hC : IsChain (· ⊆ ·) C) (hS : ∀ S ∈ C, IsSemikernelOf E X S) :
    IsSemikernelOf E X (⋃₀ C) := by
  refine ⟨sUnion_subset fun S hS' => (hS S hS').1, ?_, ?_⟩
  · intro u hu w hw huw
    obtain ⟨S1, hS1, hu1⟩ := mem_sUnion.mp hu
    obtain ⟨S2, hS2, hw2⟩ := mem_sUnion.mp hw
    by_cases h12 : S1 = S2
    · subst h12
      exact (hS S1 hS1).2.1 u hu1 w hw2 huw
    · rcases hC hS1 hS2 h12 with h | h
      · exact (hS S2 hS2).2.1 u (h hu1) w hw2 huw
      · exact (hS S1 hS1).2.1 u hu1 w (h hw2) huw
  · intro u hu w hw huw
    obtain ⟨S1, hS1, hu1⟩ := mem_sUnion.mp hu
    obtain ⟨s, hs, hws⟩ := (hS S1 hS1).2.2 u hu1 w hw huw
    exact ⟨s, mem_sUnion_of_mem hs hS1, hws⟩

/-- Lemma 2.2(2): a semikernel of a successor-closed `G[D]` is one of `G[X]`. -/
lemma semikernel_of_succClosed {X D S : Set V} (hDX : D ⊆ X) (hD : SuccClosedIn E X D)
    (hS : IsSemikernelOf E D S) : IsSemikernelOf E X S :=
  ⟨hS.1.trans hDX, hS.2.1,
    fun u hu w hw huw => hS.2.2 u hu w (hD u (hS.1 hu) w hw huw) huw⟩

/-- Lemma 2.2(3). -/
lemma semikernel_union (X S S' : Set V) (hS : IsSemikernelOf E X S)
    (hS' : IsSemikernelOf E {v | v ∈ X ∧ v ∉ S ∧ ∀ s ∈ S, ¬ E v s} S') :
    IsSemikernelOf E X (S ∪ S') := by
  obtain ⟨hSX, hSi, hSa⟩ := hS
  obtain ⟨hS'C, hS'i, hS'a⟩ := hS'
  refine ⟨union_subset hSX (fun x hx => (hS'C hx).1), ?_, ?_⟩
  · intro u hu w hw huw
    rcases hu with hu | hu <;> rcases hw with hw | hw
    · exact hSi u hu w hw huw
    · obtain ⟨s, hs, hws⟩ := hSa u hu w (hS'C hw).1 huw
      exact (hS'C hw).2.2 s hs hws
    · exact (hS'C hu).2.2 w hw huw
    · exact hS'i u hu w hw huw
  · intro u hu w hw huw
    rcases hu with hu | hu
    · obtain ⟨s, hs, hws⟩ := hSa u hu w hw huw
      exact ⟨s, Or.inl hs, hws⟩
    · by_cases hpre : ∃ s ∈ S, E w s
      · obtain ⟨s, hs, hws⟩ := hpre
        exact ⟨s, Or.inl hs, hws⟩
      · have hwS : w ∉ S := fun hwS => (hS'C hu).2.2 w hwS huw
        have hwC : w ∈ {v | v ∈ X ∧ v ∉ S ∧ ∀ s ∈ S, ¬ E v s} :=
          ⟨hw, hwS, fun s hs hws => hpre ⟨s, hs, hws⟩⟩
        obtain ⟨s, hs, hws⟩ := hS'a u hu w hwC huw
        exact ⟨s, Or.inr hs, hws⟩

/-- Proposition 2.3 (Neumann-Lara; Zorn). -/
lemma kernel_of_semikernels (X : Set V)
    (h : ∀ Y ⊆ X, Y.Nonempty → ∃ S, IsSemikernelOf E Y S ∧ S.Nonempty) :
    ∃ K, IsKernelOf E X K := by
  -- a maximal semikernel, by Zorn's lemma and Lemma 2.2(1)
  obtain ⟨M, hM⟩ := zorn_subset {S | IsSemikernelOf E X S} (by
    intro c hc hchain
    refine ⟨⋃₀ c, semikernel_sUnion_chain E X c hchain (fun S hS => hc hS), ?_⟩
    intro s hs
    exact subset_sUnion_of_mem hs)
  have hMs : IsSemikernelOf E X M := hM.1
  refine ⟨M, hMs.1, hMs.2.1, ?_⟩
  -- if some vertex were not absorbed, the rest `C` would give a larger semikernel
  intro v hv hvM
  by_contra hno
  have hvC : v ∈ {x | x ∈ X ∧ x ∉ M ∧ ∀ s ∈ M, ¬ E x s} :=
    ⟨hv, hvM, fun s hs hvs => hno ⟨s, hs, hvs⟩⟩
  obtain ⟨S', hS', hne⟩ :=
    h {x | x ∈ X ∧ x ∉ M ∧ ∀ s ∈ M, ¬ E x s} (fun x hx => hx.1) ⟨v, hvC⟩
  have hU : IsSemikernelOf E X (M ∪ S') := semikernel_union E X M S' hMs hS'
  have hsub : M ∪ S' ⊆ M := hM.2 hU subset_union_left
  obtain ⟨x, hx⟩ := hne
  exact (hS'.1 hx).2.1 (hsub (Or.inr hx))

/-- Corollary 2.4, first part: a non-kernel-perfect `G[X]` contains an induced core. -/
lemma exists_core (X : Set V) (h : ¬ KernelPerfectOn E X) :
    ∃ C ⊆ X, IsCore E C := by
  by_contra hno
  apply h
  intro Y hY
  apply kernel_of_semikernels E
  intro Y' hY' hne
  by_contra hS
  apply hno
  refine ⟨Y', hY'.trans hY, hne, ?_⟩
  intro S hSk
  by_contra hSne
  exact hS ⟨S, hSk, ne_empty_iff_nonempty.mp hSne⟩

/-- Corollary 2.4, second part: nonempty successor-closed parts of a core are cores. -/
lemma core_succClosed {C D : Set V} (hC : IsCore E C) (hDC : D ⊆ C)
    (hD : SuccClosedIn E C D) (hne : D.Nonempty) : IsCore E D :=
  ⟨hne, fun S hS => hC.2 S (semikernel_of_succClosed E hDC hD hS)⟩

/-- Corollary 2.4: a core has no sink. -/
lemma core_no_sink {C : Set V} (hC : IsCore E C) {v : V} (hv : v ∈ C) :
    ∃ w ∈ C, E v w := by
  by_contra hno
  have hS : IsSemikernelOf E C {v} := by
    refine ⟨singleton_subset_iff.mpr hv, ?_, ?_⟩
    · intro a ha b hb hab
      rw [mem_singleton_iff] at ha hb
      rw [ha, hb] at hab
      exact hno ⟨v, hv, hab⟩
    · intro a ha w hw haw
      rw [mem_singleton_iff] at ha
      rw [ha] at haw
      exact (hno ⟨w, hw, haw⟩).elim
  have := hC.2 {v} hS
  exact (ne_empty_iff_nonempty.mpr (singleton_nonempty v)) this

/-- Lemma 2.5 (two pieces). -/
lemma two_pieces {X D : Set V} (hDX : D ⊆ X) (hD : SuccClosedIn E X D)
    (h1 : KernelPerfectOn E D) (h2 : KernelPerfectOn E (X \ D)) :
    KernelPerfectOn E X := by
  intro Y hY
  apply kernel_of_semikernels E
  intro Y' hY' hne
  by_cases hint : (Y' ∩ D).Nonempty
  · obtain ⟨K, hK⟩ := h1 (Y' ∩ D) inter_subset_right
    refine ⟨K, semikernel_of_succClosed E inter_subset_left ?_
      (isSemikernelOf_of_isKernelOf E hK), kernel_nonempty E hK hint⟩
    intro u hu w hw huw
    exact ⟨hw, hD u hu.2 w (hY (hY' hw)) huw⟩
  · have hsub : Y' ⊆ X \ D := fun y hy => ⟨hY (hY' hy), fun hyD => hint ⟨y, hy, hyD⟩⟩
    obtain ⟨K, hK⟩ := h2 Y' hsub
    exact ⟨K, isSemikernelOf_of_isKernelOf E hK, kernel_nonempty E hK hne⟩

/-! ### Canonical kernels of bipartite graphs (Lemma 2.6) -/

/-- `Φ_Q(T)`, with colour classes `B₀ = {c = false}`, `B₁ = {c = true}`. -/
def PhiQ (c : V → Bool) (Q T : Set V) : Set V :=
  {x | x ∈ Q ∧ c x = false ∧ ∀ y ∈ Q, E x y → ∃ t ∈ T, E y t}

/-- `T(Q)`: the union of all post-fixed points of `Φ_Q`. -/
def TQ (c : V → Bool) (Q : Set V) : Set V :=
  ⋃₀ {T | T ⊆ {x | x ∈ Q ∧ c x = false} ∧ T ⊆ PhiQ E c Q T}

/-- The canonical kernel `κ(Q)`. -/
def kappa (c : V → Bool) (Q : Set V) : Set V :=
  TQ E c Q ∪ {y | y ∈ Q ∧ c y = true ∧ ∀ t ∈ TQ E c Q, ¬ E y t}

/-- `c` properly 2-colours `G[Z]`. -/
def IsBipartiteOn (c : V → Bool) (Z : Set V) : Prop :=
  ∀ u ∈ Z, ∀ v ∈ Z, E u v → c u ≠ c v

lemma phiQ_mono (c : V → Bool) (Q : Set V) {T T' : Set V} (h : T ⊆ T') :
    PhiQ E c Q T ⊆ PhiQ E c Q T' := by
  rintro x ⟨hxQ, hxc, hx⟩
  refine ⟨hxQ, hxc, fun y hy hxy => ?_⟩
  obtain ⟨t, ht, hyt⟩ := hx y hy hxy
  exact ⟨t, h ht, hyt⟩

lemma TQ_subset (c : V → Bool) (Q : Set V) :
    TQ E c Q ⊆ {x | x ∈ Q ∧ c x = false} := by
  intro x hx
  unfold TQ at hx
  obtain ⟨T, hT, hxT⟩ := mem_sUnion.mp hx
  exact hT.1 hxT

/-- `T(Q) ⊆ Φ_Q(T(Q))`. -/
lemma TQ_post (c : V → Bool) (Q : Set V) :
    TQ E c Q ⊆ PhiQ E c Q (TQ E c Q) := by
  intro x hx
  unfold TQ at hx
  obtain ⟨T, hT, hxT⟩ := mem_sUnion.mp hx
  exact phiQ_mono E c Q (subset_sUnion_of_mem hT) (hT.2 hxT)

/-- `Φ_Q(T(Q)) ⊆ T(Q)`; with `TQ_post`, `T(Q)` is a fixed point. -/
lemma TQ_fixed (c : V → Bool) (Q : Set V) :
    PhiQ E c Q (TQ E c Q) ⊆ TQ E c Q := by
  intro x hx
  exact mem_sUnion_of_mem hx
    ⟨fun y hy => ⟨hy.1, hy.2.1⟩, phiQ_mono E c Q (TQ_post E c Q)⟩

/-- Lemma 2.6(1). -/
lemma kappa_isKernel (c : V → Bool) (Q : Set V) (hc : IsBipartiteOn E c Q) :
    IsKernelOf E Q (kappa E c Q) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x (hx | hx)
    · exact (TQ_subset E c Q hx).1
    · exact hx.1
  · rintro u (hu | hu) w (hw | hw) huw
    · exact hc u (TQ_subset E c Q hu).1 w (TQ_subset E c Q hw).1 huw
        (by rw [(TQ_subset E c Q hu).2, (TQ_subset E c Q hw).2])
    · obtain ⟨t, ht, hwt⟩ := (TQ_post E c Q hu).2.2 w hw.1 huw
      exact hw.2.2 t ht hwt
    · exact hu.2.2 w hw huw
    · exact hc u hu.1 w hw.1 huw (by rw [hu.2.1, hw.2.1])
  · intro v hvQ hvK
    by_cases hcv : c v = true
    · by_contra hno
      exact hvK (Or.inr ⟨hvQ, hcv, fun t ht hvt => hno ⟨t, Or.inl ht, hvt⟩⟩)
    · have hcv' : c v = false := by simpa using hcv
      have hvT : v ∉ PhiQ E c Q (TQ E c Q) := fun h => hvK (Or.inl (TQ_fixed E c Q h))
      have hn : ¬ ∀ y ∈ Q, E v y → ∃ t ∈ TQ E c Q, E y t := fun h => hvT ⟨hvQ, hcv', h⟩
      push_neg at hn
      obtain ⟨y, hyQ, hvy, hy⟩ := hn
      have hcy : c y = true := by
        have hne := hc v hvQ y hyQ hvy
        rw [hcv'] at hne
        simpa using hne.symm
      exact ⟨y, Or.inr ⟨hyQ, hcy, hy⟩, hvy⟩

/-- Lemma 2.6(2): monotonicity of `κ`. (Needs `c` to colour `G[Q']` properly:
    then every successor in `Q'` of a colour-0 vertex has colour 1.) -/
lemma kappa_mono (c : V → Bool) (Q Q' : Set V) (hc' : IsBipartiteOn E c Q')
    (h0 : {x | x ∈ Q ∧ c x = false} ⊆ {x | x ∈ Q' ∧ c x = false})
    (h1 : {x | x ∈ Q' ∧ c x = true} ⊆ {x | x ∈ Q ∧ c x = true}) :
    {x | x ∈ kappa E c Q ∧ c x = false} ⊆ {x | x ∈ kappa E c Q' ∧ c x = false} ∧
    {x | x ∈ kappa E c Q' ∧ c x = true} ⊆ {x | x ∈ kappa E c Q ∧ c x = true} := by
  have hT : TQ E c Q ⊆ TQ E c Q' := by
    intro x hx
    refine mem_sUnion_of_mem hx ⟨fun z hz => h0 (TQ_subset E c Q hz), ?_⟩
    intro z hz
    have hzQ' : z ∈ {x | x ∈ Q' ∧ c x = false} := h0 (TQ_subset E c Q hz)
    have hzP := TQ_post E c Q hz
    refine ⟨hzQ'.1, hzQ'.2, fun y hyQ' hzy => ?_⟩
    have hcy : c y = true := by
      have hne := hc' z hzQ'.1 y hyQ' hzy
      rw [hzQ'.2] at hne
      simpa using hne.symm
    have hyQ : y ∈ {x | x ∈ Q ∧ c x = true} := h1 ⟨hyQ', hcy⟩
    exact hzP.2.2 y hyQ.1 hzy
  refine ⟨?_, ?_⟩
  · rintro x ⟨hx | hx, hxc⟩
    · exact ⟨Or.inl (hT hx), hxc⟩
    · rw [hx.2.1] at hxc
      exact absurd hxc (by decide)
  · rintro y ⟨hy | hy, hyc⟩
    · rw [(TQ_subset E c Q' hy).2] at hyc
      exact absurd hyc (by decide)
    · exact ⟨Or.inr ⟨(h1 ⟨hy.1, hyc⟩).1, hyc, fun t ht hyt => hy.2.2 t (hT ht) hyt⟩, hyc⟩

/-- Lemma 2.6(1), second sentence: bipartite graphs are kernel-perfect. -/
lemma bipartite_kernelPerfectOn (c : V → Bool) (Z : Set V) (hc : IsBipartiteOn E c Z) :
    KernelPerfectOn E Z :=
  fun X hX => ⟨kappa E c X, kappa_isKernel E c X (fun u hu v hv huv => hc u (hX hu) v (hX hv) huv)⟩

/-! ## §3. Rays: fans, parity fans, feeding and ends -/

/-- Safe digraphs are parity-safe: a mixed fan is in particular a fan. -/
theorem isParitySafe_of_safe (h : Safe E) : IsParitySafe E := by
  refine ⟨h.1, fun R hR hinf => h.2 R hR (hinf.mono ?_)⟩
  intro n hn
  obtain ⟨P, k, hfan, -⟩ := hn
  show ∃ (P : ℕ → List V) (k : ℕ → ℕ), IsFan E (R n) R P k
  exact ⟨P, k, hfan⟩

lemma mem_of_getLast {l : List V} {a : V} (h : l.getLast? = some a) : a ∈ l := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    cases l with
    | nil =>
      simp at h
      simp [h]
    | cons c l =>
      rw [List.getLast?_cons_cons] at h
      exact List.mem_cons_of_mem b (ih h)

/-- The vertices used by the first `j` paths in the construction of a mixed fan. -/
noncomputable def accF (Pf : Finset V → ℕ → List V) : ℕ → Finset V
  | 0 => ∅
  | j + 1 => accF Pf j ∪ (Pf (accF Pf j) j).toFinset

lemma accF_succ (Pf : Finset V → ℕ → List V) (j : ℕ) :
    accF Pf (j + 1) = accF Pf j ∪ (Pf (accF Pf j) j).toFinset := rfl

lemma accF_mono (Pf : Finset V → ℕ → List V) (i d : ℕ) : accF Pf i ⊆ accF Pf (i + d) := by
  induction d with
  | zero => exact Finset.Subset.refl _
  | succ d ih =>
    show accF Pf i ⊆ accF Pf (i + d + 1)
    rw [accF_succ]
    exact ih.trans Finset.subset_union_left

/-- Lemma 3.2 (parity cut criterion). -/
lemma parityDominates_iff_cut (v : V) (R : ℕ → V) (hR : IsRay E R) :
    ParityDominates E v R ↔
      ∀ F : Finset V, v ∉ F → ∀ m : ℕ,
        ∃ (P P' : List V) (k k' : ℕ),
          IsPathToRay E F v R P k ∧ IsPathToRay E F v R P' k' ∧ m ≤ k ∧ m ≤ k' ∧
          (P.length + k) % 2 ≠ (P'.length + k') % 2 := by
  constructor
  · -- a finite set meets only finitely many paths of a fan
    rintro ⟨P, k, ⟨hP, hdisj⟩, hev, hod⟩ F hvF m
    obtain ⟨F', hF'⟩ : ∃ F' : Finset V, F' = F ∪ (Finset.range m).image R := ⟨_, rfl⟩
    have hB : {n | ∃ x ∈ F', x ∈ P n}.Finite := by
      have hsub : {n | ∃ x ∈ F', x ∈ P n} ⊆ ⋃ x ∈ (↑F' : Set V), {n | x ∈ P n} := by
        rintro n ⟨x, hx, hxn⟩
        exact mem_biUnion (Finset.mem_coe.mpr hx) hxn
      refine (Set.Finite.biUnion F'.finite_toSet (fun x _ => ?_)).subset hsub
      refine Set.Subsingleton.finite ?_
      intro n1 hn1 n2 hn2
      by_contra hne
      exact hdisj n1 n2 hne hn1 hn2
    have good : ∀ n, n ∉ {n | ∃ x ∈ F', x ∈ P n} →
        IsPathToRay E F v R (P n) (k n) ∧ m ≤ k n := by
      intro n hn
      obtain ⟨h1, h2, h3, h4⟩ := hP n
      refine ⟨⟨h1, h2, h3, h4, fun x hx hxF => hn ⟨x, ?_, hx⟩⟩, ?_⟩
      · rw [hF']
        exact Finset.mem_union_left _ hxF
      · by_contra hlt
        apply hn
        refine ⟨R (k n), ?_, mem_of_getLast h4⟩
        rw [hF']
        exact Finset.mem_union_right _
          (Finset.mem_image_of_mem R (Finset.mem_range.mpr (by omega)))
    obtain ⟨n1, hn1ev, hn1B⟩ := (hev.sdiff hB).nonempty
    obtain ⟨n2, hn2od, hn2B⟩ := (hod.sdiff hB).nonempty
    refine ⟨P n1, P n2, k n1, k n2, (good n1 hn1B).1, (good n2 hn2B).1,
      (good n1 hn1B).2, (good n2 hn2B).2, ?_⟩
    have e1 : Even ((P n1).length + k n1) := hn1ev
    have o2 : Odd ((P n2).length + k n2) := hn2od
    have e1' := Nat.even_iff.mp e1
    have o2' := Nat.odd_iff.mp o2
    omega
  · -- build the fan path by path, the `j`-th path avoiding the earlier ones
    -- and having the type of `j`
    intro h
    have h' : ∀ (F : Finset V) (b : ℕ), ∃ (P : List V) (k : ℕ),
        v ∉ F → IsPathToRay E F v R P k ∧ (P.length + k) % 2 = b % 2 := by
      intro F b
      by_cases hvF : v ∉ F
      · obtain ⟨P, P', k, k', hP, hP', -, -, hne⟩ := h F hvF 0
        by_cases hb : (P.length + k) % 2 = b % 2
        · exact ⟨P, k, fun _ => ⟨hP, hb⟩⟩
        · exact ⟨P', k', fun _ => ⟨hP', by omega⟩⟩
      · exact ⟨[], 0, fun h => absurd h hvF⟩
    choose Pf kf hPf using h'
    have hvacc : ∀ j, v ∉ accF Pf j := by
      intro j
      induction j with
      | zero => simp [accF]
      | succ j ih =>
        have hj := (hPf (accF Pf j) j ih).1
        intro hmem
        rw [accF_succ, Finset.mem_union] at hmem
        rcases hmem with hm | hm
        · exact ih hm
        · exact (List.nodup_cons.mp hj.2.2.1).1 (List.mem_toFinset.mp hm)
    have hp : ∀ j, IsPathToRay E (accF Pf j) v R (Pf (accF Pf j) j) (kf (accF Pf j) j) ∧
        ((Pf (accF Pf j) j).length + kf (accF Pf j) j) % 2 = j % 2 :=
      fun j => hPf (accF Pf j) j (hvacc j)
    have hdisj : ∀ i j, i < j → List.Disjoint (Pf (accF Pf i) i) (Pf (accF Pf j) j) := by
      intro i j hij x hxi hxj
      have h1 : x ∈ accF Pf (i + 1) := by
        rw [accF_succ]
        exact Finset.mem_union_right _ (List.mem_toFinset.mpr hxi)
      have h2 : x ∈ accF Pf j := by
        have h3 := accF_mono Pf (i + 1) (j - (i + 1)) h1
        rwa [show i + 1 + (j - (i + 1)) = j by omega] at h3
      exact (hp j).1.2.2.2.2 x hxj h2
    refine ⟨fun j => Pf (accF Pf j) j, fun j => kf (accF Pf j) j,
      ⟨fun n => ?_, fun m n hmn => ?_⟩, ?_, ?_⟩
    · obtain ⟨⟨h1, h2, h3, h4, -⟩, -⟩ := hp n
      exact ⟨h1, h2, h3, h4⟩
    · rcases Nat.lt_or_gt_of_ne hmn with hlt | hlt
      · exact hdisj m n hlt
      · exact fun x hx1 hx2 => hdisj n m hlt hx2 hx1
    · apply Set.infinite_of_not_bddAbove
      rintro ⟨b, hb⟩
      have hmem : 2 * b + 2 ∈
          {n : ℕ | Even ((Pf (accF Pf n) n).length + kf (accF Pf n) n)} := by
        have hpar := (hp (2 * b + 2)).2
        exact Nat.even_iff.mpr (by omega)
      have hle := hb hmem
      omega
    · apply Set.infinite_of_not_bddAbove
      rintro ⟨b, hb⟩
      have hmem : 2 * b + 1 ∈
          {n : ℕ | Odd ((Pf (accF Pf n) n).length + kf (accF Pf n) n)} := by
        have hpar := (hp (2 * b + 1)).2
        exact Nat.odd_iff.mpr (by omega)
      have hle := hb hmem
      omega

/-- An injective sequence eventually avoids any finite set. -/
lemma exists_tail_avoid {R : ℕ → V} (hR : Function.Injective R) (F : Finset V) :
    ∃ m, ∀ n, m ≤ n → R n ∉ F := by
  refine ⟨(F.preimage R (fun _ _ _ _ h => hR h)).sup id + 1, fun n hn hRn => ?_⟩
  have h1 : n ∈ F.preimage R (fun _ _ _ _ h => hR h) := Finset.mem_preimage.mpr hRn
  have h2 : n ≤ (F.preimage R (fun _ _ _ _ h => hR h)).sup id :=
    Finset.le_sup (f := id) h1
  omega

/-- A tail of a ray is a ray. -/
lemma isRay_tail {R : ℕ → V} (hR : IsRay E R) (m : ℕ) : IsRay E (fun n => R (m + n)) :=
  ⟨fun a b h => by have := hR.1 h; omega, fun n => hR.2 (m + n)⟩

/-- Lemma 3.5(3), reflexivity. -/
lemma feeds_refl {R : ℕ → V} (hR : IsRay E R) : Feeds E R R := by
  intro F
  obtain ⟨m, hm⟩ := exists_tail_avoid hR.1 F
  exact ⟨m, m, hm m le_rfl, ReflTransGen.refl⟩

lemma reachAvoiding_mono {F F' : Finset V} {u w : V} (hFF' : F ⊆ F')
    (h : ReachAvoiding E F' u w) : ReachAvoiding E F u w := by
  refine ⟨fun hu => h.1 (hFF' hu), ?_⟩
  obtain ⟨-, h2⟩ := h
  induction h2 with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih =>
    refine ReflTransGen.tail ih ?_
    exact ⟨hbc.1, fun hb => hbc.2 (hFF' hb)⟩

lemma reachAvoiding_trans {F : Finset V} {u v w : V}
    (h1 : ReachAvoiding E F u v) (h2 : ReachAvoiding E F v w) : ReachAvoiding E F u w :=
  ⟨h1.1, h1.2.trans h2.2⟩

/-- The last vertex of a walk in `G − F` is not in `F`. -/
lemma reachAvoiding_end {F : Finset V} {u w : V} (h : ReachAvoiding E F u w) : w ∉ F := by
  obtain ⟨hu, h⟩ := h
  induction h with
  | refl => exact hu
  | tail _ hbc _ => exact hbc.2

/-- A segment of a ray avoiding `F` is a walk in `G − F`. -/
lemma ray_segment {R : ℕ → V} (hR : IsRay E R) (F : Finset V) (i d : ℕ)
    (h : ∀ k, i ≤ k → k ≤ i + d → R k ∉ F) : ReachAvoiding E F (R i) (R (i + d)) := by
  induction d with
  | zero => exact ⟨h i le_rfl (by omega), ReflTransGen.refl⟩
  | succ d ih =>
    obtain ⟨hi, hrt⟩ := ih (fun k hk1 hk2 => h k hk1 (by omega))
    refine ⟨hi, ReflTransGen.tail hrt ?_⟩
    exact ⟨hR.2 (i + d), h (i + d + 1) (by omega) (by omega)⟩

/-- Lemma 3.5(1): feeding connects any two tails, avoiding any finite set. -/
lemma feeds_tails {R R' : ℕ → V} (h : Feeds E R R') (F : Finset V) (a b : ℕ) :
    ∃ m n, a ≤ m ∧ b ≤ n ∧ ReachAvoiding E F (R m) (R' n) := by
  obtain ⟨m, n, hmn⟩ := h (F ∪ (Finset.range a).image R ∪ (Finset.range b).image R')
  refine ⟨m, n, ?_, ?_, reachAvoiding_mono E ?_ hmn⟩
  · by_contra hlt
    exact hmn.1 (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem R (Finset.mem_range.mpr (by omega)))))
  · by_contra hlt
    exact reachAvoiding_end E hmn (Finset.mem_union_right _
      (Finset.mem_image_of_mem R' (Finset.mem_range.mpr (by omega))))
  · exact Finset.subset_union_left.trans Finset.subset_union_left

/-- Lemma 3.5(3), transitivity: go from `R` to `R'` beyond the part of `R'` meeting
    `F`, along `R'`, and from a later vertex of `R'` to `R''`. -/
lemma feeds_trans {R R' R'' : ℕ → V} (hR' : IsRay E R')
    (h1 : Feeds E R R') (h2 : Feeds E R' R'') : Feeds E R R'' := by
  intro F
  obtain ⟨m0, hm0⟩ := exists_tail_avoid hR'.1 F
  -- reach `R'` at some `R' n` with `n ≥ m0`
  obtain ⟨m, n, hmn⟩ := h1 (F ∪ (Finset.range m0).image R')
  have hn0 : m0 ≤ n := by
    by_contra hlt
    exact reachAvoiding_end E hmn (Finset.mem_union_right _
      (Finset.mem_image_of_mem R' (Finset.mem_range.mpr (by omega))))
  -- leave `R'` at some `R' m'` with `m' > n`
  obtain ⟨m', n', hmn'⟩ := h2 (F ∪ (Finset.range (n + 1)).image R')
  have hm'n : n < m' := by
    by_contra hle
    exact hmn'.1 (Finset.mem_union_right _
      (Finset.mem_image_of_mem R' (Finset.mem_range.mpr (by omega))))
  refine ⟨m, n', ?_⟩
  have hA : ReachAvoiding E F (R m) (R' n) := reachAvoiding_mono E Finset.subset_union_left hmn
  have hB : ReachAvoiding E F (R' n) (R' (n + (m' - n))) :=
    ray_segment E hR' F n (m' - n) (fun k hk1 hk2 => hm0 k (by omega))
  rw [show n + (m' - n) = m' by omega] at hB
  have hC : ReachAvoiding E F (R' m') (R'' n') :=
    reachAvoiding_mono E Finset.subset_union_left hmn'
  exact reachAvoiding_trans E (reachAvoiding_trans E hA hB) hC

/-- Lemma 3.5(3): a ray and each of its tails belong to the same end. -/
lemma tail_mem_endOf {R : ℕ → V} (hR : IsRay E R) (m : ℕ) :
    (fun n => R (m + n)) ∈ endOf E R := by
  refine ⟨isRay_tail E hR m, ?_, ?_⟩
  · intro F
    obtain ⟨k, hk⟩ := exists_tail_avoid hR.1 F
    exact ⟨m + k, k, hk (m + k) (by omega), ReflTransGen.refl⟩
  · intro F
    obtain ⟨k, hk⟩ := exists_tail_avoid hR.1 F
    exact ⟨k, m + k, hk (m + k) (by omega), ReflTransGen.refl⟩

/-! ## §4. Finite-port regions and the cover lemma -/

/-- Lemma 4.2(1). -/
lemma finitePort_union {U U' : Set V} (h : FinitePort E U) (h' : FinitePort E U') :
    FinitePort E (U ∪ U') := by
  refine (h.union h').subset ?_
  rintro w ⟨hw, u, hu, huw⟩
  rcases hu with hu | hu
  · exact Or.inl ⟨fun hwU => hw (Or.inl hwU), u, hu, huw⟩
  · exact Or.inr ⟨fun hwU => hw (Or.inr hwU), u, hu, huw⟩

/-- `V(G)` is a finite-port region (without ports). -/
lemma finitePort_univ : FinitePort E (univ : Set V) := by
  refine Set.finite_empty.subset ?_
  rintro w ⟨hw, -⟩
  exact (hw (mem_univ w)).elim

/-- Vertices reachable from `v ∈ Z` inside `G[Z]` lie in `Z`. -/
lemma reachIn_subset {Z : Set V} {v : V} (hv : v ∈ Z) : reachIn E Z v ⊆ Z := by
  intro w hw
  have hw' : ReflTransGen (restrict E Z) v w := hw
  clear hw
  induction hw' with
  | refl => exact hv
  | tail _ hbc _ => exact hbc.2.2

/-- Lemma 4.2(3): cones are finite-port regions (with ports in `∂Z ∪ F`). -/
lemma cone_finitePort {Z : Set V} (hZ : FinitePort E Z) (F : Finset V) {v : V}
    (hv : v ∈ Z) (hvF : v ∉ F) :
    FinitePort E (reachIn E (Z \ ↑F) v) := by
  refine (hZ.union F.finite_toSet).subset ?_
  rintro w ⟨hw, u, hu, huw⟩
  have hvZF : v ∈ Z \ ↑F := ⟨hv, hvF⟩
  have huZ : u ∈ Z \ ↑F := reachIn_subset E hvZF hu
  by_cases hwZ : w ∈ Z
  · refine Or.inr ?_
    by_contra hwF
    have hu' : ReflTransGen (restrict E (Z \ ↑F)) v u := hu
    have hvw : ReflTransGen (restrict E (Z \ ↑F)) v w := by
      refine ReflTransGen.tail hu' ?_
      exact ⟨huw, huZ, hwZ, hwF⟩
    exact hw hvw
  · exact Or.inl ⟨hwZ, u, huZ.1, huw⟩

/-! ### Helpers for assignments -/

lemma glue_mem {U : Set V} {α β : V → Bool} {v : V} (h : v ∈ U) : glue U α β v = α v := by
  simp [glue, h]

lemma glue_not_mem {U : Set V} {α β : V → Bool} {v : V} (h : v ∉ U) :
    glue U α β v = β v := by
  simp [glue, h]

lemma allFalse_true {Y : Set V} {a : V → Bool} :
    allFalse Y a = true ↔ ∀ w ∈ Y, a w = false := by
  simp [allFalse]

lemma allFalse_false {Y : Set V} {a : V → Bool} :
    allFalse Y a = false ↔ ¬ ∀ w ∈ Y, a w = false := by
  simp [allFalse]

lemma allFalse_congr {Y : Set V} {a a' : V → Bool} (h : ∀ w ∈ Y, a w = a' w) :
    allFalse Y a = allFalse Y a' := by
  have hiff : (∀ w ∈ Y, a w = false) ↔ (∀ w ∈ Y, a' w = false) :=
    ⟨fun h' w hw => by rw [← h w hw]; exact h' w hw,
     fun h' w hw => by rw [h w hw]; exact h' w hw⟩
  rw [Bool.eq_iff_iff, allFalse_true, allFalse_true]
  exact hiff

/-- Lemma 4.5 (sign rule). -/
lemma sign_rule (c : V → Bool) (hc : IsCompColouring E c) (s v : V) (hv : v ∈ comp E s)
    (Y : Set V) (hY : ∀ w ∈ Y, E v w) (a a' : V → Bool)
    (h : SignLE c (comp E s) Y a a') :
    leAt c v (allFalse Y a) (allFalse Y a') := by
  -- successors of `v` inside its component have the other colour
  have hsame : ∀ w ∈ Y, w ∈ comp E s → c w ≠ c v := by
    intro w hw hwS
    have hwv : ReflTransGen E w v := hwS.2.trans hv.1
    exact (hc v w (hY w hw) hwv).symm
  constructor
  · intro hcv hA
    rw [allFalse_true] at hA ⊢
    intro w hw
    by_cases hwS : w ∈ comp E s
    · have hcw : c w = true := by
        have hne := hsame w hw hwS
        rw [hcv] at hne
        simpa using hne
      exact ((h w hw).1 hwS).2 hcw (hA w hw)
    · rw [← (h w hw).2 hwS]
      exact hA w hw
  · intro hcv hA
    rw [allFalse_false] at hA ⊢
    intro hall
    apply hA
    intro w hw
    by_cases hwS : w ∈ comp E s
    · have hcw : c w = false := by
        have hne := hsame w hw hwS
        rw [hcv] at hne
        simpa using hne
      have himp := ((h w hw).1 hwS).1 hcw
      cases haw : a w
      · rfl
      · exact absurd (himp haw) (by rw [hall w hw]; decide)
    · rw [(h w hw).2 hwS]
      exact hall w hw

/-! ### Lemma 4.6: layered solving

  The solution is built layer by layer: by induction on `n`, a solution `ω` is
  constructed on the vertices `w ∈ W` with `|X(w)| < n`.  The vertices with
  `|X(w)| = n` fall into layers `{w : X(w) = Φ}` with `|Φ| = n`; their successors
  lie in the same layer or have `|X(z)| < n`.  In a layer, the marked part (the
  vertices reached from `Φ`, i.e. the trace of the marked component) is solved by
  the canonical kernel `κ`, and the rest by a chosen kernel. -/

/-- `X(w)`: the vertices of `X` that `w` reaches. -/
noncomputable def Xr (X : Finset V) (w : V) : Finset V := X.filter (fun x => ReflTransGen E w x)

lemma mem_Xr {X : Finset V} {w x : V} : x ∈ Xr E X w ↔ x ∈ X ∧ ReflTransGen E w x :=
  Finset.mem_filter

lemma Xr_succ {X : Finset V} {w z : V} (h : E w z) : Xr E X z ⊆ Xr E X w := by
  intro x hx
  rw [mem_Xr] at hx ⊢
  exact ⟨hx.1, ReflTransGen.head h hx.2⟩

/-- A chosen kernel of `G[Y]` (one exists when `Y ⊆ W` and `G[W]` is kernel-perfect). -/
noncomputable def chooseKer (W Y : Set V) : Set V :=
  Classical.epsilon (fun K : Set V => Y ⊆ W → IsKernelOf E Y K)

lemma chooseKer_spec {W Y : Set V} (hW : KernelPerfectOn E W) (hY : Y ⊆ W) :
    IsKernelOf E Y (chooseKer E W Y) := by
  have hex : ∃ K : Set V, Y ⊆ W → IsKernelOf E Y K := by
    obtain ⟨K, hK⟩ := hW Y hY
    exact ⟨K, fun _ => hK⟩
  exact Classical.epsilon_spec hex hY

/-- The veto at `u`, given the solution `ω` on the vertices `z` with `|X(z)| < n`. -/
def vetoL (W : Set V) (X : Finset V) (g : V → (V → Bool) → Bool)
    (ω : (V → Bool) → V → Bool) (n : ℕ) (γ : V → Bool) (u : V) : Prop :=
  g u γ = false ∨ ∃ z ∈ W, E u z ∧ (Xr E X z).card < n ∧ ω γ z = true

/-- The layer of `Φ`. -/
def layerSet (W : Set V) (X Φ : Finset V) : Set V := {w | w ∈ W ∧ Xr E X w = Φ}

/-- The marked part of the layer: the vertices reached from `Φ`. -/
def markedSet (W : Set V) (X Φ : Finset V) : Set V :=
  {w | w ∈ layerSet E W X Φ ∧ ∃ x ∈ Φ, ReflTransGen E x w}

/-- The non-vetoed vertices of the marked part. -/
def QSet (W : Set V) (X : Finset V) (g : V → (V → Bool) → Bool) (ω : (V → Bool) → V → Bool)
    (n : ℕ) (Φ : Finset V) (γ : V → Bool) : Set V :=
  {w | w ∈ markedSet E W X Φ ∧ ¬ vetoL E W X g ω n γ w}

/-- The solution on the marked part: the canonical kernel. -/
def K1Set (c : V → Bool) (W : Set V) (X : Finset V) (g : V → (V → Bool) → Bool)
    (ω : (V → Bool) → V → Bool) (n : ℕ) (Φ : Finset V) (γ : V → Bool) : Set V :=
  kappa E c (QSet E W X g ω n Φ γ)

/-- The rest of the layer, without the vetoed vertices and those pointing into `K1`. -/
def RSet (c : V → Bool) (W : Set V) (X : Finset V) (g : V → (V → Bool) → Bool)
    (ω : (V → Bool) → V → Bool) (n : ℕ) (Φ : Finset V) (γ : V → Bool) : Set V :=
  {w | w ∈ layerSet E W X Φ ∧ w ∉ markedSet E W X Φ ∧ ¬ vetoL E W X g ω n γ w ∧
    ∀ z ∈ K1Set E c W X g ω n Φ γ, ¬ E w z}

/-- The solution on the rest of the layer: a chosen kernel. -/
noncomputable def K2Set (c : V → Bool) (W : Set V) (X : Finset V)
    (g : V → (V → Bool) → Bool) (ω : (V → Bool) → V → Bool) (n : ℕ) (Φ : Finset V)
    (γ : V → Bool) : Set V :=
  chooseKer E W (RSet E c W X g ω n Φ γ)

/-- The value on the layer of `w`. -/
noncomputable def LS (c : V → Bool) (W : Set V) (X : Finset V) (g : V → (V → Bool) → Bool)
    (ω : (V → Bool) → V → Bool) (n : ℕ) (γ : V → Bool) (w : V) : Bool :=
  decide (w ∈ K1Set E c W X g ω n (Xr E X w) γ ∨ w ∈ K2Set E c W X g ω n (Xr E X w) γ)

/-- The solution extended from `|X(w)| < n` to `|X(w)| ≤ n`. -/
noncomputable def omegaStep (c : V → Bool) (W : Set V) (X : Finset V)
    (g : V → (V → Bool) → Bool) (ω : (V → Bool) → V → Bool) (n : ℕ) :
    (V → Bool) → V → Bool :=
  fun γ w => if (Xr E X w).card < n then ω γ w else LS E c W X g ω n γ w

section LayeredSolving

variable {c : V → Bool} {W : Set V} {X : Finset V} {g : V → (V → Bool) → Bool}
  {ω : (V → Bool) → V → Bool} {n : ℕ}

lemma omegaStep_lt {γ : V → Bool} {w : V} (h : (Xr E X w).card < n) :
    omegaStep E c W X g ω n γ w = ω γ w := by
  show (if (Xr E X w).card < n then ω γ w else LS E c W X g ω n γ w) = ω γ w
  exact ite_eq_left h

lemma omegaStep_ge {γ : V → Bool} {w : V} (h : ¬ (Xr E X w).card < n) :
    omegaStep E c W X g ω n γ w = LS E c W X g ω n γ w := by
  show (if (Xr E X w).card < n then ω γ w else LS E c W X g ω n γ w) = LS E c W X g ω n γ w
  exact ite_eq_right h

lemma leAt_refl (v : V) (a : Bool) : leAt c v a a := ⟨fun _ h => h, fun _ h => h⟩

/-- The marked part of a layer lies in one strong component, so `c` 2-colours it. -/
lemma marked_bip (hc : IsCompColouring E c) (Φ : Finset V) :
    IsBipartiteOn E c (markedSet E W X Φ) := by
  intro u hu v hv huv
  apply hc u v huv
  obtain ⟨⟨-, -⟩, x, hx, hxu⟩ := hu
  obtain ⟨⟨-, hvΦ⟩, -⟩ := hv
  have hx' : x ∈ Xr E X v := by rw [hvΦ]; exact hx
  exact ((mem_Xr E).mp hx').2.trans hxu

lemma marked_closed {Φ : Finset V} {u z : V} (hu : u ∈ markedSet E W X Φ) (hzW : z ∈ W)
    (hzΦ : Xr E X z = Φ) (huz : E u z) : z ∈ markedSet E W X Φ := by
  obtain ⟨-, x, hx, hxu⟩ := hu
  exact ⟨⟨hzW, hzΦ⟩, x, hx, hxu.tail huz⟩

lemma K1_kernel (hc : IsCompColouring E c) (Φ : Finset V) (γ : V → Bool) :
    IsKernelOf E (QSet E W X g ω n Φ γ) (K1Set E c W X g ω n Φ γ) :=
  kappa_isKernel E c _ (fun u hu v hv huv => marked_bip E hc Φ u hu.1 v hv.1 huv)

lemma K2_kernel (hW : KernelPerfectOn E W) (Φ : Finset V) (γ : V → Bool) :
    IsKernelOf E (RSet E c W X g ω n Φ γ) (K2Set E c W X g ω n Φ γ) :=
  chooseKer_spec E hW (fun u hu => hu.1.1)

lemma LS_iff {γ : V → Bool} {Φ : Finset V} {u : V} (hu : Xr E X u = Φ) :
    LS E c W X g ω n γ u = true ↔
      (u ∈ K1Set E c W X g ω n Φ γ ∨ u ∈ K2Set E c W X g ω n Φ γ) := by
  unfold LS
  rw [hu]
  exact ⟨of_decide_eq_true, decide_eq_true⟩

/-- Property (1) of Lemma 4.6 on a layer with `|Φ| = n`. -/
lemma layer_eq (hc : IsCompColouring E c) (hW : KernelPerfectOn E W) {Φ : Finset V}
    (hΦ : Φ.card = n) {γ : V → Bool} {w : V} (hw : w ∈ layerSet E W X Φ) :
    LS E c W X g ω n γ w = true ↔
      (g w γ = true ∧ ∀ z ∈ W, E w z → omegaStep E c W X g ω n γ z = false) := by
  obtain ⟨hwW, hwΦ⟩ := hw
  have hK1 := K1_kernel E (W := W) (X := X) (g := g) (ω := ω) (n := n) hc Φ γ
  have hK2 := K2_kernel E (c := c) (X := X) (g := g) (ω := ω) (n := n) hW Φ γ
  have hsuccΦ : ∀ z ∈ W, E w z → (Xr E X z).card < n ∨ Xr E X z = Φ := by
    intro z hz hwz
    have hsub : Xr E X z ⊆ Φ := by rw [← hwΦ]; exact Xr_succ E hwz
    by_cases hlt : (Xr E X z).card < n
    · exact Or.inl hlt
    · exact Or.inr (Finset.eq_of_subset_of_card_le hsub (by omega))
  rw [LS_iff E hwΦ]
  by_cases hv : vetoL E W X g ω n γ w
  · -- vetoed: both sides are false
    have hnK1 : w ∉ K1Set E c W X g ω n Φ γ := fun h => (hK1.1 h).2 hv
    have hnK2 : w ∉ K2Set E c W X g ω n Φ γ := fun h => (hK2.1 h).2.2.1 hv
    constructor
    · rintro (h | h)
      · exact absurd h hnK1
      · exact absurd h hnK2
    · rintro ⟨hg', hall⟩
      rcases hv with hv | ⟨z, hz, hwz, hzlt, hzt⟩
      · rw [hv] at hg'
        exact absurd hg' (by decide)
      · have hz' := hall z hz hwz
        rw [omegaStep_lt E hzlt] at hz'
        rw [hz'] at hzt
        exact absurd hzt (by decide)
  · have hg' : g w γ = true := by
      by_contra hgf
      exact hv (Or.inl (Bool.eq_false_iff.mpr hgf))
    have hlow : ∀ z ∈ W, E w z → (Xr E X z).card < n → ω γ z = false := by
      intro z hz hwz hlt
      by_contra h
      exact hv (Or.inr ⟨z, hz, hwz, hlt, by simpa using h⟩)
    by_cases hwM : w ∈ markedSet E W X Φ
    · -- marked: the canonical kernel
      have hnK2 : w ∉ K2Set E c W X g ω n Φ γ := fun h => (hK2.1 h).2.1 hwM
      have hwQ : w ∈ QSet E W X g ω n Φ γ := ⟨hwM, hv⟩
      constructor
      · rintro (hK | hK)
        · refine ⟨hg', fun z hz hwz => ?_⟩
          rcases hsuccΦ z hz hwz with hlt | heq
          · rw [omegaStep_lt E hlt]
            exact hlow z hz hwz hlt
          · have hzM := marked_closed E hwM hz heq hwz
            have hznlt : ¬ (Xr E X z).card < n := by rw [heq]; omega
            rw [omegaStep_ge E hznlt, Bool.eq_false_iff]
            intro hzt
            rcases (LS_iff E heq).mp hzt with hz1 | hz2
            · exact hK1.2.1 w hK z hz1 hwz
            · exact (hK2.1 hz2).2.1 hzM
        · exact absurd hK hnK2
      · rintro ⟨-, hall⟩
        left
        by_contra hnK
        obtain ⟨z, hzK, hwz⟩ := hK1.2.2 w hwQ hnK
        have hzQ := hK1.1 hzK
        have hznlt : ¬ (Xr E X z).card < n := by rw [hzQ.1.1.2]; omega
        have hz' := hall z hzQ.1.1.1 hwz
        rw [omegaStep_ge E hznlt, Bool.eq_false_iff] at hz'
        exact hz' ((LS_iff E hzQ.1.1.2).mpr (Or.inl hzK))
    · -- not marked
      have hnK1 : w ∉ K1Set E c W X g ω n Φ γ := fun h => hwM (hK1.1 h).1
      by_cases hK1succ : ∃ z ∈ K1Set E c W X g ω n Φ γ, E w z
      · obtain ⟨z, hzK, hwz⟩ := hK1succ
        have hnK2 : w ∉ K2Set E c W X g ω n Φ γ := fun h => (hK2.1 h).2.2.2 z hzK hwz
        constructor
        · rintro (h | h)
          · exact absurd h hnK1
          · exact absurd h hnK2
        · rintro ⟨-, hall⟩
          have hzQ := hK1.1 hzK
          have hznlt : ¬ (Xr E X z).card < n := by rw [hzQ.1.1.2]; omega
          have hz' := hall z hzQ.1.1.1 hwz
          rw [omegaStep_ge E hznlt, Bool.eq_false_iff] at hz'
          exact absurd ((LS_iff E hzQ.1.1.2).mpr (Or.inl hzK)) hz'
      · push_neg at hK1succ
        have hwR : w ∈ RSet E c W X g ω n Φ γ := ⟨⟨hwW, hwΦ⟩, hwM, hv, hK1succ⟩
        constructor
        · rintro (h | hK)
          · exact absurd h hnK1
          · refine ⟨hg', fun z hz hwz => ?_⟩
            rcases hsuccΦ z hz hwz with hlt | heq
            · rw [omegaStep_lt E hlt]
              exact hlow z hz hwz hlt
            · have hznlt : ¬ (Xr E X z).card < n := by rw [heq]; omega
              rw [omegaStep_ge E hznlt, Bool.eq_false_iff]
              intro hzt
              rcases (LS_iff E heq).mp hzt with hz1 | hz2
              · exact hK1succ z hz1 hwz
              · exact hK2.2.1 w hK z hz2 hwz
        · rintro ⟨-, hall⟩
          right
          by_contra hnK
          obtain ⟨z, hzK, hwz⟩ := hK2.2.2 w hwR hnK
          have hzR := hK2.1 hzK
          have hznlt : ¬ (Xr E X z).card < n := by rw [hzR.1.2]; omega
          have hz' := hall z hzR.1.1 hwz
          rw [omegaStep_ge E hznlt, Bool.eq_false_iff] at hz'
          exact hz' ((LS_iff E hzR.1.2).mpr (Or.inr hzK))

/-- Property (2) of Lemma 4.6 on a layer: everything depends only on `γ | X(w)`. -/
lemma layer_causal
    (h2 : ∀ γ γ', ∀ w ∈ W, (Xr E X w).card < n → (∀ x ∈ X, ReflTransGen E w x → γ x = γ' x) →
      ω γ w = ω γ' w)
    (hg : ∀ w ∈ W, ∀ γ γ', (∀ x ∈ X, ReflTransGen E w x → γ x = γ' x) → g w γ = g w γ')
    {γ γ' : V → Bool} {w : V} (hag : ∀ x ∈ X, ReflTransGen E w x → γ x = γ' x) :
    LS E c W X g ω n γ w = LS E c W X g ω n γ' w := by
  have hveto : ∀ u ∈ layerSet E W X (Xr E X w),
      (vetoL E W X g ω n γ u ↔ vetoL E W X g ω n γ' u) := by
    intro u hu
    have hagu : ∀ x ∈ X, ReflTransGen E u x → γ x = γ' x := by
      intro x hx hux
      have hxw : x ∈ Xr E X w := by
        rw [← hu.2]
        exact (mem_Xr E).mpr ⟨hx, hux⟩
      exact hag x hx ((mem_Xr E).mp hxw).2
    have hgu : g u γ = g u γ' := hg u hu.1 γ γ' hagu
    have hlow : ∀ z ∈ W, E u z → (Xr E X z).card < n → ω γ z = ω γ' z :=
      fun z hz huz hlt => h2 γ γ' z hz hlt
        (fun x hx hzx => hagu x hx (ReflTransGen.head huz hzx))
    unfold vetoL
    rw [hgu]
    constructor
    · rintro (h | ⟨z, hz, huz, hlt, hzt⟩)
      · exact Or.inl h
      · exact Or.inr ⟨z, hz, huz, hlt, by rw [← hlow z hz huz hlt]; exact hzt⟩
    · rintro (h | ⟨z, hz, huz, hlt, hzt⟩)
      · exact Or.inl h
      · exact Or.inr ⟨z, hz, huz, hlt, by rw [hlow z hz huz hlt]; exact hzt⟩
  have hQ : QSet E W X g ω n (Xr E X w) γ = QSet E W X g ω n (Xr E X w) γ' := by
    ext u
    constructor
    · rintro ⟨hM, hv⟩
      exact ⟨hM, fun h => hv ((hveto u hM.1).mpr h)⟩
    · rintro ⟨hM, hv⟩
      exact ⟨hM, fun h => hv ((hveto u hM.1).mp h)⟩
  have hK1 : K1Set E c W X g ω n (Xr E X w) γ = K1Set E c W X g ω n (Xr E X w) γ' := by
    unfold K1Set
    rw [hQ]
  have hR : RSet E c W X g ω n (Xr E X w) γ = RSet E c W X g ω n (Xr E X w) γ' := by
    ext u
    unfold RSet
    rw [hK1]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, fun h => h3 ((hveto u h1).mpr h), h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, fun h => h3 ((hveto u h1).mp h), h4⟩
  have hK2 : K2Set E c W X g ω n (Xr E X w) γ = K2Set E c W X g ω n (Xr E X w) γ' := by
    unfold K2Set
    rw [hR]
  unfold LS
  rw [hK1, hK2]

/-- Property (3) of Lemma 4.6 on a layer with `|X(w)| = n`. -/
lemma layer_mono (hc : IsCompColouring E c) (hW : KernelPerfectOn E W)
    (h2 : ∀ γ γ', ∀ w ∈ W, (Xr E X w).card < n → (∀ x ∈ X, ReflTransGen E w x → γ x = γ' x) →
      ω γ w = ω γ' w)
    (hg : ∀ w ∈ W, ∀ γ γ', (∀ x ∈ X, ReflTransGen E w x → γ x = γ' x) → g w γ = g w γ')
    {s : V}
    (hyp : ∀ γ γ', SignLE c (comp E s) ↑X γ γ' →
      ∀ w ∈ W ∩ comp E s, leAt c w (g w γ) (g w γ'))
    {γ γ' : V → Bool} (hγ : SignLE c (comp E s) ↑X γ γ') {w : V} (hw : w ∈ W ∩ comp E s)
    (hΦ : (Xr E X w).card = n) :
    leAt c w (LS E c W X g ω n γ w) (LS E c W X g ω n γ' w) := by
  by_cases hmark : ∃ x0 ∈ X, x0 ∈ comp E s
  · obtain ⟨x0, hx0X, hx0S⟩ := hmark
    -- `w` lies in the marked part of its layer, which lies in `comp s`
    have hx0Φ : x0 ∈ Xr E X w := (mem_Xr E).mpr ⟨hx0X, hw.2.2.trans hx0S.1⟩
    have hwM : w ∈ markedSet E W X (Xr E X w) := ⟨⟨hw.1, rfl⟩, x0, hx0Φ, hx0S.2.trans hw.2.1⟩
    have hMS : ∀ u ∈ markedSet E W X (Xr E X w), u ∈ comp E s := by
      rintro u ⟨⟨-, huΦ⟩, x, hx, hxu⟩
      have hx0u : x0 ∈ Xr E X u := by rw [huΦ]; exact hx0Φ
      have hwx : ReflTransGen E w x := ((mem_Xr E).mp hx).2
      exact ⟨hx0S.1.trans ((hx0S.2.trans hw.2.1).trans (hwx.trans hxu)),
        ((mem_Xr E).mp hx0u).2.trans hx0S.2⟩
    -- the values on the lower layers do not change
    have hlowEq : ∀ u ∈ markedSet E W X (Xr E X w), ∀ z ∈ W, E u z →
        (Xr E X z).card < n → ω γ z = ω γ' z := by
      intro u huM z hz huz hlt
      apply h2 γ γ' z hz hlt
      intro x hx hzx
      have hxS : x ∉ comp E s := by
        intro hxS
        -- then `z ∈ comp s`, and `z` reaches everything `u` reaches
        have hsub : Xr E X u ⊆ Xr E X z := by
          intro y hy
          rw [mem_Xr] at hy ⊢
          exact ⟨hy.1, ((hzx.trans hxS.2).trans (hMS u huM).1).trans hy.2⟩
        rw [huM.1.2] at hsub
        have hle := Finset.card_le_card hsub
        omega
      exact (hγ x hx).2 hxS
    have hmon : ∀ u ∈ markedSet E W X (Xr E X w), leAt c u (g u γ) (g u γ') :=
      fun u huM => hyp γ γ' hγ u ⟨huM.1.1, hMS u huM⟩
    -- the sets `Q` move in the right direction
    have h0 : {x | x ∈ QSet E W X g ω n (Xr E X w) γ ∧ c x = false} ⊆
        {x | x ∈ QSet E W X g ω n (Xr E X w) γ' ∧ c x = false} := by
      rintro u ⟨⟨huM, hvu⟩, hcu⟩
      refine ⟨⟨huM, ?_⟩, hcu⟩
      intro hv'
      apply hvu
      rcases hv' with hg' | ⟨z, hz, huz, hlt, hzt⟩
      · left
        by_contra hne
        have hne' : g u γ = true := by simpa using hne
        have hgt := (hmon u huM).1 hcu hne'
        rw [hg'] at hgt
        exact absurd hgt (by decide)
      · right
        exact ⟨z, hz, huz, hlt, by rw [hlowEq u huM z hz huz hlt]; exact hzt⟩
    have h1 : {x | x ∈ QSet E W X g ω n (Xr E X w) γ' ∧ c x = true} ⊆
        {x | x ∈ QSet E W X g ω n (Xr E X w) γ ∧ c x = true} := by
      rintro u ⟨⟨huM, hvu'⟩, hcu⟩
      refine ⟨⟨huM, ?_⟩, hcu⟩
      intro hv
      apply hvu'
      rcases hv with hg' | ⟨z, hz, huz, hlt, hzt⟩
      · exact Or.inl ((hmon u huM).2 hcu hg')
      · exact Or.inr ⟨z, hz, huz, hlt, by rw [← hlowEq u huM z hz huz hlt]; exact hzt⟩
    have hbip' : IsBipartiteOn E c (QSet E W X g ω n (Xr E X w) γ') :=
      fun u hu v hv huv => marked_bip E hc (Xr E X w) u hu.1 v hv.1 huv
    obtain ⟨hk0, hk1⟩ := kappa_mono E c _ _ hbip' h0 h1
    -- on the marked part, the value is membership in `K1`
    have hval : ∀ δ, LS E c W X g ω n δ w = true ↔ w ∈ K1Set E c W X g ω n (Xr E X w) δ := by
      intro δ
      rw [LS_iff E rfl]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd hwM ((K2_kernel E hW (Xr E X w) δ).1 h).2.1
      · exact Or.inl
    constructor
    · intro hcw hLS
      have hK := (hval γ).mp hLS
      exact (hval γ').mpr (hk0 ⟨hK, hcw⟩).1
    · intro hcw hLS
      rw [Bool.eq_false_iff]
      intro hLS'
      have hK := (hval γ').mp hLS'
      have hK' := (hk1 ⟨hK, hcw⟩).1
      rw [(hval γ).mpr hK'] at hLS
      exact absurd hLS (by decide)
  · -- `comp s` meets no vertex of `X`: then `γ = γ'` on `X`
    push_neg at hmark
    have hag : ∀ x ∈ X, ReflTransGen E w x → γ x = γ' x :=
      fun x hx _ => (hγ x hx).2 (hmark x hx)
    rw [layer_causal E h2 hg hag]
    exact leAt_refl w _

/-- Lemma 4.6, by induction over `n = |X(w)|`. -/
lemma layered_aux (hc : IsCompColouring E c) (hW : KernelPerfectOn E W)
    (hg : ∀ w ∈ W, ∀ γ γ', (∀ x ∈ X, ReflTransGen E w x → γ x = γ' x) → g w γ = g w γ') :
    ∀ n : ℕ, ∃ ω : (V → Bool) → V → Bool,
      (∀ γ, ∀ w ∈ W, (Xr E X w).card < n →
        (ω γ w = true ↔ (g w γ = true ∧ ∀ z ∈ W, E w z → ω γ z = false))) ∧
      (∀ γ γ', ∀ w ∈ W, (Xr E X w).card < n →
        (∀ x ∈ X, ReflTransGen E w x → γ x = γ' x) → ω γ w = ω γ' w) ∧
      (∀ s, (∀ γ γ', SignLE c (comp E s) ↑X γ γ' →
          ∀ w ∈ W ∩ comp E s, leAt c w (g w γ) (g w γ')) →
        ∀ γ γ', SignLE c (comp E s) ↑X γ γ' →
          ∀ w ∈ W ∩ comp E s, (Xr E X w).card < n → leAt c w (ω γ w) (ω γ' w)) := by
  intro n
  induction n with
  | zero =>
    exact ⟨fun _ _ => false, fun γ w _ h => absurd h (Nat.not_lt_zero _),
      fun γ γ' w _ h => absurd h (Nat.not_lt_zero _),
      fun s _ γ γ' _ w _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨ω, h1, h2, h3⟩ := ih
    refine ⟨omegaStep E c W X g ω n, ?_, ?_, ?_⟩
    · intro γ w hw hlt1
      by_cases hlt : (Xr E X w).card < n
      · rw [omegaStep_lt E hlt, h1 γ w hw hlt]
        have hsucc : ∀ z ∈ W, E w z → omegaStep E c W X g ω n γ z = ω γ z :=
          fun z _ hwz => omegaStep_lt E (lt_of_le_of_lt (Finset.card_le_card (Xr_succ E hwz)) hlt)
        constructor
        · rintro ⟨hg', hz⟩
          exact ⟨hg', fun z hz' hwz => by rw [hsucc z hz' hwz]; exact hz z hz' hwz⟩
        · rintro ⟨hg', hz⟩
          exact ⟨hg', fun z hz' hwz => by rw [← hsucc z hz' hwz]; exact hz z hz' hwz⟩
      · have hΦ : (Xr E X w).card = n := by omega
        rw [omegaStep_ge E hlt]
        exact layer_eq E hc hW hΦ ⟨hw, rfl⟩
    · intro γ γ' w hw hlt1 hag
      by_cases hlt : (Xr E X w).card < n
      · rw [omegaStep_lt E hlt, omegaStep_lt E hlt]
        exact h2 γ γ' w hw hlt hag
      · rw [omegaStep_ge E hlt, omegaStep_ge E hlt]
        exact layer_causal E h2 hg hag
    · intro s hyp γ γ' hγ w hw hlt1
      by_cases hlt : (Xr E X w).card < n
      · rw [omegaStep_lt E hlt, omegaStep_lt E hlt]
        exact h3 s hyp γ γ' hγ w hw hlt
      · rw [omegaStep_ge E hlt, omegaStep_ge E hlt]
        exact layer_mono E hc hW h2 hg hyp hγ hw (by omega)

end LayeredSolving

/-- Lemma 4.6 (layered solving). -/
lemma layered_solving (c : V → Bool) (hc : IsCompColouring E c)
    (W : Set V) (hW : KernelPerfectOn E W) (X : Finset V) (hXW : ∀ x ∈ X, x ∉ W)
    (g : V → (V → Bool) → Bool)
    (hg : ∀ w ∈ W, ∀ γ γ', (∀ x ∈ X, ReflTransGen E w x → γ x = γ' x) → g w γ = g w γ') :
    ∃ ω : (V → Bool) → V → Bool,
      (∀ γ, ∀ w ∈ W, ω γ w = true ↔ (g w γ = true ∧ ∀ z ∈ W, E w z → ω γ z = false)) ∧
      (∀ γ γ', ∀ w ∈ W, (∀ x ∈ X, ReflTransGen E w x → γ x = γ' x) → ω γ w = ω γ' w) ∧
      (∀ s, (∀ γ γ', SignLE c (comp E s) ↑X γ γ' →
              ∀ w ∈ W ∩ comp E s, leAt c w (g w γ) (g w γ')) →
        ∀ γ γ', SignLE c (comp E s) ↑X γ γ' →
          SignLE c (comp E s) (W ∩ comp E s) (ω γ) (ω γ')) := by
  obtain ⟨ω, h1, h2, h3⟩ := layered_aux E hc hW hg (X.card + 1)
  have hbound : ∀ w, (Xr E X w).card < X.card + 1 :=
    fun w => Nat.lt_succ_of_le (Finset.card_filter_le X _)
  refine ⟨ω, fun γ w hw => h1 γ w hw (hbound w),
    fun γ γ' w hw hag => h2 γ γ' w hw (hbound w) hag, ?_⟩
  intro s hyp γ γ' hγ v hv
  exact ⟨fun _ => h3 s hyp γ γ' hγ v hv (hbound v), fun hvS => absurd hv.2 hvS⟩

/-- Lemma 4.7: kernel-perfect finite-port regions have good solvers. -/
lemma good_solver_exists (c : V → Bool) (hc : IsCompColouring E c)
    (U : Set V) (hU : FinitePort E U) (hkp : KernelPerfectOn E U) :
    ∃ σ, IsGoodSolver E c U σ := by
  -- Lemma 4.6 with `W = U`, `X = ∂U` and `g_u(β) = 1` iff all ports among the
  -- successors of `u` are `0`.
  have hX : ∀ x, x ∈ hU.toFinset ↔ x ∈ ports E U := fun x => hU.mem_toFinset
  obtain ⟨ω, h1, h2, h3⟩ := layered_solving E c hc U hkp hU.toFinset
    (fun x hx => ((hX x).mp hx).1)
    (fun u β => allFalse {b | b ∈ ports E U ∧ E u b} β)
    (by
      intro w hw γ γ' hγ
      apply allFalse_congr
      intro b hb
      exact hγ b ((hX b).mpr hb.1) (ReflTransGen.single hb.2))
  refine ⟨ω, ?_, ?_, ?_⟩
  · -- the kernel equation
    intro β u hu
    show glue U (ω β) β u = true ↔ ∀ w, E u w → glue U (ω β) β w = false
    rw [glue_mem hu, h1 β u hu]
    constructor
    · rintro ⟨hg, hz⟩ w huw
      by_cases hwU : w ∈ U
      · rw [glue_mem hwU]
        exact hz w hwU huw
      · rw [glue_not_mem hwU]
        exact (allFalse_true.mp hg) w ⟨⟨hwU, u, hu, huw⟩, huw⟩
    · intro hall
      refine ⟨allFalse_true.mpr (fun b hb => ?_), fun z hz huz => ?_⟩
      · have hb' := hall b hb.2
        rwa [glue_not_mem hb.1.1] at hb'
      · have hz' := hall z huz
        rwa [glue_mem hz] at hz'
  · -- causality
    intro β β' u hu hagree
    exact h2 β β' u hu (fun x hx hux => hagree x ((hX x).mp hx) hux)
  · -- monotonicity, by the sign rule
    intro s β β' hββ'
    have hX' : SignLE c (comp E s) ↑hU.toFinset β β' := fun x hx => hββ' x ((hX x).mp hx)
    refine h3 s ?_ β β' hX'
    intro γ γ' hγ w hw
    exact sign_rule E c hc s w hw.2 {b | b ∈ ports E U ∧ E w b} (fun b hb => hb.2) γ γ'
      (fun b hb => hγ b ((hX b).mpr hb.1))

/-- Kernel-perfectness passes to subsets. -/
lemma kpOn_mono {A B : Set V} (h : KernelPerfectOn E B) (hAB : A ⊆ B) : KernelPerfectOn E A :=
  fun X hX => h X (hX.trans hAB)

/-! ### Lemma 4.8: adding a region

  Step 2 of the proof (the equations at `F`) is isolated in `fix_solve`: the classes
  of `F` are solved one after the other, by induction over `|F(f)|` where `F(f)` is
  the set of vertices of `F` that `f` reaches (vertices with the same `F(f)` form a
  class), taking on each class the largest fixed point in the sign order. -/

lemma leAt_trans' {c : V → Bool} {v : V} {a b d : Bool} (h1 : leAt c v a b)
    (h2 : leAt c v b d) : leAt c v a d :=
  ⟨fun hc ha => h2.1 hc (h1.1 hc ha), fun hc ha => h2.2 hc (h1.2 hc ha)⟩

lemma leAt_antisymm {c : V → Bool} {v : V} {a b : Bool} (h1 : leAt c v a b)
    (h2 : leAt c v b a) : a = b := by
  cases hcv : c v
  · cases a <;> cases b
    · rfl
    · exact absurd (h2.1 hcv rfl) (by decide)
    · exact absurd (h1.1 hcv rfl) (by decide)
    · rfl
  · cases a <;> cases b
    · rfl
    · exact absurd (h1.2 hcv rfl) (by decide)
    · exact absurd (h2.2 hcv rfl) (by decide)
    · rfl

lemma kernelEq_congr {x y : V → Bool} {v : V} (hv : x v = y v)
    (hs : ∀ w, E v w → x w = y w) : KernelEqAt E x v ↔ KernelEqAt E y v := by
  have hall : (∀ w, E v w → x w = false) ↔ (∀ w, E v w → y w = false) :=
    ⟨fun h w hw => by rw [← hs w hw]; exact h w hw,
     fun h w hw => by rw [hs w hw]; exact h w hw⟩
  unfold KernelEqAt
  rw [hv, hall]

/-! #### Largest fixed points in the sign order -/

/-- `δ` is a post-fixed point of `Ψ` on `K` in the sign order. -/
def postFix (c : V → Bool) (K : Finset V) (Ψ : (V → Bool) → V → Bool) (δ : V → Bool) : Prop :=
  ∀ g ∈ K, leAt c g (δ g) (Ψ δ g)

/-- The supremum of the post-fixed points in the sign order. -/
noncomputable def gfpF (c : V → Bool) (K : Finset V) (Ψ : (V → Bool) → V → Bool) (f : V) :
    Bool :=
  decide ((c f = false ∧ ∃ δ, postFix c K Ψ δ ∧ δ f = true) ∨
    (c f = true ∧ ∀ δ, postFix c K Ψ δ → δ f = true))

lemma gfpF_false {c : V → Bool} {K : Finset V} {Ψ : (V → Bool) → V → Bool} {f : V}
    (hcf : c f = false) : gfpF c K Ψ f = true ↔ ∃ δ, postFix c K Ψ δ ∧ δ f = true := by
  unfold gfpF
  constructor
  · intro h
    rcases of_decide_eq_true h with ⟨-, h'⟩ | ⟨hct, -⟩
    · exact h'
    · rw [hcf] at hct
      exact absurd hct (by decide)
  · intro h
    exact decide_eq_true (Or.inl ⟨hcf, h⟩)

lemma gfpF_true {c : V → Bool} {K : Finset V} {Ψ : (V → Bool) → V → Bool} {f : V}
    (hcf : c f = true) : gfpF c K Ψ f = true ↔ ∀ δ, postFix c K Ψ δ → δ f = true := by
  unfold gfpF
  constructor
  · intro h
    rcases of_decide_eq_true h with ⟨hcf', -⟩ | ⟨-, h'⟩
    · rw [hcf] at hcf'
      exact absurd hcf' (by decide)
    · exact h'
  · intro h
    exact decide_eq_true (Or.inr ⟨hcf, h⟩)

lemma gfpF_ub {c : V → Bool} {K : Finset V} {Ψ : (V → Bool) → V → Bool} {δ : V → Bool}
    (hδ : postFix c K Ψ δ) : ∀ f, leAt c f (δ f) (gfpF c K Ψ f) := by
  intro f
  constructor
  · intro hcf hδf
    exact (gfpF_false hcf).mpr ⟨δ, hδ, hδf⟩
  · intro hcf hδf
    rw [Bool.eq_false_iff]
    intro hg
    have h1 := (gfpF_true hcf).mp hg δ hδ
    rw [hδf] at h1
    exact absurd h1 (by decide)

lemma gfpF_lub {c : V → Bool} {K : Finset V} {Ψ : (V → Bool) → V → Bool} {θ : V → Bool}
    (h : ∀ δ, postFix c K Ψ δ → ∀ f ∈ K, leAt c f (δ f) (θ f)) :
    ∀ f ∈ K, leAt c f (gfpF c K Ψ f) (θ f) := by
  intro f hf
  constructor
  · intro hcf hg
    obtain ⟨δ, hδ, hδf⟩ := (gfpF_false hcf).mp hg
    exact (h δ hδ f hf).1 hcf hδf
  · intro hcf hg
    rw [Bool.eq_false_iff]
    intro hθ
    have hall : ∀ δ, postFix c K Ψ δ → δ f = true := by
      intro δ hδ
      by_contra hne
      have hf' : δ f = false := by simpa using hne
      have h1 := (h δ hδ f hf).2 hcf hf'
      rw [hθ] at h1
      exact absurd h1 (by decide)
    rw [(gfpF_true hcf).mpr hall] at hg
    exact absurd hg (by decide)

/-- Knaster–Tarski on the finite lattice `(2^K, ⊑)`. -/
lemma gfpF_spec {c : V → Bool} {K : Finset V} {Ψ : (V → Bool) → V → Bool}
    (hmono : ∀ δ δ', (∀ g ∈ K, leAt c g (δ g) (δ' g)) → ∀ g ∈ K, leAt c g (Ψ δ g) (Ψ δ' g)) :
    (∀ f ∈ K, gfpF c K Ψ f = Ψ (gfpF c K Ψ) f) ∧
    (∀ δ, postFix c K Ψ δ → ∀ f, leAt c f (δ f) (gfpF c K Ψ f)) := by
  have hpost : postFix c K Ψ (gfpF c K Ψ) := by
    apply gfpF_lub
    intro δ hδ g hg
    exact leAt_trans' (hδ g hg) (hmono δ (gfpF c K Ψ) (fun g' _ => gfpF_ub hδ g') g hg)
  have hpost2 : postFix c K Ψ (Ψ (gfpF c K Ψ)) := hmono _ _ hpost
  exact ⟨fun f hf => leAt_antisymm (hpost f hf) (gfpF_ub hpost2 f), fun δ hδ => gfpF_ub hδ⟩

lemma gfpF_congr {c : V → Bool} {K : Finset V} {Ψ Ψ' : (V → Bool) → V → Bool}
    (hP : ∀ δ, postFix c K Ψ δ ↔ postFix c K Ψ' δ) (f : V) :
    gfpF c K Ψ f = gfpF c K Ψ' f := by
  rw [Bool.eq_iff_iff]
  cases hcf : c f
  · rw [gfpF_false hcf, gfpF_false hcf]
    constructor
    · rintro ⟨δ, h1, h2⟩
      exact ⟨δ, (hP δ).mp h1, h2⟩
    · rintro ⟨δ, h1, h2⟩
      exact ⟨δ, (hP δ).mpr h1, h2⟩
  · rw [gfpF_true hcf, gfpF_true hcf]
    constructor
    · intro h δ hδ
      exact h δ ((hP δ).mpr hδ)
    · intro h δ hδ
      exact h δ ((hP δ).mp hδ)

/-! #### Step 2: solving the equations at `F` class by class -/

/-- `F(f)`: the vertices of `F` that `f` reaches. -/
noncomputable def FrF (F : Finset V) (f : V) : Finset V := F.filter (fun x => ReflTransGen E f x)

/-- The class `{f ∈ F : F(f) = Φ}`. -/
noncomputable def KsetF (F Φ : Finset V) : Finset V := F.filter (fun f => FrF E F f = Φ)

/-- The map `Ψ` of a class: the values on the class are `δ`, below they are `Γn β`. -/
noncomputable def PsiF (F : Finset V) (h : V → (V → Bool) → Bool)
    (Γn : (V → Bool) → V → Bool) (Φ : Finset V) (β : V → Bool) :
    (V → Bool) → V → Bool :=
  fun δ f => h f (glue ↑(KsetF E F Φ) δ (Γn β))

/-- The solution extended from the classes with `|F(f)| < n` to those with `|F(f)| = n`. -/
noncomputable def GammaStep (c : V → Bool) (F : Finset V) (h : V → (V → Bool) → Bool)
    (Γn : (V → Bool) → V → Bool) (n : ℕ) : (V → Bool) → V → Bool :=
  fun β x => if x ∈ F ∧ (FrF E F x).card = n then
    gfpF c (KsetF E F (FrF E F x)) (PsiF E F h Γn (FrF E F x) β) x else Γn β x

lemma mem_FrF {F : Finset V} {f x : V} : x ∈ FrF E F f ↔ x ∈ F ∧ ReflTransGen E f x :=
  Finset.mem_filter

lemma mem_KsetF {F Φ : Finset V} {f : V} : f ∈ KsetF E F Φ ↔ f ∈ F ∧ FrF E F f = Φ :=
  Finset.mem_filter

lemma FrF_mono {F : Finset V} {f f' : V} (h : ReflTransGen E f f') :
    FrF E F f' ⊆ FrF E F f := by
  intro x hx
  rw [mem_FrF] at hx ⊢
  exact ⟨hx.1, h.trans hx.2⟩

lemma GammaStep_new {c : V → Bool} {F : Finset V} {h : V → (V → Bool) → Bool}
    {Γn : (V → Bool) → V → Bool} {n : ℕ} {β : V → Bool} {x : V}
    (hx : x ∈ F ∧ (FrF E F x).card = n) :
    GammaStep E c F h Γn n β x =
      gfpF c (KsetF E F (FrF E F x)) (PsiF E F h Γn (FrF E F x) β) x := by
  unfold GammaStep
  exact ite_eq_left hx

lemma GammaStep_old {c : V → Bool} {F : Finset V} {h : V → (V → Bool) → Bool}
    {Γn : (V → Bool) → V → Bool} {n : ℕ} {β : V → Bool} {x : V}
    (hx : ¬ (x ∈ F ∧ (FrF E F x).card = n)) : GammaStep E c F h Γn n β x = Γn β x := by
  unfold GammaStep
  exact ite_eq_right hx

lemma fix_aux (c : V → Bool) (X F : Finset V) (h : V → (V → Bool) → Bool)
    (hcaus : ∀ f ∈ F, ∀ γ γ', (∀ x ∈ X, ReflTransGen E f x → γ x = γ' x) → h f γ = h f γ')
    (hmono : ∀ s γ γ', SignLE c (comp E s) {x | x ∈ X ∧ ReflTransGen E s x} γ γ' →
      ∀ f ∈ F, f ∈ comp E s → leAt c f (h f γ) (h f γ')) :
    ∀ n : ℕ, ∃ Γ : (V → Bool) → V → Bool,
      (∀ β x, ¬ (x ∈ F ∧ (FrF E F x).card < n) → Γ β x = β x) ∧
      (∀ β, ∀ f ∈ F, (FrF E F f).card < n → Γ β f = h f (Γ β)) ∧
      (∀ β β', ∀ f ∈ F, (FrF E F f).card < n →
        (∀ x ∈ X, x ∉ F → ReflTransGen E f x → β x = β' x) → Γ β f = Γ β' f) ∧
      (∀ s β β', SignLE c (comp E s) {x | x ∈ X ∧ x ∉ F ∧ ReflTransGen E s x} β β' →
        SignLE c (comp E s) {x | x ∈ F ∧ (FrF E F x).card < n ∧ ReflTransGen E s x}
          (Γ β) (Γ β')) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun β => β, fun β x _ => rfl, fun β f _ hlt => absurd hlt (Nat.not_lt_zero _),
      fun β β' f _ hlt => absurd hlt (Nat.not_lt_zero _), ?_⟩
    rintro s β β' - x ⟨-, hlt, -⟩
    exact absurd hlt (Nat.not_lt_zero _)
  | succ n ih =>
    obtain ⟨Γ, hA, hB, hC, hD⟩ := ih
    -- a vertex of `F` reached from the class of `f` is in that class or below it
    have hK : ∀ f f', f ∈ F → (FrF E F f).card = n → f' ∈ F → ReflTransGen E f f' →
        (FrF E F f').card < n ∨ FrF E F f' = FrF E F f := by
      intro f f' hfF hfn hf'F hff'
      by_cases hlt : (FrF E F f').card < n
      · exact Or.inl hlt
      · exact Or.inr (Finset.eq_of_subset_of_card_le (FrF_mono E hff') (by omega))
    -- members of a class reach each other
    have hKreach : ∀ f f', f ∈ F → f' ∈ F → FrF E F f' = FrF E F f → ReflTransGen E f' f := by
      intro f f' hfF hf'F heq
      have hf : f ∈ FrF E F f := (mem_FrF E).mpr ⟨hfF, ReflTransGen.refl⟩
      rw [← heq] at hf
      exact ((mem_FrF E).mp hf).2
    -- the map of a class is monotone in the sign order
    have hPsimono : ∀ (β : V → Bool) (Φ : Finset V), ∀ δ δ',
        (∀ g ∈ KsetF E F Φ, leAt c g (δ g) (δ' g)) →
        ∀ g ∈ KsetF E F Φ, leAt c g (PsiF E F h Γ Φ β δ g) (PsiF E F h Γ Φ β δ' g) := by
      intro β Φ δ δ' hδ g hg
      have hgK := (mem_KsetF E).mp hg
      refine hmono g _ _ ?_ g hgK.1 ⟨ReflTransGen.refl, ReflTransGen.refl⟩
      rintro x ⟨hxX, hgx⟩
      by_cases hxK : x ∈ KsetF E F Φ
      · have hxK' := (mem_KsetF E).mp hxK
        have hxg : ReflTransGen E x g := hKreach g x hgK.1 hxK'.1 (hxK'.2.trans hgK.2.symm)
        rw [glue_mem (show x ∈ (↑(KsetF E F Φ) : Set V) from hxK),
          glue_mem (show x ∈ (↑(KsetF E F Φ) : Set V) from hxK)]
        exact ⟨fun _ => hδ x hxK, fun hxS => (hxS ⟨hgx, hxg⟩).elim⟩
      · rw [glue_not_mem (show x ∉ (↑(KsetF E F Φ) : Set V) from hxK),
          glue_not_mem (show x ∉ (↑(KsetF E F Φ) : Set V) from hxK)]
        exact ⟨fun _ => leAt_refl x _, fun _ => rfl⟩
    have hfix : ∀ (β : V → Bool) (Φ : Finset V), ∀ f ∈ KsetF E F Φ,
        gfpF c (KsetF E F Φ) (PsiF E F h Γ Φ β) f =
          PsiF E F h Γ Φ β (gfpF c (KsetF E F Φ) (PsiF E F h Γ Φ β)) f :=
      fun β Φ => (gfpF_spec (hPsimono β Φ)).1
    have hGold : ∀ β x, ¬ (x ∈ F ∧ (FrF E F x).card = n) →
        GammaStep E c F h Γ n β x = Γ β x := fun β x hx => GammaStep_old E hx
    have hGnew : ∀ β x, x ∈ F → (FrF E F x).card = n → GammaStep E c F h Γ n β x =
        gfpF c (KsetF E F (FrF E F x)) (PsiF E F h Γ (FrF E F x) β) x :=
      fun β x hxF hxn => GammaStep_new E ⟨hxF, hxn⟩
    -- what a new vertex sees
    have hagNew : ∀ β f, f ∈ F → (FrF E F f).card = n → ∀ x ∈ X, ReflTransGen E f x →
        GammaStep E c F h Γ n β x = glue ↑(KsetF E F (FrF E F f))
          (gfpF c (KsetF E F (FrF E F f)) (PsiF E F h Γ (FrF E F f) β)) (Γ β) x := by
      intro β f hfF hfn x hxX hfx
      by_cases hxF : x ∈ F
      · rcases hK f x hfF hfn hxF hfx with hlt | heq
        · have hxK : x ∉ KsetF E F (FrF E F f) := by
            intro hk
            have h1 := ((mem_KsetF E).mp hk).2
            rw [h1] at hlt
            omega
          rw [hGold β x (fun ⟨_, h'⟩ => by omega),
            glue_not_mem (show x ∉ (↑(KsetF E F (FrF E F f)) : Set V) from hxK)]
        · have hxK : x ∈ KsetF E F (FrF E F f) := (mem_KsetF E).mpr ⟨hxF, heq⟩
          have hxn : (FrF E F x).card = n := by rw [heq]; exact hfn
          rw [hGnew β x hxF hxn, heq,
            glue_mem (show x ∈ (↑(KsetF E F (FrF E F f)) : Set V) from hxK)]
      · have hxK : x ∉ KsetF E F (FrF E F f) := fun hk => hxF ((mem_KsetF E).mp hk).1
        rw [hGold β x (fun ⟨h', _⟩ => hxF h'),
          glue_not_mem (show x ∉ (↑(KsetF E F (FrF E F f)) : Set V) from hxK)]
    -- what an old vertex sees
    have hagOld : ∀ β f, (FrF E F f).card < n → ∀ x, ReflTransGen E f x →
        GammaStep E c F h Γ n β x = Γ β x := by
      intro β f hfn x hfx
      apply hGold β x
      rintro ⟨-, hxn⟩
      have hle := Finset.card_le_card (FrF_mono E (F := F) hfx)
      omega
    -- causality
    have hC' : ∀ β β', ∀ f ∈ F, (FrF E F f).card < n + 1 →
        (∀ x ∈ X, x ∉ F → ReflTransGen E f x → β x = β' x) →
        GammaStep E c F h Γ n β f = GammaStep E c F h Γ n β' f := by
      intro β β' f hfF hfn hag
      by_cases hlt : (FrF E F f).card < n
      · rw [hGold β f (fun ⟨_, h'⟩ => by omega), hGold β' f (fun ⟨_, h'⟩ => by omega)]
        exact hC β β' f hfF hlt hag
      · have hfn' : (FrF E F f).card = n := by omega
        rw [hGnew β f hfF hfn', hGnew β' f hfF hfn']
        apply gfpF_congr
        intro δ
        have hPsi : ∀ g ∈ KsetF E F (FrF E F f),
            PsiF E F h Γ (FrF E F f) β δ g = PsiF E F h Γ (FrF E F f) β' δ g := by
          intro g hg
          have hgK := (mem_KsetF E).mp hg
          have hfg : ReflTransGen E f g := hKreach g f hgK.1 hfF hgK.2.symm
          show h g (glue ↑(KsetF E F (FrF E F f)) δ (Γ β)) =
            h g (glue ↑(KsetF E F (FrF E F f)) δ (Γ β'))
          apply hcaus g hgK.1
          intro x hx hgx
          by_cases hxK : x ∈ KsetF E F (FrF E F f)
          · rw [glue_mem (show x ∈ (↑(KsetF E F (FrF E F f)) : Set V) from hxK),
              glue_mem (show x ∈ (↑(KsetF E F (FrF E F f)) : Set V) from hxK)]
          · rw [glue_not_mem (show x ∉ (↑(KsetF E F (FrF E F f)) : Set V) from hxK),
              glue_not_mem (show x ∉ (↑(KsetF E F (FrF E F f)) : Set V) from hxK)]
            have hfx : ReflTransGen E f x := hfg.trans hgx
            by_cases hxF : x ∈ F
            · rcases hK f x hfF hfn' hxF hfx with hxlt | heq
              · exact hC β β' x hxF hxlt (fun y hy hyF hxy => hag y hy hyF (hfx.trans hxy))
              · exact absurd ((mem_KsetF E).mpr ⟨hxF, heq⟩) hxK
            · rw [hA β x (fun ⟨h1, _⟩ => hxF h1), hA β' x (fun ⟨h1, _⟩ => hxF h1)]
              exact hag x hx hxF hfx
        constructor
        · intro hp g hg
          rw [← hPsi g hg]
          exact hp g hg
        · intro hp g hg
          rw [hPsi g hg]
          exact hp g hg
    refine ⟨GammaStep E c F h Γ n, ?_, ?_, hC', ?_⟩
    · -- (A)
      intro β x hx
      rw [hGold β x (fun ⟨h1, h2⟩ => hx ⟨h1, by omega⟩)]
      exact hA β x (fun ⟨h1, h2⟩ => hx ⟨h1, by omega⟩)
    · -- (B): the equations
      intro β f hfF hfn
      by_cases hlt : (FrF E F f).card < n
      · rw [hGold β f (fun ⟨_, h'⟩ => by omega), hB β f hfF hlt]
        apply hcaus f hfF
        intro x _ hfx
        exact (hagOld β f hlt x hfx).symm
      · have hfn' : (FrF E F f).card = n := by omega
        have hfK : f ∈ KsetF E F (FrF E F f) := (mem_KsetF E).mpr ⟨hfF, rfl⟩
        rw [hGnew β f hfF hfn', hfix β _ f hfK]
        show h f (glue ↑(KsetF E F (FrF E F f))
            (gfpF c (KsetF E F (FrF E F f)) (PsiF E F h Γ (FrF E F f) β)) (Γ β)) =
          h f (GammaStep E c F h Γ n β)
        apply hcaus f hfF
        intro x hx hfx
        exact (hagNew β f hfF hfn' x hx hfx).symm
    · -- (D): monotonicity
      rintro s β β' hββ' x ⟨hxF, hxn, hsx⟩
      constructor
      · intro hxS
        by_cases hlt : (FrF E F x).card < n
        · rw [hGold β x (fun ⟨_, h'⟩ => by omega), hGold β' x (fun ⟨_, h'⟩ => by omega)]
          exact (hD s β β' hββ' x ⟨hxF, hlt, hsx⟩).1 hxS
        · have hxn' : (FrF E F x).card = n := by omega
          rw [hGnew β x hxF hxn', hGnew β' x hxF hxn']
          -- the solution for `β` is a post-fixed point of the class map for `β'`
          have hpost : postFix c (KsetF E F (FrF E F x)) (PsiF E F h Γ (FrF E F x) β')
              (gfpF c (KsetF E F (FrF E F x)) (PsiF E F h Γ (FrF E F x) β)) := by
            intro g hg
            have hgK := (mem_KsetF E).mp hg
            have hgx : ReflTransGen E g x := hKreach x g hxF hgK.1 hgK.2
            have hxg : ReflTransGen E x g := hKreach g x hgK.1 hxF hgK.2.symm
            have hgS : g ∈ comp E s := ⟨hsx.trans hxg, hgx.trans hxS.2⟩
            rw [hfix β _ g hg]
            refine hmono s _ _ ?_ g hgK.1 hgS
            rintro y ⟨hyX, hsy⟩
            by_cases hyK : y ∈ KsetF E F (FrF E F x)
            · rw [glue_mem (show y ∈ (↑(KsetF E F (FrF E F x)) : Set V) from hyK),
                glue_mem (show y ∈ (↑(KsetF E F (FrF E F x)) : Set V) from hyK)]
              exact ⟨fun _ => leAt_refl y _, fun _ => rfl⟩
            · rw [glue_not_mem (show y ∉ (↑(KsetF E F (FrF E F x)) : Set V) from hyK),
                glue_not_mem (show y ∉ (↑(KsetF E F (FrF E F x)) : Set V) from hyK)]
              by_cases hyF : y ∈ F
              · have hxy : ReflTransGen E x y := hxS.2.trans hsy
                rcases hK x y hxF hxn' hyF hxy with hylt | heq
                · exact hD s β β' hββ' y ⟨hyF, hylt, hsy⟩
                · exact absurd ((mem_KsetF E).mpr ⟨hyF, heq⟩) hyK
              · rw [hA β y (fun ⟨h1, _⟩ => hyF h1), hA β' y (fun ⟨h1, _⟩ => hyF h1)]
                exact hββ' y ⟨hyX, hyF, hsy⟩
          exact (gfpF_spec (hPsimono β' _)).2 _ hpost x
      · intro hxS
        exact hC' β β' x hxF hxn (fun y hy hyF hxy =>
          (hββ' y ⟨hy, hyF, hsx.trans hxy⟩).2 (fun hyS => hxS ⟨hsx, hxy.trans hyS.2⟩))

/-- Step 2 of Lemma 4.8: a causal, monotone solution `Γ` of the equations `γ f = h f γ`
    at the vertices of `F`, for every assignment `β` on `X \ F`. -/
lemma fix_solve (c : V → Bool) (X F : Finset V) (h : V → (V → Bool) → Bool)
    (hcaus : ∀ f ∈ F, ∀ γ γ', (∀ x ∈ X, ReflTransGen E f x → γ x = γ' x) → h f γ = h f γ')
    (hmono : ∀ s γ γ', SignLE c (comp E s) {x | x ∈ X ∧ ReflTransGen E s x} γ γ' →
      ∀ f ∈ F, f ∈ comp E s → leAt c f (h f γ) (h f γ')) :
    ∃ Γ : (V → Bool) → V → Bool,
      (∀ β x, x ∉ F → Γ β x = β x) ∧
      (∀ β, ∀ f ∈ F, Γ β f = h f (Γ β)) ∧
      (∀ β β', ∀ f ∈ F, (∀ x ∈ X, x ∉ F → ReflTransGen E f x → β x = β' x) →
        Γ β f = Γ β' f) ∧
      (∀ s β β', SignLE c (comp E s) {x | x ∈ X ∧ x ∉ F ∧ ReflTransGen E s x} β β' →
        SignLE c (comp E s) {x | x ∈ X ∧ ReflTransGen E s x} (Γ β) (Γ β')) := by
  obtain ⟨Γ, hA, hB, hC, hD⟩ := fix_aux E c X F h hcaus hmono (F.card + 1)
  have hbound : ∀ f, (FrF E F f).card < F.card + 1 :=
    fun f => Nat.lt_succ_of_le (Finset.card_filter_le F _)
  refine ⟨Γ, fun β x hx => hA β x (fun ⟨h1, _⟩ => hx h1),
    fun β f hf => hB β f hf (hbound f), fun β β' f hf hag => hC β β' f hf (hbound f) hag, ?_⟩
  rintro s β β' hββ' x ⟨hxX, hsx⟩
  by_cases hxF : x ∈ F
  · exact hD s β β' hββ' x ⟨hxF, hbound x, hsx⟩
  · rw [hA β x (fun ⟨h1, _⟩ => hxF h1), hA β' x (fun ⟨h1, _⟩ => hxF h1)]
    exact hββ' x ⟨hxX, hxF, hsx⟩

/-- Lemma 4.8 (adding a region). -/
lemma adding_region (c : V → Bool) (hc : IsCompColouring E c)
    (U : Set V) (hU : FinitePort E U) (σ : (V → Bool) → V → Bool)
    (hσ : IsGoodSolver E c U σ)
    (W : Set V) (hW : FinitePort E W) (hWkp : KernelPerfectOn E W) :
    ∃ τ, IsGoodSolver E c (U ∪ W) τ ∧ Extends U (U ∪ W) σ τ := by
  obtain ⟨hσsol, hσcaus, hσmono⟩ := hσ
  have hH : FinitePort E (U ∪ W) := finitePort_union E hU hW
  -- `F`: the ports of `U` inside `H = U ∪ W`; `P`: the ports of `H`; `X = F ∪ P`
  obtain ⟨F, hF⟩ : ∃ F : Finset V, F = hU.toFinset.filter (fun x => x ∈ U ∪ W) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Finset V, P = hH.toFinset := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Finset V, X = F ∪ P := ⟨_, rfl⟩
  have hmemF : ∀ x, x ∈ F ↔ x ∈ ports E U ∧ x ∈ U ∪ W := by
    intro x
    rw [hF, Finset.mem_filter, hU.mem_toFinset]
  have hmemP : ∀ x, x ∈ P ↔ x ∈ ports E (U ∪ W) := by
    intro x
    rw [hP, hH.mem_toFinset]
  have hmemX : ∀ x, x ∈ X ↔ x ∈ F ∨ x ∈ P := by
    intro x
    rw [hX, Finset.mem_union]
  have hFX : ∀ x ∈ F, x ∈ X := fun x hx => (hmemX x).mpr (Or.inl hx)
  have hPX : ∀ x ∈ P, x ∈ X := fun x hx => (hmemX x).mpr (Or.inr hx)
  -- `W'`: the rest of `H`
  obtain ⟨W', hW'⟩ : ∃ W' : Set V, W' = (U ∪ W) \ (U ∪ ↑F) := ⟨_, rfl⟩
  have hmemW' : ∀ x, x ∈ W' ↔ x ∈ U ∪ W ∧ x ∉ U ∧ x ∉ F := by
    intro x
    rw [hW']
    constructor
    · rintro ⟨hxH, hxUF⟩
      exact ⟨hxH, fun h => hxUF (Or.inl h), fun h => hxUF (Or.inr h)⟩
    · rintro ⟨hxH, hxU, hxF⟩
      refine ⟨hxH, ?_⟩
      rintro (h | h)
      · exact hxU h
      · exact hxF h
  have hW'kp : KernelPerfectOn E W' := by
    refine kpOn_mono E hWkp ?_
    intro x hx
    obtain ⟨hxH, hxU, -⟩ := (hmemW' x).mp hx
    rcases hxH with h | h
    · exact absurd h hxU
    · exact h
  have hFU : ∀ x ∈ F, x ∉ U := fun x hx => ((hmemF x).mp hx).1.1
  have hFH : ∀ x ∈ F, x ∈ U ∪ W := fun x hx => ((hmemF x).mp hx).2
  have hPH : ∀ x ∈ P, x ∉ U ∪ W := fun x hx => ((hmemP x).mp hx).1
  have hXU : ∀ x ∈ X, x ∉ U := by
    intro x hx
    rcases (hmemX x).mp hx with h | h
    · exact hFU x h
    · exact fun hxU => hPH x h (Or.inl hxU)
  have hXW' : ∀ x ∈ X, x ∉ W' := by
    intro x hx hxW'
    obtain ⟨hxH, -, hxF⟩ := (hmemW' x).mp hxW'
    rcases (hmemX x).mp hx with h | h
    · exact hxF h
    · exact hPH x h hxH
  have hXF_P : ∀ x ∈ X, x ∉ F → x ∈ P := by
    intro x hx hxF
    rcases (hmemX x).mp hx with h | h
    · exact absurd h hxF
    · exact h
  have hportsU : ∀ b ∈ ports E U, b ∈ X := by
    intro b hb
    by_cases hbH : b ∈ U ∪ W
    · exact hFX b ((hmemF b).mpr ⟨hb, hbH⟩)
    · obtain ⟨-, u, hu, hub⟩ := hb
      exact hPX b ((hmemP b).mpr ⟨hbH, u, Or.inl hu, hub⟩)
  have hcases : ∀ v ∈ U ∪ W, v ∈ U ∨ v ∈ F ∨ v ∈ W' := by
    intro v hv
    by_cases hvU : v ∈ U
    · exact Or.inl hvU
    · by_cases hvF : v ∈ F
      · exact Or.inr (Or.inl hvF)
      · exact Or.inr (Or.inr ((hmemW' v).mpr ⟨hv, hvU, hvF⟩))
  have hsucc : ∀ v ∈ U ∪ W, ∀ z, E v z → z ∈ U ∨ z ∈ W' ∨ z ∈ X := by
    intro v hv z hvz
    by_cases hzH : z ∈ U ∪ W
    · rcases hcases z hzH with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (hFX z h))
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (hPX z ((hmemP z).mpr ⟨hzH, v, hv, hvz⟩)))
  have hW'H : ∀ x ∈ W', x ∈ U ∪ W := fun x hx => ((hmemW' x).mp hx).1
  have hW'U : ∀ x ∈ W', x ∉ U := fun x hx => ((hmemW' x).mp hx).2.1
  -- Step 1: the vetoes `g` on `W'` and the layered solution `ω` (Lemma 4.6)
  obtain ⟨g, hgdef⟩ : ∃ g : V → (V → Bool) → Bool,
      g = fun w γ => allFalse {z | E w z ∧ (z ∈ U ∨ z ∈ X)} (glue U (σ γ) γ) := ⟨_, rfl⟩
  have hgval : ∀ w γ, g w γ = allFalse {z | E w z ∧ (z ∈ U ∨ z ∈ X)} (glue U (σ γ) γ) := by
    intro w γ
    rw [hgdef]
  have hg : ∀ w ∈ W', ∀ γ γ', (∀ x ∈ X, ReflTransGen E w x → γ x = γ' x) →
      g w γ = g w γ' := by
    intro w hw γ γ' hag
    rw [hgval, hgval]
    apply allFalse_congr
    rintro z ⟨hwz, hzUX⟩
    by_cases hzU : z ∈ U
    · rw [glue_mem hzU, glue_mem hzU]
      apply hσcaus γ γ' z hzU
      intro b hb hzb
      exact hag b (hportsU b hb) (ReflTransGen.head hwz hzb)
    · rw [glue_not_mem hzU, glue_not_mem hzU]
      rcases hzUX with h | h
      · exact absurd h hzU
      · exact hag z h (ReflTransGen.single hwz)
  obtain ⟨ω, hω1, hω2, hω3⟩ := layered_solving E c hc W' hW'kp X hXW' g hg
  -- the assignment `a_γ`: `σ` on `U`, `ω` on `W'`, `γ` elsewhere
  obtain ⟨a, hadef⟩ : ∃ a : (V → Bool) → V → Bool,
      a = fun γ => glue U (σ γ) (glue W' (ω γ) γ) := ⟨_, rfl⟩
  have haU : ∀ γ, ∀ v ∈ U, a γ v = σ γ v := by
    intro γ v hv
    rw [hadef]
    show glue U (σ γ) (glue W' (ω γ) γ) v = σ γ v
    rw [glue_mem hv]
  have haW' : ∀ γ, ∀ v ∈ W', a γ v = ω γ v := by
    intro γ v hv
    rw [hadef]
    show glue U (σ γ) (glue W' (ω γ) γ) v = ω γ v
    rw [glue_not_mem (hW'U v hv), glue_mem hv]
  have haX : ∀ γ, ∀ v ∈ X, a γ v = γ v := by
    intro γ v hv
    rw [hadef]
    show glue U (σ γ) (glue W' (ω γ) γ) v = γ v
    rw [glue_not_mem (hXU v hv), glue_not_mem (hXW' v hv)]
  -- (a): the kernel equations at the vertices of `U` and `W'`
  have haEqU : ∀ γ, ∀ u ∈ U, KernelEqAt E (a γ) u := by
    intro γ u hu
    refine (kernelEq_congr E ?_ ?_).mpr (hσsol γ u hu)
    · rw [haU γ u hu, glue_mem hu]
    · intro z huz
      by_cases hzU : z ∈ U
      · rw [haU γ z hzU, glue_mem hzU]
      · rw [haX γ z (hportsU z ⟨hzU, u, hu, huz⟩), glue_not_mem hzU]
  have haEqW' : ∀ γ, ∀ w ∈ W', KernelEqAt E (a γ) w := by
    intro γ w hw
    show a γ w = true ↔ ∀ z, E w z → a γ z = false
    rw [haW' γ w hw, hω1 γ w hw, hgval]
    constructor
    · rintro ⟨hgt, hz⟩ z hwz
      rcases hsucc w (hW'H w hw) z hwz with hzU | hzW' | hzX
      · rw [haU γ z hzU]
        have h1 := (allFalse_true.mp hgt) z ⟨hwz, Or.inl hzU⟩
        rwa [glue_mem hzU] at h1
      · rw [haW' γ z hzW']
        exact hz z hzW' hwz
      · rw [haX γ z hzX]
        have h1 := (allFalse_true.mp hgt) z ⟨hwz, Or.inr hzX⟩
        rwa [glue_not_mem (hXU z hzX)] at h1
    · intro hall
      refine ⟨allFalse_true.mpr ?_, fun z hz hwz => ?_⟩
      · rintro z ⟨hwz, hzUX⟩
        have h1 := hall z hwz
        by_cases hzU : z ∈ U
        · rw [haU γ z hzU] at h1
          rw [glue_mem hzU]
          exact h1
        · rcases hzUX with h | h
          · exact absurd h hzU
          · rw [haX γ z h] at h1
            rw [glue_not_mem hzU]
            exact h1
      · have h1 := hall z hwz
        rwa [haW' γ z hz] at h1
  -- (b): causality
  have hacaus : ∀ γ γ', ∀ v, (v ∈ U ∨ v ∈ W') →
      (∀ x ∈ X, ReflTransGen E v x → γ x = γ' x) → a γ v = a γ' v := by
    rintro γ γ' v (hv | hv) hag
    · rw [haU γ v hv, haU γ' v hv]
      apply hσcaus γ γ' v hv
      intro b hb hvb
      exact hag b (hportsU b hb) hvb
    · rw [haW' γ v hv, haW' γ' v hv]
      exact hω2 γ γ' v hv hag
  -- the hypothesis of Lemma 4.6(3), by the sign rule and (d)
  have hyp46 : ∀ s, ∀ γ1 γ2, SignLE c (comp E s) ↑X γ1 γ2 →
      ∀ w ∈ W' ∩ comp E s, leAt c w (g w γ1) (g w γ2) := by
    intro s γ1 γ2 hγ w hw
    rw [hgval, hgval]
    refine sign_rule E c hc s w hw.2 {z | E w z ∧ (z ∈ U ∨ z ∈ X)} (fun z hz => hz.1)
      (glue U (σ γ1) γ1) (glue U (σ γ2) γ2) ?_
    rintro z ⟨hwz, hzUX⟩
    by_cases hzU : z ∈ U
    · rw [glue_mem hzU, glue_mem hzU]
      refine ⟨fun hzS => ?_, fun hzS => ?_⟩
      · exact (hσmono s γ1 γ2 (fun b hb => hγ b (hportsU b hb)) z ⟨hzU, hzS⟩).1 hzS
      · apply hσcaus γ1 γ2 z hzU
        intro b hb hzb
        apply (hγ b (hportsU b hb)).2
        intro hbS
        exact hzS ⟨hw.2.1.tail hwz, hzb.trans hbS.2⟩
    · rw [glue_not_mem hzU, glue_not_mem hzU]
      rcases hzUX with h | h
      · exact absurd h hzU
      · exact hγ z h
  -- (c): monotonicity for `γ ⊑ γ'` on all of `X`
  have hamonoFull : ∀ s γ1 γ2, SignLE c (comp E s) ↑X γ1 γ2 → ∀ v, (v ∈ U ∨ v ∈ W') →
      v ∈ comp E s → leAt c v (a γ1 v) (a γ2 v) := by
    rintro s γ1 γ2 hγ v (hv | hv) hvS
    · rw [haU γ1 v hv, haU γ2 v hv]
      exact (hσmono s γ1 γ2 (fun b hb => hγ b (hportsU b hb)) v ⟨hv, hvS⟩).1 hvS
    · rw [haW' γ1 v hv, haW' γ2 v hv]
      exact (hω3 s (hyp46 s) γ1 γ2 hγ v ⟨hv, hvS⟩).1 hvS
  -- (c) and (d), for `γ ⊑ γ'` on the vertices of `X` reached from `S`
  have hamono : ∀ s γ γ', SignLE c (comp E s) {x | x ∈ X ∧ ReflTransGen E s x} γ γ' →
      ∀ v, (v ∈ U ∨ v ∈ W') → ReflTransGen E s v →
        (v ∈ comp E s → leAt c v (a γ v) (a γ' v)) ∧ (v ∉ comp E s → a γ v = a γ' v) := by
    intro s γ γ' hγ v hv hsv
    constructor
    · intro hvS
      obtain ⟨γh, hγh⟩ : ∃ γh : V → Bool, γh = glue {x | ReflTransGen E s x} γ γ' :=
        ⟨_, rfl⟩
      have hfull : SignLE c (comp E s) ↑X γh γ' := by
        intro x hx
        by_cases hsx : ReflTransGen E s x
        · have h1 : γh x = γ x := by
            rw [hγh]
            exact glue_mem (show x ∈ {x | ReflTransGen E s x} from hsx)
          rw [h1]
          exact hγ x ⟨hx, hsx⟩
        · have h1 : γh x = γ' x := by
            rw [hγh]
            exact glue_not_mem (show x ∉ {x | ReflTransGen E s x} from hsx)
          rw [h1]
          exact ⟨fun _ => leAt_refl x _, fun _ => rfl⟩
      have heq : a γ v = a γh v := by
        apply hacaus γ γh v hv
        intro x _ hvx
        rw [hγh]
        exact (glue_mem (show x ∈ {x | ReflTransGen E s x} from hsv.trans hvx)).symm
      rw [heq]
      exact hamonoFull s γh γ' hfull v hv hvS
    · intro hvS
      apply hacaus γ γ' v hv
      intro x hx hvx
      apply (hγ x ⟨hx, hsv.trans hvx⟩).2
      intro hxS
      exact hvS ⟨hsv, hvx.trans hxS.2⟩
  -- Step 2: the equations at `F`
  obtain ⟨kf, hkfdef⟩ : ∃ kf : V → (V → Bool) → Bool,
      kf = fun f γ => allFalse {z | E f z} (a γ) := ⟨_, rfl⟩
  have hkfval : ∀ f γ, kf f γ = allFalse {z | E f z} (a γ) := by
    intro f γ
    rw [hkfdef]
  have hcausF : ∀ f ∈ F, ∀ γ γ', (∀ x ∈ X, ReflTransGen E f x → γ x = γ' x) →
      kf f γ = kf f γ' := by
    intro f hf γ γ' hag
    rw [hkfval, hkfval]
    apply allFalse_congr
    intro z hfz
    have hfz' : E f z := hfz
    rcases hsucc f (hFH f hf) z hfz' with hzU | hzW' | hzX
    · exact hacaus γ γ' z (Or.inl hzU) (fun x hx hzx => hag x hx (ReflTransGen.head hfz' hzx))
    · exact hacaus γ γ' z (Or.inr hzW') (fun x hx hzx => hag x hx (ReflTransGen.head hfz' hzx))
    · rw [haX γ z hzX, haX γ' z hzX]
      exact hag z hzX (ReflTransGen.single hfz')
  have hmonoF : ∀ s γ γ', SignLE c (comp E s) {x | x ∈ X ∧ ReflTransGen E s x} γ γ' →
      ∀ f ∈ F, f ∈ comp E s → leAt c f (kf f γ) (kf f γ') := by
    intro s γ γ' hγ f hf hfS
    rw [hkfval, hkfval]
    refine sign_rule E c hc s f hfS {z | E f z} (fun z hz => hz) (a γ) (a γ') ?_
    intro z hfz
    have hfz' : E f z := hfz
    have hsz : ReflTransGen E s z := hfS.1.tail hfz'
    rcases hsucc f (hFH f hf) z hfz' with hzU | hzW' | hzX
    · exact hamono s γ γ' hγ z (Or.inl hzU) hsz
    · exact hamono s γ γ' hγ z (Or.inr hzW') hsz
    · rw [haX γ z hzX, haX γ' z hzX]
      exact hγ z ⟨hzX, hsz⟩
  obtain ⟨Γ, hΓA, hΓB, hΓC, hΓD⟩ := fix_solve E c X F kf hcausF hmonoF
  have hΓP : ∀ β, ∀ x ∈ P, Γ β x = β x :=
    fun β x hx => hΓA β x (fun hxF => hPH x hx (hFH x hxF))
  -- Step 3: `τ_β = a_{Γ β}` on `H`
  refine ⟨fun β => a (Γ β), ⟨?_, ?_, ?_⟩, ?_⟩
  · -- `τ_β` is a solution of `H` for `β`
    intro β v hv
    have hka : KernelEqAt E (a (Γ β)) v := by
      rcases hcases v hv with hvU | hvF | hvW'
      · exact haEqU (Γ β) v hvU
      · show a (Γ β) v = true ↔ ∀ z, E v z → a (Γ β) z = false
        rw [haX (Γ β) v (hFX v hvF), hΓB β v hvF, hkfval]
        exact allFalse_true
      · exact haEqW' (Γ β) v hvW'
    have hagr : ∀ y, (y ∈ U ∪ W ∨ y ∈ ports E (U ∪ W)) →
        glue (U ∪ W) ((fun β => a (Γ β)) β) β y = a (Γ β) y := by
      rintro y (hy | hy)
      · exact glue_mem hy
      · have hyP : y ∈ P := (hmemP y).mpr hy
        rw [glue_not_mem hy.1, haX (Γ β) y (hPX y hyP), hΓP β y hyP]
    refine (kernelEq_congr E (hagr v (Or.inl hv)) ?_).mpr hka
    intro z hvz
    by_cases hzH : z ∈ U ∪ W
    · exact hagr z (Or.inl hzH)
    · exact hagr z (Or.inr ⟨hzH, v, hv, hvz⟩)
  · -- causality
    intro β β' v hv hag
    have hΓag : ∀ x ∈ X, ReflTransGen E v x → Γ β x = Γ β' x := by
      intro x hx hvx
      by_cases hxF : x ∈ F
      · apply hΓC β β' x hxF
        intro y hy hyF hxy
        exact hag y ((hmemP y).mp (hXF_P y hy hyF)) (hvx.trans hxy)
      · have hxP := hXF_P x hx hxF
        rw [hΓP β x hxP, hΓP β' x hxP]
        exact hag x ((hmemP x).mp hxP) hvx
    show a (Γ β) v = a (Γ β') v
    rcases hcases v hv with hvU | hvF | hvW'
    · exact hacaus (Γ β) (Γ β') v (Or.inl hvU) hΓag
    · rw [haX (Γ β) v (hFX v hvF), haX (Γ β') v (hFX v hvF)]
      exact hΓag v (hFX v hvF) ReflTransGen.refl
    · exact hacaus (Γ β) (Γ β') v (Or.inr hvW') hΓag
  · -- monotonicity
    intro s β β' hββ' v hv
    refine ⟨fun hvS => ?_, fun hvS => absurd hv.2 hvS⟩
    have hβloc : SignLE c (comp E s) {x | x ∈ X ∧ x ∉ F ∧ ReflTransGen E s x} β β' := by
      rintro x ⟨hxX, hxF, -⟩
      exact hββ' x ((hmemP x).mp (hXF_P x hxX hxF))
    have hΓloc := hΓD s β β' hβloc
    have hsv : ReflTransGen E s v := hv.2.1
    show leAt c v (a (Γ β) v) (a (Γ β') v)
    rcases hcases v hv.1 with hvU | hvF | hvW'
    · exact (hamono s (Γ β) (Γ β') hΓloc v (Or.inl hvU) hsv).1 hvS
    · rw [haX (Γ β) v (hFX v hvF), haX (Γ β') v (hFX v hvF)]
      exact (hΓloc v ⟨hFX v hvF, hsv⟩).1 hvS
    · exact (hamono s (Γ β) (Γ β') hΓloc v (Or.inr hvW') hsv).1 hvS
  · -- `τ` extends `σ`
    intro β u hu
    show a (Γ β) u = σ (glue (U ∪ W) (a (Γ β)) β) u
    rw [haU (Γ β) u hu]
    apply hσcaus (Γ β) _ u hu
    intro b hb _
    by_cases hbH : b ∈ U ∪ W
    · rw [glue_mem hbH, haX (Γ β) b (hportsU b hb)]
    · obtain ⟨-, u', hu', hu'b⟩ := hb
      rw [glue_not_mem hbH]
      exact hΓP β b ((hmemP b).mpr ⟨hbH, u', Or.inl hu', hu'b⟩)

/-! ### Proof of Lemma 1.3: exhaustion and the limit -/

/-- "Extension is transitive, as one sees by writing out the definition twice." -/
lemma extends_trans {U H' H : Set V} {σ σ' τ : (V → Bool) → V → Bool}
    (hUH' : U ⊆ H') (hH'H : H' ⊆ H)
    (hσc : ∀ β β', ∀ u ∈ U, (∀ b ∈ ports E U, ReflTransGen E u b → β b = β' b) →
      σ β u = σ β' u)
    (h1 : Extends U H' σ σ') (h2 : Extends H' H σ' τ) : Extends U H σ τ := by
  intro β u hu
  rw [h2 β u (hUH' hu), h1 _ u hu]
  apply hσc _ _ u hu
  intro b hb _
  by_cases hbH' : b ∈ H'
  · rw [glue_mem hbH', glue_mem (hH'H hbH')]
    exact (h2 β b hbH').symm
  · rw [glue_not_mem hbH']

/-- One exhaustion step: add a kernel-perfect finite-port region around every
    port of `U`, one at a time (Lemma 4.8). -/
lemma exhaust_step (c : V → Bool) (hc : IsCompColouring E c) (Y : Set V)
    (hYcl : ∀ u ∈ Y, ∀ w, E u w → w ∈ Y)
    (hcov : ∀ v ∈ Y, ∃ U ⊆ Y, FinitePort E U ∧ v ∈ U ∧ KernelPerfectOn E U)
    (U : Set V) (hUY : U ⊆ Y) (hU : FinitePort E U)
    (σ : (V → Bool) → V → Bool) (hσ : IsGoodSolver E c U σ) :
    ∃ H τ, U ⊆ H ∧ ports E U ⊆ H ∧ H ⊆ Y ∧ FinitePort E H ∧
      IsGoodSolver E c H τ ∧ Extends U H σ τ := by
  have key : ∀ P : Finset V, ↑P ⊆ Y → ∃ H τ, U ⊆ H ∧ ↑P ⊆ H ∧ H ⊆ Y ∧ FinitePort E H ∧
      IsGoodSolver E c H τ ∧ Extends U H σ τ := by
    intro P
    refine Finset.induction_on P ?_ ?_
    · intro _
      refine ⟨U, σ, subset_rfl, by simp, hUY, hU, hσ, ?_⟩
      intro β u hu
      apply hσ.2.1 _ _ u hu
      intro b hb _
      rw [glue_not_mem hb.1]
    · intro a s ha ih hsub
      obtain ⟨H, τ, h1, h2, h3, h4, h5, h6⟩ :=
        ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      have haY : a ∈ Y := hsub (Finset.mem_insert_self a s)
      obtain ⟨W, hWY, hW, haW, hWkp⟩ := hcov a haY
      obtain ⟨τ', hτ', hext⟩ := adding_region E c hc H h4 τ h5 W hW hWkp
      refine ⟨H ∪ W, τ', h1.trans subset_union_left, ?_, union_subset h3 hWY,
        finitePort_union E h4 hW, hτ', extends_trans E h1 subset_union_left hσ.2.1 h6 hext⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Or.inr haW
      · exact Or.inl (h2 hx)
  have hPY : ↑hU.toFinset ⊆ Y := by
    intro x hx
    obtain ⟨-, u, hu, hux⟩ := hU.mem_toFinset.mp hx
    exact hYcl u (hUY hu) x hux
  obtain ⟨H, τ, h⟩ := key hU.toFinset hPY
  exact ⟨H, τ, h.1, fun x hx => h.2.1 (hU.mem_toFinset.mpr hx), h.2.2⟩

/-- A sequence defined by recursion. -/
def seqRec {T : Type*} (a0 : T) (nxt : ℕ → T → T) : ℕ → T
  | 0 => a0
  | n + 1 => nxt n (seqRec a0 nxt n)

/-- `projIter π n m = π n ∘ π (n+1) ∘ ⋯ ∘ π (n+m-1)`. -/
def projIter {T : Type*} (π : ℕ → T → T) (n : ℕ) : ℕ → T → T
  | 0 => id
  | m + 1 => fun b => projIter π n m (π (n + m) b)

lemma projIter_succ' {T : Type*} (π : ℕ → T → T) :
    ∀ n m b, projIter π n (m + 1) b = π n (projIter π (n + 1) m b)
  | n, 0, b => rfl
  | n, m + 1, b => by
    show projIter π n (m + 1) (π (n + (m + 1)) b) =
      π n (projIter π (n + 1) m (π (n + 1 + m) b))
    rw [projIter_succ' π n m, show n + 1 + m = n + (m + 1) by omega]

/-- König's lemma for an inverse sequence of finite nonempty sets. -/
lemma konig {T : Type*} (A : ℕ → Set T) (hfin : ∀ n, (A n).Finite)
    (hne : ∀ n, (A n).Nonempty) (π : ℕ → T → T) (hπ : ∀ n, ∀ b ∈ A (n + 1), π n b ∈ A n) :
    ∃ x : ℕ → T, (∀ n, x n ∈ A n) ∧ ∀ n, π n (x (n + 1)) = x n := by
  have hproj : ∀ n m, ∀ b ∈ A (n + m), projIter π n m b ∈ A n := by
    intro n m
    induction m with
    | zero => intro b hb; exact hb
    | succ m ih => intro b hb; exact ih _ (hπ (n + m) b hb)
  have hanti : ∀ n m, ∀ a, (∃ b ∈ A (n + (m + 1)), projIter π n (m + 1) b = a) →
      ∃ b ∈ A (n + m), projIter π n m b = a := by
    rintro n m a ⟨b, hb, hba⟩
    exact ⟨π (n + m) b, hπ _ b hb, hba⟩
  have hanti' : ∀ n m m', m ≤ m' → ∀ a, (∃ b ∈ A (n + m'), projIter π n m' b = a) →
      ∃ b ∈ A (n + m), projIter π n m b = a := by
    intro n m m' hmm'
    induction hmm' with
    | refl => exact fun a h => h
    | step _ ih => exact fun a h => ih a (hanti n _ a h)
  -- every level has a "good" element: one in the image of every later level
  have hex : ∀ n, ∃ a, ∀ m, ∃ b ∈ A (n + m), projIter π n m b = a := by
    intro n
    by_contra hno
    push_neg at hno
    choose mf hmf using hno
    obtain ⟨M, hM⟩ : ∃ M, ∀ a ∈ A n, mf a ≤ M :=
      ⟨(hfin n).toFinset.sup mf, fun a ha => Finset.le_sup ((hfin n).mem_toFinset.mpr ha)⟩
    obtain ⟨b, hb⟩ := hne (n + M)
    have ha := hproj n M b hb
    obtain ⟨b', hb', hb'a⟩ := hanti' n (mf (projIter π n M b)) M (hM _ ha) _ ⟨b, hb, rfl⟩
    exact hmf _ b' hb' hb'a
  -- a good element has a good preimage
  have hstep : ∀ n a, (∀ m, ∃ b ∈ A (n + m), projIter π n m b = a) →
      ∃ b, b ∈ A (n + 1) ∧ (∀ m, ∃ c ∈ A (n + 1 + m), projIter π (n + 1) m c = b) ∧
        π n b = a := by
    intro n a ha
    by_contra hno
    push_neg at hno
    have hbad : ∀ b, ∃ m, b ∈ A (n + 1) → π n b = a →
        ∀ c ∈ A (n + 1 + m), projIter π (n + 1) m c ≠ b := by
      intro b
      by_cases hb : b ∈ A (n + 1) ∧ π n b = a
      · by_contra hall
        push_neg at hall
        exact hno b hb.1 (fun m => (hall m).2.2) hb.2
      · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hb⟩
    choose mf hmf using hbad
    obtain ⟨M, hM⟩ : ∃ M, ∀ b ∈ A (n + 1), mf b ≤ M :=
      ⟨(hfin (n + 1)).toFinset.sup mf,
        fun b hb => Finset.le_sup ((hfin (n + 1)).mem_toFinset.mpr hb)⟩
    obtain ⟨c, hc, hca⟩ := ha (M + 1)
    rw [projIter_succ'] at hca
    have hc' : c ∈ A (n + 1 + M) := by
      rw [show n + 1 + M = n + (M + 1) by omega]
      exact hc
    obtain ⟨b, hbdef⟩ : ∃ b, b = projIter π (n + 1) M c := ⟨_, rfl⟩
    rw [← hbdef] at hca
    have hbA : b ∈ A (n + 1) := by rw [hbdef]; exact hproj (n + 1) M c hc'
    obtain ⟨c', hc'', hc'b⟩ :=
      hanti' (n + 1) (mf b) M (hM b hbA) b ⟨c, hc', hbdef.symm⟩
    exact hmf b hbA hca c' hc'' hc'b
  haveI : Nonempty T := ⟨(hne 0).some⟩
  choose! nxt hnxt using hstep
  obtain ⟨a0, ha0⟩ := hex 0
  have hx : ∀ n, ∀ m, ∃ b ∈ A (n + m), projIter π n m b = seqRec a0 nxt n := by
    intro n
    induction n with
    | zero => exact ha0
    | succ n ih => exact (hnxt n _ ih).2.1
  refine ⟨seqRec a0 nxt, fun n => ?_, fun n => (hnxt n _ (hx n)).2.2⟩
  obtain ⟨b, hb, hba⟩ := hx n 0
  rw [← hba]
  exact hb

/-- Port patterns that vanish outside a finite set form a finite set. -/
lemma patterns_finite {P : Set V} (hP : P.Finite) :
    {β : V → Bool | ∀ v, v ∉ P → β v = false}.Finite := by
  apply Set.Finite.of_finite_image (f := fun β => {v | β v = true})
  · apply hP.finite_subsets.subset
    rintro S ⟨β, hβ, rfl⟩
    intro v hv
    have hv' : β v = true := hv
    by_contra hvP
    rw [hβ v hvP] at hv'
    exact absurd hv' (by decide)
  · intro β _ β' _ h
    have h' : {v | β v = true} = {v | β' v = true} := h
    funext v
    have h1 : v ∈ {v | β v = true} ↔ v ∈ {v | β' v = true} := by rw [h']
    exact Bool.eq_iff_iff.mpr h1

/-- The limit: an increasing chain of finite-port regions with good solvers, each
    extending the previous one and containing its ports, gives a kernel of the union. -/
lemma limit_kernel (c : V → Bool) (U : ℕ → Set V) (σ : ℕ → (V → Bool) → V → Bool)
    (hFP : ∀ n, FinitePort E (U n)) (hgood : ∀ n, IsGoodSolver E c (U n) (σ n))
    (hsub : ∀ n, U n ⊆ U (n + 1)) (hports : ∀ n, ports E (U n) ⊆ U (n + 1))
    (hext : ∀ n, Extends (U n) (U (n + 1)) (σ n) (σ (n + 1))) :
    ∃ K, IsKernelOf E (⋃ n, U n) K := by
  -- states of the ports, and König's lemma
  obtain ⟨βs, -, hβπ⟩ := konig
    (fun n => {β : V → Bool | ∀ v, v ∉ ports E (U n) → β v = false})
    (fun n => patterns_finite (P := ports E (U n)) (hFP n))
    (fun n => ⟨fun _ => false, fun _ _ => rfl⟩)
    (fun n β => glue (ports E (U n)) (σ (n + 1) β) (fun _ => false))
    (fun n β _ v hv => by
      show glue (ports E (U n)) (σ (n + 1) β) (fun _ => false) v = false
      rw [glue_not_mem hv])
  have key : ∀ n, ∀ v ∈ ports E (U n), σ (n + 1) (βs (n + 1)) v = βs n v := by
    intro n v hv
    have h1 : glue (ports E (U n)) (σ (n + 1) (βs (n + 1))) (fun _ => false) v = βs n v :=
      congrFun (hβπ n) v
    rw [glue_mem hv] at h1
    exact h1
  have hmono : ∀ n d, U n ⊆ U (n + d) := by
    intro n d
    induction d with
    | zero => exact subset_rfl
    | succ d ih => exact ih.trans (hsub (n + d))
  -- the chosen solutions agree where they overlap
  have hcons : ∀ n, ∀ u ∈ U n, σ (n + 1) (βs (n + 1)) u = σ n (βs n) u := by
    intro n u hu
    rw [hext n (βs (n + 1)) u hu]
    apply (hgood n).2.1 _ _ u hu
    intro b hb _
    rw [glue_mem (hports n hb)]
    exact key n b hb
  have hcons' : ∀ n d, ∀ u ∈ U n, σ (n + d) (βs (n + d)) u = σ n (βs n) u := by
    intro n d
    induction d with
    | zero => intro u hu; rfl
    | succ d ih =>
      intro u hu
      rw [← ih u hu]
      exact hcons (n + d) u (hmono n d hu)
  obtain ⟨K, hKdef⟩ : ∃ K : Set V, K = {v | ∃ n, v ∈ U n ∧ σ n (βs n) v = true} :=
    ⟨_, rfl⟩
  have hK : ∀ n, ∀ v ∈ U n, (v ∈ K ↔ σ n (βs n) v = true) := by
    intro n v hv
    rw [hKdef]
    constructor
    · rintro ⟨m, hm, hvm⟩
      have e1 := hcons' n m v hv
      have e2 := hcons' m n v hm
      rw [Nat.add_comm m n] at e2
      rw [← e1, e2]
      exact hvm
    · intro h
      exact ⟨n, hv, h⟩
  -- the values seen by the equation at a vertex of `U n` are the values of `K`
  have hsucc : ∀ n, ∀ v ∈ U n, ∀ w, E v w →
      (glue (U n) (σ n (βs n)) (βs n) w = true ↔ w ∈ K) := by
    intro n v hv w hvw
    by_cases hw : w ∈ U n
    · rw [glue_mem hw, hK n w hw]
    · have hwp : w ∈ ports E (U n) := ⟨hw, v, hv, hvw⟩
      rw [glue_not_mem hw, ← key n w hwp, hK (n + 1) w (hports n hwp)]
  refine ⟨K, ?_, ?_, ?_⟩
  · intro v hv
    rw [hKdef] at hv
    obtain ⟨n, hn, -⟩ := hv
    exact mem_iUnion.mpr ⟨n, hn⟩
  · intro u hu w hw huw
    have hu' := hu
    rw [hKdef] at hu'
    obtain ⟨n, hn, hun⟩ := hu'
    have sol : glue (U n) (σ n (βs n)) (βs n) u = true ↔
        ∀ w, E u w → glue (U n) (σ n (βs n)) (βs n) w = false := (hgood n).1 (βs n) u hn
    have hgu : glue (U n) (σ n (βs n)) (βs n) u = true := by
      rw [glue_mem hn]
      exact hun
    have h1 := sol.mp hgu w huw
    have h2 := (hsucc n u hn w huw).mpr hw
    rw [h1] at h2
    exact absurd h2 (by decide)
  · intro v hv hvK
    obtain ⟨n, hn⟩ := mem_iUnion.mp hv
    have sol : glue (U n) (σ n (βs n)) (βs n) v = true ↔
        ∀ w, E v w → glue (U n) (σ n (βs n)) (βs n) w = false := (hgood n).1 (βs n) v hn
    have hgv : ¬ glue (U n) (σ n (βs n)) (βs n) v = true := by
      rw [glue_mem hn]
      intro h
      exact hvK ((hK n v hn).mpr h)
    have hn' : ¬ ∀ w, E v w → glue (U n) (σ n (βs n)) (βs n) w = false :=
      fun h => hgv (sol.mpr h)
    push_neg at hn'
    obtain ⟨w, hvw, hw⟩ := hn'
    have hwt : glue (U n) (σ n (βs n)) (βs n) w = true := by simpa using hw
    exact ⟨w, (hsucc n v hn w hvw).mp hwt, hvw⟩

/-- Exhaustion (proof of Lemma 1.3): inside a successor-closed `Y` covered by
    kernel-perfect finite-port regions, some nonempty successor-closed `D ⊆ Y`
    induces a graph with a kernel. -/
lemma exhaust (c : V → Bool) (hc : IsCompColouring E c) (Y : Set V)
    (hYcl : ∀ u ∈ Y, ∀ w, E u w → w ∈ Y) (y : V) (hy : y ∈ Y)
    (hcov : ∀ v ∈ Y, ∃ U ⊆ Y, FinitePort E U ∧ v ∈ U ∧ KernelPerfectOn E U) :
    ∃ D ⊆ Y, D.Nonempty ∧ (∀ u ∈ D, ∀ w, E u w → w ∈ D) ∧ ∃ K, IsKernelOf E D K := by
  obtain ⟨U0, hU0Y, hU0, hyU0, hU0kp⟩ := hcov y hy
  obtain ⟨σ0, hσ0⟩ := good_solver_exists E c hc U0 hU0 hU0kp
  have hstep : ∀ p : Set V × ((V → Bool) → V → Bool),
      (p.1 ⊆ Y ∧ FinitePort E p.1 ∧ IsGoodSolver E c p.1 p.2) →
      ∃ q : Set V × ((V → Bool) → V → Bool), p.1 ⊆ q.1 ∧ ports E p.1 ⊆ q.1 ∧
        (q.1 ⊆ Y ∧ FinitePort E q.1 ∧ IsGoodSolver E c q.1 q.2) ∧
        Extends p.1 q.1 p.2 q.2 := by
    rintro ⟨U, σ⟩ ⟨hUY, hU, hσ⟩
    obtain ⟨H, τ, h1, h2, h3, h4, h5, h6⟩ := exhaust_step E c hc Y hYcl hcov U hUY hU σ hσ
    exact ⟨(H, τ), h1, h2, ⟨h3, h4, h5⟩, h6⟩
  haveI : Nonempty (Set V × ((V → Bool) → V → Bool)) := ⟨(U0, σ0)⟩
  choose! nxt hnxt using hstep
  have hinv : ∀ n, (seqRec (U0, σ0) (fun _ p => nxt p) n).1 ⊆ Y ∧
      FinitePort E (seqRec (U0, σ0) (fun _ p => nxt p) n).1 ∧
      IsGoodSolver E c (seqRec (U0, σ0) (fun _ p => nxt p) n).1
        (seqRec (U0, σ0) (fun _ p => nxt p) n).2 := by
    intro n
    induction n with
    | zero => exact ⟨hU0Y, hU0, hσ0⟩
    | succ n ih => exact (hnxt (seqRec (U0, σ0) (fun _ p => nxt p) n) ih).2.2.1
  have hrel := fun n => hnxt (seqRec (U0, σ0) (fun _ p => nxt p) n) (hinv n)
  obtain ⟨K, hK⟩ := limit_kernel E c (fun n => (seqRec (U0, σ0) (fun _ p => nxt p) n).1)
    (fun n => (seqRec (U0, σ0) (fun _ p => nxt p) n).2)
    (fun n => (hinv n).2.1) (fun n => (hinv n).2.2)
    (fun n => (hrel n).1) (fun n => (hrel n).2.1) (fun n => (hrel n).2.2.2)
  refine ⟨⋃ n, (seqRec (U0, σ0) (fun _ p => nxt p) n).1,
    iUnion_subset (fun n => (hinv n).1), ⟨y, mem_iUnion.mpr ⟨0, hyU0⟩⟩, ?_, K, hK⟩
  intro u hu w huw
  obtain ⟨n, hn⟩ := mem_iUnion.mp hu
  by_cases hw : w ∈ (seqRec (U0, σ0) (fun _ p => nxt p) n).1
  · exact mem_iUnion.mpr ⟨n, hw⟩
  · have hwp : w ∈ ports E (seqRec (U0, σ0) (fun _ p => nxt p) n).1 := ⟨hw, u, hn, huw⟩
    exact mem_iUnion.mpr ⟨n + 1, (hrel n).2.1 hwp⟩

/-! ### Passing to induced subgraphs -/

lemma kernel_restrict_iff {Y X K : Set V} (hX : X ⊆ Y) :
    IsKernelOf (restrict E Y) X K ↔ IsKernelOf E X K := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun u hu w hw huw => h2 u hu w hw ⟨huw, hX (h1 hu), hX (h1 hw)⟩,
      fun v hv hvK => ?_⟩
    obtain ⟨w, hw, hvw⟩ := h3 v hv hvK
    exact ⟨w, hw, hvw.1⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun u hu w hw huw => h2 u hu w hw huw.1, fun v hv hvK => ?_⟩
    obtain ⟨w, hw, hvw⟩ := h3 v hv hvK
    exact ⟨w, hw, hvw, hX hv, hX (h1 hw)⟩

lemma kpOn_restrict {Y U : Set V} (hUY : U ⊆ Y) (h : KernelPerfectOn E U) :
    KernelPerfectOn (restrict E Y) U := by
  intro X hX
  obtain ⟨K, hK⟩ := h X hX
  exact ⟨K, (kernel_restrict_iff E (hX.trans hUY)).mpr hK⟩

lemma rtg_restrict {Y : Set V} {a b : V} (h : ReflTransGen (restrict E Y) a b) :
    ReflTransGen E a b := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ReflTransGen.tail ih hbc.1

lemma colouring_restrict {c : V → Bool} (hc : IsCompColouring E c) (Y : Set V) :
    IsCompColouring (restrict E Y) c :=
  fun u v huv hvu => hc u v huv.1 (rtg_restrict E hvu)

lemma finitePort_restrict {Y U : Set V} (hU : FinitePort E U) :
    FinitePort (restrict E Y) (U ∩ Y) := by
  refine hU.subset ?_
  rintro w ⟨hw, u, hu, huw⟩
  exact ⟨fun hwU => hw ⟨hwU, huw.2.2⟩, u, hu.1, huw.1⟩

/-- **Lemma 1.3 (finite-port cover).** -/
lemma cover (hodd : NoOddCycle E)
    (h : ∀ v : V, ∃ U, FinitePort E U ∧ v ∈ U ∧ KernelPerfectOn E U) :
    KernelPerfect E := by
  obtain ⟨c, hc⟩ := exists_compColouring E hodd
  intro X
  apply kernel_of_semikernels E X
  intro Y hYX hYne
  obtain ⟨y, hy⟩ := hYne
  -- work in `G[Y]`, where the hypothesis still holds (Lemma 4.2(2))
  obtain ⟨D, hDY, hDne, hDcl, K, hK⟩ :=
    exhaust (restrict E Y) c (colouring_restrict E hc Y) Y (fun u _ w huw => huw.2.2) y hy
      (by
        intro v hv
        obtain ⟨U, hU, hvU, hkp⟩ := h v
        exact ⟨U ∩ Y, inter_subset_right, finitePort_restrict E hU, ⟨hvU, hv⟩,
          kpOn_restrict E inter_subset_right (fun Z hZ => hkp Z (hZ.trans inter_subset_left))⟩)
  have hK' : IsKernelOf E D K := (kernel_restrict_iff E hDY).mp hK
  refine ⟨K, semikernel_of_succClosed E hDY ?_ (isSemikernelOf_of_isKernelOf E hK'),
    kernel_nonempty E hK' hDne⟩
  intro u hu w hw huw
  exact hDcl u hu w ⟨huw, hDY hu, hw⟩

/-! ## §5. Ladder rays -/

/-! ### Collisions -/

/-- Alternating walks from `r` (proof of Lemma 5.1): the flag is `false` for even
    length (the attempt makes the end true) and `true` for odd length (false).
    An even walk is prolonged by any edge, an odd one by the chosen edge to `d x`. -/
inductive AltW {α : Type*} (R : α → α → Prop) (d : α → α) (r : α) : α → Bool → Prop
  | start : AltW R d r r false
  | even {x y : α} : AltW R d r x false → R x y → AltW R d r y true
  | odd {x : α} : AltW R d r x true → R x (d x) → AltW R d r (d x) false

lemma walkN_restrict {Z : Set V} {u w : V} {n : ℕ} (h : WalkN (restrict E Z) u w n) :
    WalkN E u w n := by
  induction h with
  | nil v => exact WalkN.nil v
  | cons huv _ ih => exact WalkN.cons huv.1 ih

lemma prec_restrict {Z : Set V} {u w : V} (h : Prec (restrict E Z) u w) : Prec E u w := by
  obtain ⟨⟨n1, h1, w1⟩, ⟨n2, h2, w2⟩⟩ := h
  exact ⟨⟨n1, h1, walkN_restrict E w1⟩, ⟨n2, h2, walkN_restrict E w2⟩⟩

/-- Lemma 5.1 (collision). -/
lemma collision (hodd : NoOddCycle E) {C : Set V} (hC : IsCore E C) {r : V} (hr : r ∈ C) :
    ∃ z ∈ C, Prec (restrict E C) r z := by
  haveI : Nonempty V := ⟨r⟩
  -- choose a successor `d v` inside `C` for every `v ∈ C` (a core has no sink)
  obtain ⟨d, hd⟩ : ∃ d : V → V, ∀ v ∈ C, d v ∈ C ∧ E v (d v) := by
    choose! d hd using fun v (hv : v ∈ C) => core_no_sink E hC hv
    exact ⟨d, hd⟩
  have hmemC : ∀ x b, AltW (restrict E C) d r x b → x ∈ C := by
    intro x b h
    induction h with
    | start => exact hr
    | even _ hxy _ => exact hxy.2.2
    | odd _ hxd _ => exact hxd.2.2
  have hwalk : ∀ x b, AltW (restrict E C) d r x b →
      ∃ n, WalkN (restrict E C) r x n ∧ (b = false → Even n) ∧ (b = true → Odd n) := by
    intro x b h
    induction h with
    | start => exact ⟨0, WalkN.nil r, fun _ => ⟨0, rfl⟩, fun h => absurd h (by decide)⟩
    | even _ hxy ih =>
      obtain ⟨n, hn, he, -⟩ := ih
      exact ⟨n + 1, walkN_append (restrict E C) hn (WalkN.cons hxy (WalkN.nil _)),
        fun h => absurd h (by decide), fun _ => (he rfl).add_one⟩
    | odd _ hxd ih =>
      obtain ⟨n, hn, -, ho⟩ := ih
      exact ⟨n + 1, walkN_append (restrict E C) hn (WalkN.cons hxd (WalkN.nil _)),
        fun _ => (ho rfl).add_one, fun h => absurd h (by decide)⟩
  by_contra hno
  push_neg at hno
  -- otherwise the vertices made true form a nonempty semikernel of the core
  have hdisj : ∀ x, AltW (restrict E C) d r x false → AltW (restrict E C) d r x true →
      False := by
    intro x h0 h1
    obtain ⟨n1, w1, he1, -⟩ := hwalk x false h0
    obtain ⟨n2, w2, -, ho2⟩ := hwalk x true h1
    exact hno x (hmemC x false h0) ⟨⟨n1, he1 rfl, w1⟩, ⟨n2, ho2 rfl, w2⟩⟩
  have hsk : IsSemikernelOf E C {x | AltW (restrict E C) d r x false} := by
    refine ⟨fun x hx => hmemC x false hx, ?_, ?_⟩
    · intro x hx y hy hxy
      exact hdisj y hy (AltW.even hx ⟨hxy, hmemC x false hx, hmemC y false hy⟩)
    · intro u hu w hw huw
      have hwt : AltW (restrict E C) d r w true := AltW.even hu ⟨huw, hmemC u false hu, hw⟩
      exact ⟨d w, AltW.odd hwt ⟨(hd w hw).2, hw, (hd w hw).1⟩, (hd w hw).2⟩
  have hrS : r ∈ {x | AltW (restrict E C) d r x false} := AltW.start
  rw [hC.2 _ hsk] at hrS
  exact hrS

/-! ### Essential vertices -/

/-- Lemma 5.3(1): essential in an induced subgraph ⇒ essential in `G`. -/
lemma essential_of_restrict {H : Set V} {v : V} (hv : v ∈ H)
    (h : Essential (restrict E H) v) : Essential E v := by
  intro U hU hvU hkp
  exact h (U ∩ H) (finitePort_restrict E hU) ⟨hvU, hv⟩
    (kpOn_restrict E inter_subset_right (fun Z hZ => hkp Z (hZ.trans inter_subset_left)))

/-- A core is not kernel-perfect (it has no kernel). -/
lemma core_not_kp {C : Set V} (hC : IsCore E C) : ¬ KernelPerfectOn E C := by
  intro h
  obtain ⟨K, hK⟩ := h C subset_rfl
  have hne := kernel_nonempty E hK hC.1
  rw [hC.2 K (isSemikernelOf_of_isKernelOf E hK)] at hne
  exact Set.not_nonempty_empty hne

lemma noOddCycle_restrict (hodd : NoOddCycle E) (D : Set V) : NoOddCycle (restrict E D) := by
  intro v p hcyc
  obtain ⟨hne, hch, hlast, hnd⟩ := hcyc
  exact hodd v p ⟨hne, List.IsChain.imp (fun a b h => h.1) hch, hlast, hnd⟩

lemma mem_reachIn_self (Z : Set V) (v : V) : v ∈ reachIn E Z v :=
  (ReflTransGen.refl : ReflTransGen (restrict E Z) v v)

lemma rtg_of_reachIn {Z : Set V} {v w : V} (h : w ∈ reachIn E Z v) : ReflTransGen E v w :=
  rtg_restrict E h

/-- The vertices reachable from `v` in `G[Z]` form a successor-closed part of `G[Z]`. -/
lemma reachIn_succClosed {Z : Set V} {v : V} (hv : v ∈ Z) :
    SuccClosedIn E Z (reachIn E Z v) := by
  intro u hu w hw huw
  have hu' : ReflTransGen (restrict E Z) v u := hu
  have hvw : ReflTransGen (restrict E Z) v w := by
    refine ReflTransGen.tail hu' ?_
    exact ⟨huw, reachIn_subset E hv hu, hw⟩
  exact hvw

lemma reachIn_mono {Z1 Z2 : Set V} (h : Z1 ⊆ Z2) (v : V) :
    reachIn E Z1 v ⊆ reachIn E Z2 v := by
  intro w hw
  have hw' : ReflTransGen (restrict E Z1) v w := hw
  clear hw
  induction hw' with
  | refl => exact mem_reachIn_self E Z2 v
  | @tail b c _ hbc ih =>
    have ih' : ReflTransGen (restrict E Z2) v b := ih
    have hvc : ReflTransGen (restrict E Z2) v c := by
      refine ReflTransGen.tail ih' ?_
      exact ⟨hbc.1, h hbc.2.1, h hbc.2.2⟩
    exact hvc

lemma reachIn_restrict_eq {Z D : Set V} (hZD : Z ⊆ D) (v : V) :
    reachIn (restrict E D) Z v = reachIn E Z v := by
  have hrel : restrict (restrict E D) Z = restrict E Z := by
    funext a b
    apply propext
    constructor
    · rintro ⟨⟨h, -, -⟩, ha, hb⟩
      exact ⟨h, ha, hb⟩
    · rintro ⟨h, ha, hb⟩
      exact ⟨⟨h, hZD ha, hZD hb⟩, ha, hb⟩
  unfold reachIn
  rw [hrel]

/-- Lemma 5.3(2): cones at an essential vertex are not kernel-perfect. -/
lemma essential_cone {v : V} (hv : Essential E v) {Z : Set V} (hZ : FinitePort E Z)
    (hvZ : v ∈ Z) (F : Finset V) (hvF : v ∉ F) :
    ¬ KernelPerfectOn E (reachIn E (Z \ ↑F) v) :=
  hv _ (cone_finitePort E hZ F hvZ hvF) ReflTransGen.refl

/-- Lemma 5.3(3), in the form used: a graph without odd cycles that is not
    kernel-perfect has an essential vertex (contrapositive of Lemma 1.3). -/
lemma exists_essential (hodd : NoOddCycle E) (h : ¬ KernelPerfect E) :
    ∃ v, Essential E v := by
  by_contra hne
  push_neg at hne
  apply h
  apply cover E hodd
  intro v
  have hv := hne v
  unfold Essential at hv
  push_neg at hv
  exact hv

/-- Lemma 5.3(3) for a core `D`: it contains a vertex essential in `G[D]`. -/
lemma core_essential (hodd : NoOddCycle E) {D : Set V} (hD : IsCore E D) :
    ∃ p ∈ D, Essential (restrict E D) p := by
  have hnkp : ¬ KernelPerfect (restrict E D) := by
    intro hkp
    obtain ⟨K, hK⟩ := hkp D
    have hK' : IsKernelOf E D K := (kernel_restrict_iff E subset_rfl).mp hK
    have hne := kernel_nonempty E hK' hD.1
    rw [hD.2 K (isSemikernelOf_of_isKernelOf E hK')] at hne
    exact Set.not_nonempty_empty hne
  obtain ⟨p, hp⟩ := exists_essential (restrict E D) (noOddCycle_restrict E hodd D) hnkp
  refine ⟨p, ?_, hp⟩
  by_contra hpD
  -- outside `D` the vertex `p` is isolated in `G[D]`, hence not essential there
  have hFP : FinitePort (restrict E D) {p} := by
    refine Set.finite_empty.subset ?_
    rintro w ⟨-, u, hu, huw⟩
    rw [mem_singleton_iff] at hu
    rw [hu] at huw
    exact absurd huw.2.1 hpD
  have hKP : KernelPerfectOn (restrict E D) {p} := by
    intro X hX
    refine ⟨X, subset_rfl, ?_, ?_⟩
    · intro u hu w _ huw
      have hup := hX hu
      rw [mem_singleton_iff] at hup
      rw [hup] at huw
      exact hpD huw.2.1
    · intro v hv hvX
      exact absurd hv hvX
  exact hp {p} hFP (mem_singleton p) hKP

/-- Cones at a vertex essential in `G[D]` (inside `D`) are not kernel-perfect. -/
lemma cone_not_kp_of_essential_in {D : Set V} {p : V} (hpD : p ∈ D)
    (hp : Essential (restrict E D) p) (F : Finset V) (hpF : p ∉ F) :
    ¬ KernelPerfectOn E (reachIn E (D \ ↑F) p) := by
  intro hkp
  have hFP : FinitePort (restrict E D) D := by
    refine Set.finite_empty.subset ?_
    rintro w ⟨hw, u, -, huw⟩
    exact absurd huw.2.2 hw
  apply essential_cone (restrict E D) hp hFP hpD F hpF
  rw [reachIn_restrict_eq E sdiff_subset]
  have hpDF : p ∈ D \ ↑F := ⟨hpD, hpF⟩
  exact kpOn_restrict E ((reachIn_subset E hpDF).trans sdiff_subset) hkp

/-- Lemma 5.5(1): a tail of a ladder ray is a ladder ray. -/
lemma isLadderRay_tail {R : ℕ → V} (h : IsLadderRay E R) (m : ℕ) :
    IsLadderRay E (fun n => R (m + n)) := by
  obtain ⟨hR, b, hb, hess, hprec⟩ := h
  refine ⟨isRay_tail E hR m, fun i => b (m + i) - m, ?_, ?_, ?_⟩
  -- The facts coming from `StrictMono` / `StrictMono.id_le` carry the generic
  -- order instances (`Preorder.toLT`, `Preorder.toLE`), which `omega` does not
  -- recognise.  Restating them with explicit types puts them in the standard
  -- `Nat` form that `omega` understands.
  · intro i j hij'
    have hij : i < j := hij'
    have h1 : b (m + i) < b (m + j) := hb (show m + i < m + j by omega)
    have h2 : m + i ≤ b (m + i) := hb.id_le (m + i)
    show b (m + i) - m < b (m + j) - m
    omega
  · intro i
    have h2 : m + i ≤ b (m + i) := hb.id_le (m + i)
    have e1 : m + (b (m + i) - m) = b (m + i) := by omega
    show Essential E (R (m + (b (m + i) - m)))
    rw [e1]
    exact hess _
  · intro i j hij
    have h2 : m + i ≤ b (m + i) := hb.id_le (m + i)
    have h3 : m + j ≤ b (m + j) := hb.id_le (m + j)
    have e1 : m + (b (m + i) - m) = b (m + i) := by omega
    have e2 : m + (b (m + j) - m) = b (m + j) := by omega
    show Prec E (R (m + (b (m + i) - m))) (R (m + (b (m + j) - m)))
    rw [e1, e2]
    exact hprec _ _ (by omega)

/-- `(e1)`: `u ⟶* v ≺ w ⟶* x` gives `u ≺ x`. -/
lemma prec_extend {u v w x : V} (h1 : ReflTransGen E u v) (h : Prec E v w)
    (h2 : ReflTransGen E w x) : Prec E u x := by
  obtain ⟨a, ha⟩ := walkN_of_rtg E h1
  obtain ⟨b, hb⟩ := walkN_of_rtg E h2
  obtain ⟨⟨n1, he1, hw1⟩, ⟨n2, ho2, hw2⟩⟩ := h
  have w1 := walkN_append E (walkN_append E ha hw1) hb
  have w2 := walkN_append E (walkN_append E ha hw2) hb
  have e1 := Nat.even_iff.mp he1
  have o2 := Nat.odd_iff.mp ho2
  rcases Nat.even_or_odd (a + b) with hab | hab
  · have hab' := Nat.even_iff.mp hab
    exact ⟨⟨a + n1 + b, Nat.even_iff.mpr (by omega), w1⟩,
      ⟨a + n2 + b, Nat.odd_iff.mpr (by omega), w2⟩⟩
  · have hab' := Nat.odd_iff.mp hab
    exact ⟨⟨a + n2 + b, Nat.even_iff.mpr (by omega), w2⟩,
      ⟨a + n1 + b, Nat.odd_iff.mpr (by omega), w1⟩⟩

/-- `u ≺ u` is impossible without odd cycles. -/
lemma prec_irrefl (hodd : NoOddCycle E) {u : V} (h : Prec E u u) : False := by
  obtain ⟨-, ⟨n, hn, hw⟩⟩ := h
  exact Nat.not_even_iff_odd.mpr hn (closedWalk_even E hodd hw)

lemma ray_reach {R : ℕ → V} (hR : IsRay E R) (m d : ℕ) : ReflTransGen E (R m) (R (m + d)) := by
  induction d with
  | zero => exact ReflTransGen.refl
  | succ d ih => exact ReflTransGen.tail ih (hR.2 (m + d))

/-- Lemma 5.5(2) (splicing). (Only `q n ≤ p (n+1)` is needed.) -/
lemma isLadderRay_splice {R : ℕ → V} (hR : IsRay E R) (p q : ℕ → ℕ)
    (hpq : ∀ n, p n < q n) (hqp : ∀ n, q n ≤ p (n + 1))
    (hess : ∀ n, Essential E (R (p n))) (hprec : ∀ n, Prec E (R (p n)) (R (q n))) :
    IsLadderRay E R := by
  have hp : StrictMono p := strictMono_nat_of_lt_succ (fun n => lt_of_lt_of_le (hpq n) (hqp n))
  refine ⟨hR, p, hp, hess, fun i j hij => ?_⟩
  have h1 : p (i + 1) ≤ p j := hp.monotone (show i + 1 ≤ j by omega)
  have h2 : q i ≤ p (i + 1) := hqp i
  have hreach := ray_reach E hR (q i) (p j - q i)
  rw [show q i + (p j - q i) = p j by omega] at hreach
  exact prec_extend E ReflTransGen.refl (hprec i) hreach

/-! ### Paths as functions -/

/-- `f 0 → f 1 → ⋯ → f L` is a path. -/
def IsPathF (f : ℕ → V) (L : ℕ) : Prop :=
  (∀ t < L, E (f t) (f (t + 1))) ∧ ∀ i j, i ≤ L → j ≤ L → f i = f j → i = j

lemma isPathF_prefix {f : ℕ → V} {L K : ℕ} (hf : IsPathF E f L) (hK : K ≤ L) :
    IsPathF E f K :=
  ⟨fun t ht => hf.1 t (by omega), fun i j hi hj => hf.2 i j (by omega) (by omega)⟩

/-- A vertex reachable in `G[Z]` is reached by a path in `G[Z]` (take a shortest walk). -/
lemma exists_pathF {Z : Set V} {v w : V} (hv : v ∈ Z) (hw : w ∈ reachIn E Z v) :
    ∃ (f : ℕ → V) (L : ℕ), f 0 = v ∧ f L = w ∧ IsPathF E f L ∧ ∀ t ≤ L, f t ∈ Z := by
  have hw' : ReflTransGen (restrict E Z) v w := hw
  obtain ⟨n, hn⟩ := walkN_of_rtg (restrict E Z) hw'
  obtain ⟨f, hf0, hfn, hfe⟩ := walkN_fun (restrict E Z) hn
  have hex : ∃ L, ∃ f : ℕ → V, f 0 = v ∧ f L = w ∧ ∀ t < L, restrict E Z (f t) (f (t + 1)) :=
    ⟨n, f, hf0, hfn, hfe⟩
  obtain ⟨g, hg0, hgL, hge⟩ := Nat.find_spec hex
  set L := Nat.find hex with hL
  -- a shortest walk repeats no vertex: otherwise cut out the closed part
  have key : ∀ a b, a < b → b ≤ L → g a = g b → False := by
    intro a b hab hbL hgab
    apply Nat.find_min hex (show L - (b - a) < L by omega)
    refine ⟨fun t => if t ≤ a then g t else g (t + (b - a)), ?_, ?_, ?_⟩
    · show (if 0 ≤ a then g 0 else g (0 + (b - a))) = v
      rw [ite_eq_left (Nat.zero_le a)]
      exact hg0
    · show (if L - (b - a) ≤ a then g (L - (b - a)) else g (L - (b - a) + (b - a))) = w
      by_cases hc : L - (b - a) ≤ a
      · rw [ite_eq_left hc, show L - (b - a) = a by omega, hgab, show b = L by omega]
        exact hgL
      · rw [ite_eq_right hc, show L - (b - a) + (b - a) = L by omega]
        exact hgL
    · intro t ht
      show restrict E Z (if t ≤ a then g t else g (t + (b - a)))
        (if t + 1 ≤ a then g (t + 1) else g (t + 1 + (b - a)))
      by_cases h1 : t + 1 ≤ a
      · rw [ite_eq_left (show t ≤ a by omega), ite_eq_left h1]
        exact hge t (by omega)
      · by_cases h2 : t ≤ a
        · rw [ite_eq_left h2, ite_eq_right h1, show t + 1 + (b - a) = b + 1 by omega,
            show t = a by omega, hgab]
          exact hge b (by omega)
        · rw [ite_eq_right h2, ite_eq_right h1,
            show t + 1 + (b - a) = t + (b - a) + 1 by omega]
          exact hge _ (by omega)
  refine ⟨g, L, hg0, hgL, ⟨fun t ht => (hge t ht).1, ?_⟩, ?_⟩
  · intro i j hi hj hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key i j h hj hij
    · exact key j i h hi hij.symm
  · intro t ht
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · rw [h0, hg0]
      exact hv
    · have h1 := hge (t - 1) (by omega)
      rw [show t - 1 + 1 = t by omega] at h1
      exact h1.2.2

/-- The vertices of a path in `G[Z]` starting at `v` are reachable from `v` in `G[Z]`. -/
lemma pathF_reach {Z : Set V} {v : V} {f : ℕ → V} {L : ℕ} (hf0 : f 0 = v)
    (hfe : ∀ t < L, E (f t) (f (t + 1))) (hZ : ∀ t ≤ L, f t ∈ Z) :
    ∀ t ≤ L, f t ∈ reachIn E Z v := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [hf0]
    exact mem_reachIn_self E Z v
  | succ t ih =>
    intro ht
    have ih' : ReflTransGen (restrict E Z) v (f t) := ih (by omega)
    have hvt : ReflTransGen (restrict E Z) v (f (t + 1)) := by
      refine ReflTransGen.tail ih' ?_
      exact ⟨hfe t (by omega), hZ t (by omega), hZ (t + 1) ht⟩
    exact hvt

/-- `f` up to position `L`, then `g` (with `g 0` placed at position `L`). -/
def concatF (f g : ℕ → V) (L : ℕ) : ℕ → V :=
  fun t => if t ≤ L then f t else g (t - L)

lemma concatF_left {f g : ℕ → V} {L t : ℕ} (ht : t ≤ L) : concatF f g L t = f t := by
  show (if t ≤ L then f t else g (t - L)) = f t
  rw [ite_eq_left ht]

lemma concatF_right {f g : ℕ → V} {L : ℕ} (hfg : f L = g 0) (j : ℕ) :
    concatF f g L (L + j) = g j := by
  show (if L + j ≤ L then f (L + j) else g (L + j - L)) = g j
  by_cases hj : j = 0
  · subst hj
    rw [ite_eq_left (show L + 0 ≤ L by omega)]
    exact hfg
  · rw [ite_eq_right (show ¬ (L + j ≤ L) by omega), Nat.add_sub_cancel_left]

/-- Concatenation of two paths that meet only at the junction is a path. -/
lemma concatF_path {f g : ℕ → V} {L M : ℕ} (hf : IsPathF E f L) (hg : IsPathF E g M)
    (hfg : f L = g 0) (hdisj : ∀ i ≤ L, ∀ j ≤ M, f i = g j → i = L ∧ j = 0) :
    IsPathF E (concatF f g L) (L + M) := by
  constructor
  · intro t ht
    by_cases h1 : t < L
    · rw [concatF_left (show t ≤ L by omega), concatF_left (show t + 1 ≤ L by omega)]
      exact hf.1 t h1
    · obtain ⟨j, rfl⟩ : ∃ j, t = L + j := ⟨t - L, by omega⟩
      rw [concatF_right hfg, show L + j + 1 = L + (j + 1) by omega, concatF_right hfg]
      exact hg.1 j (by omega)
  · intro i j hi hj hij
    by_cases hiL : i ≤ L
    · by_cases hjL : j ≤ L
      · rw [concatF_left hiL, concatF_left hjL] at hij
        exact hf.2 i j hiL hjL hij
      · obtain ⟨b, rfl⟩ : ∃ b, j = L + b := ⟨j - L, by omega⟩
        rw [concatF_left hiL, concatF_right hfg] at hij
        have hh := hdisj i hiL b (by omega) hij
        omega
    · obtain ⟨a, rfl⟩ : ∃ a, i = L + a := ⟨i - L, by omega⟩
      by_cases hjL : j ≤ L
      · rw [concatF_right hfg, concatF_left hjL] at hij
        have hh := hdisj j hjL a (by omega) hij.symm
        omega
      · obtain ⟨b, rfl⟩ : ∃ b, j = L + b := ⟨j - L, by omega⟩
        rw [concatF_right hfg, concatF_right hfg] at hij
        have hh := hg.2 a b (by omega) (by omega) hij
        omega

/-- Lemma 5.6 (ladder step). Here `Z` plays the role of `H − A`, and the region in (2)
    is `Z` minus the vertices of the path `f 0, …, f L` other than its end `q = f L`;
    the essential vertex is `p = f k`. -/
lemma ladder_step (hodd : NoOddCycle E) (Z : Set V) (v : V) (hv : v ∈ Z)
    (hY : ¬ KernelPerfectOn E (reachIn E Z v)) :
    ∃ (f : ℕ → V) (L k : ℕ), f 0 = v ∧ k < L ∧ IsPathF E f L ∧
      (∀ t ≤ L, f t ∈ reachIn E Z v) ∧ Essential E (f k) ∧ Prec E (f k) (f L) ∧
      ¬ KernelPerfectOn E (reachIn E (Z \ {x | ∃ t < L, f t = x}) (f L)) := by
  have hYZ : reachIn E Z v ⊆ Z := reachIn_subset E hv
  -- an induced core `C` of `G[Y]`; a path `π = g|[0, i0]` from `v` to its first vertex in `C`
  obtain ⟨C, hCY, hC⟩ := exists_core E _ hY
  obtain ⟨c0, hc0⟩ := hC.1
  obtain ⟨g, Lg, hg0, hgL, hgp, hgZ⟩ := exists_pathF E hv (hCY hc0)
  have hexC : ∃ i, i ≤ Lg ∧ g i ∈ C := ⟨Lg, le_rfl, by rw [hgL]; exact hc0⟩
  obtain ⟨hi0L, hxC⟩ := Nat.find_spec hexC
  set i0 := Nat.find hexC with hi0
  have hbefore : ∀ t < i0, g t ∉ C := fun t ht hc => Nat.find_min hexC ht ⟨by omega, hc⟩
  have hgY : ∀ t ≤ Lg, g t ∈ reachIn E Z v := pathF_reach E hg0 hgp.1 hgZ
  -- `D`: the future of `x = g i0` in `C`, a core
  have hDC : reachIn E C (g i0) ⊆ C := reachIn_subset E hxC
  have hDcore : IsCore E (reachIn E C (g i0)) :=
    core_succClosed E hC hDC (reachIn_succClosed E hxC) ⟨g i0, mem_reachIn_self E C (g i0)⟩
  -- `p`: essential in `G[D]`; `ρ`: a path from `x` to `p` in `C`
  obtain ⟨p, hpD, hpess'⟩ := core_essential E hodd hDcore
  have hpess : Essential E p := essential_of_restrict E hpD hpess'
  obtain ⟨ρ, Lρ, hρ0, hρL, hρp, hρC⟩ := exists_pathF E hxC hpD
  obtain ⟨Fρ, hFρ⟩ : ∃ F : Finset V, F = (Finset.range Lρ).image ρ := ⟨_, rfl⟩
  have hmemFρ : ∀ y, y ∈ Fρ ↔ ∃ t, t < Lρ ∧ ρ t = y := by
    intro y
    rw [hFρ, Finset.mem_image]
    simp only [Finset.mem_range]
  have hpF : p ∉ Fρ := by
    intro h
    obtain ⟨t, ht, hρt⟩ := (hmemFρ p).mp h
    have h' := hρp.2 t Lρ (by omega) le_rfl (hρt.trans hρL.symm)
    omega
  -- `Y1`: the cone at `p` in `G[D] − (ρ − p)`; it contains an induced core `C1`
  have hY1 : ¬ KernelPerfectOn E (reachIn E (reachIn E C (g i0) \ ↑Fρ) p) :=
    cone_not_kp_of_essential_in E hpD hpess' Fρ hpF
  have hpDF : p ∈ reachIn E C (g i0) \ ↑Fρ := ⟨hpD, hpF⟩
  have hY1D : reachIn E (reachIn E C (g i0) \ ↑Fρ) p ⊆ reachIn E C (g i0) \ ↑Fρ :=
    reachIn_subset E hpDF
  obtain ⟨C1, hC1Y1, hC1⟩ := exists_core E _ hY1
  obtain ⟨r, hr⟩ := hC1.1
  obtain ⟨z, hz, hrz⟩ := collision E hodd hC1 hr
  -- `q`: essential in the future `D1` of `z` in `C1`
  have hD1C1 : reachIn E C1 z ⊆ C1 := reachIn_subset E hz
  have hD1core : IsCore E (reachIn E C1 z) :=
    core_succClosed E hC1 hD1C1 (reachIn_succClosed E hz) ⟨z, mem_reachIn_self E C1 z⟩
  obtain ⟨q, hqD1, hqess'⟩ := core_essential E hodd hD1core
  have hpq : Prec E p q :=
    prec_extend E (rtg_of_reachIn E (hC1Y1 hr)) (prec_restrict E hrz) (rtg_of_reachIn E hqD1)
  -- `τ`: a path from `p` to `q` in `D − (ρ − p)`
  obtain ⟨τ, Lτ, hτ0, hτL, hτp, hτZ⟩ := exists_pathF E hpDF (hC1Y1 (hD1C1 hqD1))
  obtain ⟨Fτ, hFτ⟩ : ∃ F : Finset V, F = (Finset.range Lτ).image τ := ⟨_, rfl⟩
  have hmemFτ : ∀ y, y ∈ Fτ ↔ ∃ t, t < Lτ ∧ τ t = y := by
    intro y
    rw [hFτ, Finset.mem_image]
    simp only [Finset.mem_range]
  have hqF : q ∉ Fτ := by
    intro h
    obtain ⟨t, ht, hτt⟩ := (hmemFτ q).mp h
    have h' := hτp.2 t Lτ (by omega) le_rfl (hτt.trans hτL.symm)
    omega
  -- `Y2`: the cone at `q` in `G[D1] − (τ − q)`, not kernel-perfect
  have hY2 : ¬ KernelPerfectOn E (reachIn E (reachIn E C1 z \ ↑Fτ) q) :=
    cone_not_kp_of_essential_in E hqD1 hqess' Fτ hqF
  have hLτ : 0 < Lτ := by
    rcases Nat.eq_zero_or_pos Lτ with h | h
    · exfalso
      have hqp : q = p := by rw [← hτL, ← hτ0, h]
      rw [hqp] at hpq
      exact prec_irrefl E hodd hpq
    · exact h
  -- the path `P = π ρ τ`
  have hπ : IsPathF E g i0 := isPathF_prefix E hgp hi0L
  have hgρ : g i0 = ρ 0 := hρ0.symm
  have hd1 : ∀ i ≤ i0, ∀ j ≤ Lρ, g i = ρ j → i = i0 ∧ j = 0 := by
    intro i hi j hj hij
    have hiC : g i ∈ C := by rw [hij]; exact hρC j hj
    have hii : i = i0 := by
      by_contra hne
      exact hbefore i (by omega) hiC
    refine ⟨hii, ?_⟩
    rw [hii, hgρ] at hij
    exact (hρp.2 0 j (Nat.zero_le _) hj hij).symm
  have hf1 : IsPathF E (concatF g ρ i0) (i0 + Lρ) := concatF_path E hπ hρp hgρ hd1
  have hf1end : concatF g ρ i0 (i0 + Lρ) = τ 0 := by rw [concatF_right hgρ, hρL, hτ0]
  have hval1 : ∀ t ≤ i0 + Lρ, (t < i0 ∧ concatF g ρ i0 t = g t) ∨
      (i0 ≤ t ∧ concatF g ρ i0 t = ρ (t - i0)) := by
    intro t ht
    by_cases h : t < i0
    · exact Or.inl ⟨h, concatF_left (by omega)⟩
    · refine Or.inr ⟨by omega, ?_⟩
      obtain ⟨s, rfl⟩ : ∃ s, t = i0 + s := ⟨t - i0, by omega⟩
      rw [concatF_right hgρ, Nat.add_sub_cancel_left]
  have hd2 : ∀ i ≤ i0 + Lρ, ∀ j ≤ Lτ, concatF g ρ i0 i = τ j → i = i0 + Lρ ∧ j = 0 := by
    intro i hi j hj hij
    have hτj := hτZ j hj
    rcases hval1 i hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2] at hij
      exact (hbefore i h1 (by rw [hij]; exact hDC hτj.1)).elim
    · rw [h2] at hij
      by_cases hs : i - i0 < Lρ
      · exact (hτj.2 ((hmemFρ (τ j)).mpr ⟨i - i0, hs, hij⟩)).elim
      · have hs' : i - i0 = Lρ := by omega
        rw [hs', hρL, ← hτ0] at hij
        have h0 := hτp.2 0 j (Nat.zero_le _) hj hij
        exact ⟨by omega, h0.symm⟩
  have hfp : IsPathF E (concatF (concatF g ρ i0) τ (i0 + Lρ)) (i0 + Lρ + Lτ) :=
    concatF_path E hf1 hτp hf1end hd2
  have hf0 : concatF (concatF g ρ i0) τ (i0 + Lρ) 0 = v := by
    rw [concatF_left (Nat.zero_le _), concatF_left (Nat.zero_le _), hg0]
  have hfk : concatF (concatF g ρ i0) τ (i0 + Lρ) (i0 + Lρ) = p := by
    rw [concatF_left le_rfl, concatF_right hgρ, hρL]
  have hfL : concatF (concatF g ρ i0) τ (i0 + Lρ) (i0 + Lρ + Lτ) = q := by
    rw [concatF_right hf1end, hτL]
  have hval : ∀ t ≤ i0 + Lρ + Lτ,
      (t ≤ i0 + Lρ ∧ concatF (concatF g ρ i0) τ (i0 + Lρ) t = concatF g ρ i0 t) ∨
      (i0 + Lρ ≤ t ∧ concatF (concatF g ρ i0) τ (i0 + Lρ) t = τ (t - (i0 + Lρ))) := by
    intro t ht
    by_cases h : t ≤ i0 + Lρ
    · exact Or.inl ⟨h, concatF_left h⟩
    · refine Or.inr ⟨by omega, ?_⟩
      obtain ⟨s, rfl⟩ : ∃ s, t = i0 + Lρ + s := ⟨t - (i0 + Lρ), by omega⟩
      rw [concatF_right hf1end, Nat.add_sub_cancel_left]
  refine ⟨concatF (concatF g ρ i0) τ (i0 + Lρ), i0 + Lρ + Lτ, i0 + Lρ, hf0, by omega, hfp,
    ?_, ?_, ?_, ?_⟩
  · -- all vertices lie in `Y`
    intro t ht
    rcases hval t ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]
      rcases hval1 t h1 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [h4]
        exact hgY t (by omega)
      · rw [h4]
        exact hCY (hρC _ (by omega))
    · rw [h2]
      exact hCY (hDC (hτZ _ (by omega)).1)
  · rw [hfk]
    exact hpess
  · rw [hfk, hfL]
    exact hpq
  · -- (2): `Y2` lies in the new region
    rw [hfL]
    intro hkp
    apply hY2
    refine kpOn_mono E hkp (reachIn_mono E ?_ q)
    rintro w ⟨hwD1, hwF⟩
    have hwD := hY1D (hC1Y1 (hD1C1 hwD1))
    refine ⟨hYZ (hCY (hDC hwD.1)), ?_⟩
    rintro ⟨t, ht, hft⟩
    rcases hval t (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2] at hft
      rcases hval1 t h1 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [h4] at hft
        exact hbefore t h3 (by rw [hft]; exact hDC hwD.1)
      · rw [h4] at hft
        by_cases hs : t - i0 < Lρ
        · exact hwD.2 ((hmemFρ w).mpr ⟨t - i0, hs, hft⟩)
        · have hs' : t - i0 = Lρ := by omega
          rw [hs', hρL, ← hτ0] at hft
          exact hwF ((hmemFτ w).mpr ⟨0, hLτ, hft⟩)
    · rw [h2] at hft
      exact hwF ((hmemFτ w).mpr ⟨t - (i0 + Lρ), by omega, hft⟩)

/-- The invariant of the construction in Proposition 5.7: a path `F 0, …, F M` in `Z`
    such that, avoiding its earlier vertices, its end still has a paradox in front. -/
def LadderInv (Z : Set V) (F : ℕ → V) (M : ℕ) : Prop :=
  IsPathF E F M ∧ (∀ t ≤ M, F t ∈ Z) ∧
    ¬ KernelPerfectOn E (reachIn E (Z \ {x | ∃ t < M, F t = x}) (F M))

/-- One step of the construction in Proposition 5.7 (Lemma 5.6 appended to the path). -/
lemma ladder_extend (hodd : NoOddCycle E) (Z : Set V) (F : ℕ → V) (M : ℕ)
    (hs : LadderInv E Z F M) :
    ∃ (F' : ℕ → V) (M' k : ℕ), LadderInv E Z F' M' ∧ M < M' ∧ M ≤ k ∧ k < M' ∧
      Essential E (F' k) ∧ Prec E (F' k) (F' M') ∧ ∀ t ≤ M, F' t = F t := by
  obtain ⟨hFp, hFZ, hFk⟩ := hs
  have hvZ' : F M ∈ Z \ {x | ∃ t < M, F t = x} := by
    refine ⟨hFZ M le_rfl, ?_⟩
    rintro ⟨t, ht, hFt⟩
    have h' := hFp.2 t M (by omega) le_rfl hFt
    omega
  obtain ⟨f, L, k, hf0, hkL, hfp, hfY, hfk, hpq, hnew⟩ := ladder_step E hodd _ (F M) hvZ' hFk
  have hfZ' : ∀ j ≤ L, f j ∈ Z \ {x | ∃ t < M, F t = x} :=
    fun j hj => reachIn_subset E hvZ' (hfY j hj)
  have hdisj : ∀ i ≤ M, ∀ j ≤ L, F i = f j → i = M ∧ j = 0 := by
    intro i hi j hj hij
    have hiM : i = M := by
      by_contra hne
      exact (hfZ' j hj).2 ⟨i, by omega, hij⟩
    refine ⟨hiM, ?_⟩
    rw [hiM, ← hf0] at hij
    exact (hfp.2 0 j (Nat.zero_le _) hj hij).symm
  have hval : ∀ t, M ≤ t → concatF F f M t = f (t - M) := by
    intro t ht
    obtain ⟨s, rfl⟩ : ∃ s, t = M + s := ⟨t - M, by omega⟩
    rw [concatF_right hf0.symm, Nat.add_sub_cancel_left]
  refine ⟨concatF F f M, M + L, M + k, ⟨concatF_path E hFp hfp hf0.symm hdisj, ?_, ?_⟩,
    by omega, by omega, by omega, ?_, ?_, fun t ht => concatF_left ht⟩
  · intro t ht
    by_cases htM : t ≤ M
    · rw [concatF_left htM]
      exact hFZ t htM
    · rw [hval t (by omega)]
      exact (hfZ' _ (by omega)).1
  · rw [concatF_right hf0.symm]
    intro hkp
    apply hnew
    refine kpOn_mono E hkp (reachIn_mono E ?_ (f L))
    rintro w ⟨⟨hwZ, hwold⟩, hwnew⟩
    refine ⟨hwZ, ?_⟩
    rintro ⟨t, ht, hct⟩
    by_cases htM : t < M
    · rw [concatF_left (by omega)] at hct
      exact hwold ⟨t, htM, hct⟩
    · rw [hval t (by omega)] at hct
      exact hwnew ⟨t - M, by omega, hct⟩
  · rw [hval (M + k) (by omega), Nat.add_sub_cancel_left]
    exact hfk
  · rw [hval (M + k) (by omega), hval (M + L) (by omega), Nat.add_sub_cancel_left,
      Nat.add_sub_cancel_left]
    exact hpq

/-- Proposition 5.7 (ladder rays exist). -/
lemma ladderRays_exist (hodd : NoOddCycle E) (Z : Set V) (h : ¬ KernelPerfectOn E Z) :
    ∃ R, IsLadderRay E R ∧ LiesIn R Z := by
  obtain ⟨C, hCZ, hC⟩ := exists_core E Z h
  obtain ⟨c, hc⟩ := hC.1
  have h0 : ¬ KernelPerfectOn E (reachIn E Z c) := by
    intro hkp
    have hDC : reachIn E C c ⊆ C := reachIn_subset E hc
    apply core_not_kp E (core_succClosed E hC hDC (reachIn_succClosed E hc)
      ⟨c, mem_reachIn_self E C c⟩)
    exact kpOn_mono E hkp (reachIn_mono E hCZ c)
  have hinit : LadderInv E Z (fun _ => c) 0 := by
    refine ⟨⟨fun t ht => absurd ht (Nat.not_lt_zero t), fun i j hi hj _ => by omega⟩,
      fun t _ => hCZ hc, ?_⟩
    intro hkp
    apply h0
    refine kpOn_mono E hkp (reachIn_mono E ?_ c)
    intro w hw
    refine ⟨hw, ?_⟩
    rintro ⟨t, ht, _⟩
    omega
  have hstep : ∀ s : (ℕ → V) × ℕ, LadderInv E Z s.1 s.2 →
      ∃ s' : (ℕ → V) × ℕ, ∃ k : ℕ, LadderInv E Z s'.1 s'.2 ∧ s.2 < s'.2 ∧ s.2 ≤ k ∧
        k < s'.2 ∧ Essential E (s'.1 k) ∧ Prec E (s'.1 k) (s'.1 s'.2) ∧
        ∀ t ≤ s.2, s'.1 t = s.1 t := by
    intro s hs
    obtain ⟨F', M', k, h1, h2, h3, h4, h5, h6, h7⟩ := ladder_extend E hodd Z s.1 s.2 hs
    exact ⟨(F', M'), k, h1, h2, h3, h4, h5, h6, h7⟩
  haveI : Nonempty ((ℕ → V) × ℕ) := ⟨(fun _ => c, 0)⟩
  choose! nxt kf hnxt using hstep
  obtain ⟨S, hS⟩ : ∃ S : ℕ → (ℕ → V) × ℕ, S = seqRec (fun _ => c, 0) (fun _ s => nxt s) :=
    ⟨_, rfl⟩
  have hS0 : S 0 = (fun _ => c, 0) := by rw [hS]; rfl
  have hSsucc : ∀ n, S (n + 1) = nxt (S n) := by intro n; rw [hS]; rfl
  have hinv : ∀ n, LadderInv E Z (S n).1 (S n).2 := by
    intro n
    induction n with
    | zero => rw [hS0]; exact hinit
    | succ n ih => rw [hSsucc]; exact (hnxt (S n) ih).1
  have hstepS : ∀ n, (S n).2 < (S (n + 1)).2 ∧ (S n).2 ≤ kf (S n) ∧ kf (S n) < (S (n + 1)).2 ∧
      Essential E ((S (n + 1)).1 (kf (S n))) ∧
      Prec E ((S (n + 1)).1 (kf (S n))) ((S (n + 1)).1 (S (n + 1)).2) ∧
      ∀ t ≤ (S n).2, (S (n + 1)).1 t = (S n).1 t := by
    intro n
    rw [hSsucc]
    exact (hnxt (S n) (hinv n)).2
  have hM : ∀ n, n ≤ (S n).2 := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      have h1 := (hstepS n).1
      omega
  have hMmono : ∀ n d, (S n).2 ≤ (S (n + d)).2 := by
    intro n d
    induction d with
    | zero => exact le_rfl
    | succ d ih =>
      have h1 := (hstepS (n + d)).1
      show (S n).2 ≤ (S (n + d + 1)).2
      omega
  have hagree : ∀ n d, ∀ t ≤ (S n).2, (S (n + d)).1 t = (S n).1 t := by
    intro n d
    induction d with
    | zero => intro t _; rfl
    | succ d ih =>
      intro t ht
      have h1 := hMmono n d
      show (S (n + d + 1)).1 t = (S n).1 t
      rw [(hstepS (n + d)).2.2.2.2.2 t (by omega)]
      exact ih t ht
  have hagree2 : ∀ a b t, t ≤ (S a).2 → t ≤ (S b).2 → (S a).1 t = (S b).1 t := by
    intro a b t ha hb
    by_cases hab : a ≤ b
    · obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
      exact (hagree a d t ha).symm
    · obtain ⟨d, rfl⟩ : ∃ d, a = b + d := ⟨a - b, by omega⟩
      exact hagree b d t hb
  -- the ray: `R t = (S t).1 t`
  have hRray : IsRay E (fun t => (S t).1 t) := by
    refine ⟨fun i j hij => ?_, fun t => ?_⟩
    · have hm := hM (i + j)
      have h1 : (S (i + j)).1 i = (S i).1 i := hagree2 (i + j) i i (by omega) (hM i)
      have h2 : (S (i + j)).1 j = (S j).1 j := hagree2 (i + j) j j (by omega) (hM j)
      have hij' : (S i).1 i = (S j).1 j := hij
      exact (hinv (i + j)).1.2 i j (by omega) (by omega) (by rw [h1, h2]; exact hij')
    · have hm := hM (t + 1)
      have h1 : (S (t + 1)).1 t = (S t).1 t := hagree2 (t + 1) t t (by omega) (hM t)
      show E ((S t).1 t) ((S (t + 1)).1 (t + 1))
      rw [← h1]
      exact (hinv (t + 1)).1.1 t (by omega)
  refine ⟨fun t => (S t).1 t, isLadderRay_splice E hRray (fun n => kf (S n))
    (fun n => (S (n + 1)).2) (fun n => (hstepS n).2.2.1) (fun n => (hstepS (n + 1)).2.1)
    (fun n => ?_) (fun n => ?_), fun t => (hinv t).2.1 t (hM t)⟩
  · show Essential E ((S (kf (S n))).1 (kf (S n)))
    rw [hagree2 (kf (S n)) (n + 1) (kf (S n)) (hM _) (le_of_lt (hstepS n).2.2.1)]
    exact (hstepS n).2.2.2.1
  · show Prec E ((S (kf (S n))).1 (kf (S n))) ((S ((S (n + 1)).2)).1 ((S (n + 1)).2))
    rw [hagree2 (kf (S n)) (n + 1) (kf (S n)) (hM _) (le_of_lt (hstepS n).2.2.1),
      hagree2 ((S (n + 1)).2) (n + 1) ((S (n + 1)).2) (hM _) le_rfl]
    exact (hstepS n).2.2.2.2.1

/-! ## §6. Gates and the diagonal comb -/

/-! ### Walks in `G − F` and their parity -/

lemma walkN_mono {R R' : V → V → Prop} (hR : ∀ a b, R a b → R' a b) {u w : V} {n : ℕ}
    (h : WalkN R u w n) : WalkN R' u w n := by
  induction h with
  | nil v => exact WalkN.nil v
  | cons huv _ ih => exact WalkN.cons (hR _ _ huv) ih

/-- A walk given as a function. -/
lemma walkN_of_fun {R : V → V → Prop} {f : ℕ → V} (a : ℕ) :
    ∀ d, (∀ t < d, R (f (a + t)) (f (a + t + 1))) → WalkN R (f a) (f (a + d)) d
  | 0, _ => WalkN.nil _
  | d + 1, h => by
    have hw := walkN_of_fun a d (fun t ht => h t (by omega))
    have he : R (f (a + d)) (f (a + d + 1)) := h d (by omega)
    exact walkN_append R hw (WalkN.cons he (WalkN.nil _))

/-- Lemma 2.1(2) in the form used in the gate lemma: a walk in `G − F` between two
    different vertices contains a path of positive length and of the same parity
    (a shortest walk of that parity repeats no vertex, since closed walks are even). -/
lemma walk_path_parity (hodd : NoOddCycle E) (F : Finset V) {u w : V} {n : ℕ}
    (h : WalkN (fun a b => E a b ∧ b ∉ F) u w n) (huw : u ≠ w) :
    ∃ P : List V, P ≠ [] ∧ List.IsChain E (u :: P) ∧ (u :: P).Nodup ∧
      P.getLast? = some w ∧ (∀ x ∈ P, x ∉ F) ∧ P.length % 2 = n % 2 := by
  obtain ⟨f, hf0, hfn, hfe⟩ := walkN_fun (fun a b => E a b ∧ b ∉ F) h
  have hex : ∃ L, ∃ g : ℕ → V, g 0 = u ∧ g L = w ∧
      (∀ t < L, E (g t) (g (t + 1)) ∧ g (t + 1) ∉ F) ∧ L % 2 = n % 2 :=
    ⟨n, f, hf0, hfn, hfe, rfl⟩
  obtain ⟨g, hg0, hgL, hge, hgpar⟩ := Nat.find_spec hex
  set L := Nat.find hex with hL
  have key : ∀ a b, a < b → b ≤ L → g a = g b → False := by
    intro a b hab hbL hgab
    -- the closed walk from position `a` to `b` is even
    have hcw : WalkN E (g a) (g (a + (b - a))) (b - a) :=
      walkN_of_fun a (b - a) (fun t ht => (hge (a + t) (by omega)).1)
    rw [show a + (b - a) = b by omega, ← hgab] at hcw
    have hev := closedWalk_even E hodd hcw
    apply Nat.find_min hex (show L - (b - a) < L by omega)
    refine ⟨fun t => if t ≤ a then g t else g (t + (b - a)), ?_, ?_, ?_, ?_⟩
    · show (if 0 ≤ a then g 0 else g (0 + (b - a))) = u
      rw [ite_eq_left (Nat.zero_le a)]
      exact hg0
    · show (if L - (b - a) ≤ a then g (L - (b - a)) else g (L - (b - a) + (b - a))) = w
      by_cases hc : L - (b - a) ≤ a
      · rw [ite_eq_left hc, show L - (b - a) = a by omega, hgab, show b = L by omega]
        exact hgL
      · rw [ite_eq_right hc, show L - (b - a) + (b - a) = L by omega]
        exact hgL
    · intro t ht
      show E (if t ≤ a then g t else g (t + (b - a)))
          (if t + 1 ≤ a then g (t + 1) else g (t + 1 + (b - a))) ∧
        (if t + 1 ≤ a then g (t + 1) else g (t + 1 + (b - a))) ∉ F
      by_cases h1 : t + 1 ≤ a
      · rw [ite_eq_left (show t ≤ a by omega), ite_eq_left h1]
        exact hge t (by omega)
      · by_cases h2 : t ≤ a
        · rw [ite_eq_left h2, ite_eq_right h1, show t + 1 + (b - a) = b + 1 by omega,
            show t = a by omega, hgab]
          exact hge b (by omega)
        · rw [ite_eq_right h2, ite_eq_right h1,
            show t + 1 + (b - a) = t + (b - a) + 1 by omega]
          exact hge _ (by omega)
    · obtain ⟨r, hr⟩ := hev
      omega
  have hinj : ∀ i j, 0 < i → i ≤ 0 + L → 0 < j → j ≤ 0 + L → g i = g j → i = j := by
    intro i j _ hi _ hj hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key i j h (by omega) hij
    · exact key j i h (by omega) hij.symm
  have hLpos : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · exact (huw (by rw [← hg0, ← hgL, h0])).elim
    · exact h0
  obtain ⟨M, hM⟩ : ∃ M, L = M + 1 := ⟨L - 1, by omega⟩
  refine ⟨pathList g 0 L, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hM]
    exact List.cons_ne_nil _ _
  · rw [← hg0]
    exact pathList_chain E g 0 L (fun t ht => by simpa using (hge t ht).1)
  · rw [← hg0, List.nodup_cons]
    refine ⟨fun hmem => ?_, pathList_nodup g 0 L hinj⟩
    obtain ⟨t, ht1, htL, hgt⟩ := pathList_mem g 0 L (g 0) hmem
    rw [zero_add] at hgt
    exact key 0 t (by omega) htL hgt
  · rw [hM, pathList_getLast g 0 M, show 0 + M + 1 = L by omega, hgL]
  · intro x hx
    obtain ⟨t, ht1, htL, hxt⟩ := pathList_mem g 0 L x hx
    have h1 := (hge (t - 1) (by omega)).2
    rw [show t - 1 + 1 = t by omega] at h1
    rw [hxt, zero_add]
    exact h1
  · rw [pathList_length]
    exact hgpar

/-- Lemma 6.1 (gate). -/
lemma gate (hodd : NoOddCycle E) {Z : Set V} (hZ : FinitePort E Z)
    {L : ℕ → V} (hL : IsRay E L) {q : V} (hqZ : q ∈ Z) (hq : Essential E q)
    (hqL : ¬ ParityDominates E q L) (A : Finset V) (hqA : q ∉ A) :
    ∃ Z' : Set V, Z' ⊆ Z \ ↑A ∧ FinitePort E Z' ∧
      (∀ z ∈ Z', ReflTransGen (restrict E (Z \ ↑A)) q z) ∧
      (∀ S, IsRay E S → LiesIn S Z' → ¬ Feeds E S L) ∧
      ∃ R, IsLadderRay E R ∧ LiesIn R Z' := by
  -- the gate `F0` and the level `m0`, by the parity cut criterion (Lemma 3.2)
  have hcut := mt (parityDominates_iff_cut E q L hL).mpr hqL
  push_neg at hcut
  obtain ⟨F0, hqF0, m0, hsame⟩ := hcut
  -- a tail beyond `q`
  obtain ⟨m1, hm1⟩ := exists_tail_avoid hL.1 {q}
  obtain ⟨m', hm'⟩ : ∃ m', m' = m0 + m1 := ⟨_, rfl⟩
  -- enlarge the gate by `A`
  obtain ⟨F, hF⟩ : ∃ F : Finset V, F = F0 ∪ A := ⟨_, rfl⟩
  have hqF : q ∉ F := by
    rw [hF, Finset.mem_union]
    rintro (h | h)
    · exact hqF0 h
    · exact hqA h
  have hAF : ∀ x, x ∈ A → x ∈ F := fun x hx => by rw [hF]; exact Finset.mem_union_right _ hx
  have hF0F : ∀ x, x ∉ F → x ∉ F0 :=
    fun x hx h => hx (by rw [hF]; exact Finset.mem_union_left _ h)
  -- all walks in `G − F` from `q` to the tail have the same type
  have hWT : ∀ j1 j2 n1 n2, m' ≤ j1 → m' ≤ j2 →
      WalkN (fun a b => E a b ∧ b ∉ F) q (L j1) n1 →
      WalkN (fun a b => E a b ∧ b ∉ F) q (L j2) n2 → (n1 + j1) % 2 = (n2 + j2) % 2 := by
    intro j1 j2 n1 n2 hj1 hj2 w1 w2
    have hne1 : q ≠ L j1 := fun h =>
      hm1 j1 (by omega) (by rw [← h]; exact Finset.mem_singleton_self q)
    have hne2 : q ≠ L j2 := fun h =>
      hm1 j2 (by omega) (by rw [← h]; exact Finset.mem_singleton_self q)
    obtain ⟨P1, h11, h12, h13, h14, h15, h16⟩ := walk_path_parity E hodd F w1 hne1
    obtain ⟨P2, h21, h22, h23, h24, h25, h26⟩ := walk_path_parity E hodd F w2 hne2
    have hs := hsame P1 P2 j1 j2 ⟨h11, h12, h13, h14, fun x hx => hF0F x (h15 x hx)⟩
      ⟨h21, h22, h23, h24, fun x hx => hF0F x (h25 x hx)⟩ (by omega) (by omega)
    omega
  -- `Z*`: the cone at `q` in `G[Z] − F`
  have hqZF : q ∈ Z \ ↑F := ⟨hqZ, hqF⟩
  have hZsfp : FinitePort E (reachIn E (Z \ ↑F) q) := cone_finitePort E hZ F hqZ hqF
  have hZsnkp : ¬ KernelPerfectOn E (reachIn E (Z \ ↑F) q) := essential_cone E hq hZ hqZ F hqF
  have hZsZ : reachIn E (Z \ ↑F) q ⊆ Z \ ↑F := reachIn_subset E hqZF
  -- `A*`: the part that can still reach the tail; `B` the rest
  obtain ⟨As, hAs⟩ : ∃ As : Set V, As = {x | x ∈ reachIn E (Z \ ↑F) q ∧
      ∃ j, m' ≤ j ∧ ReachAvoiding E F x (L j)} := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Set V, B = reachIn E (Z \ ↑F) q \ As := ⟨_, rfl⟩
  -- `A*` is bipartite: colour by the parity of walks from `q`
  have hmono : ∀ u1 u2, restrict E (Z \ ↑F) u1 u2 → E u1 u2 ∧ u2 ∉ F :=
    fun u1 u2 h => ⟨h.1, h.2.2.2⟩
  have hpar : ∀ x ∈ As, ∀ a b, WalkN (restrict E (Z \ ↑F)) q x a →
      WalkN (restrict E (Z \ ↑F)) q x b → a % 2 = b % 2 := by
    intro x hx a b wa wb
    rw [hAs] at hx
    obtain ⟨-, j, hj, hxj⟩ := hx
    obtain ⟨c, wc⟩ := walkN_of_rtg (fun a b => E a b ∧ b ∉ F) hxj.2
    have h1 := walkN_append (fun a b => E a b ∧ b ∉ F) (walkN_mono hmono wa) wc
    have h2 := walkN_append (fun a b => E a b ∧ b ∉ F) (walkN_mono hmono wb) wc
    have h3 := hWT j j (a + c) (b + c) hj hj h1 h2
    omega
  have hcol : ∀ x ∈ As, ∀ a, WalkN (restrict E (Z \ ↑F)) q x a →
      (decide (∃ n, Odd n ∧ WalkN (restrict E (Z \ ↑F)) q x n) = true ↔ Odd a) := by
    intro x hx a wa
    constructor
    · intro h
      obtain ⟨n, hn, wn⟩ := of_decide_eq_true h
      have h1 := hpar x hx n a wn wa
      rw [Nat.odd_iff] at hn ⊢
      omega
    · intro ha
      exact decide_eq_true ⟨a, ha, wa⟩
  have hbip : IsBipartiteOn E
      (fun x => decide (∃ n, Odd n ∧ WalkN (restrict E (Z \ ↑F)) q x n)) As := by
    intro x hx y hy hxy hc
    have hxZs : x ∈ reachIn E (Z \ ↑F) q := by rw [hAs] at hx; exact hx.1
    have hyZs : y ∈ reachIn E (Z \ ↑F) q := by rw [hAs] at hy; exact hy.1
    have hx' : ReflTransGen (restrict E (Z \ ↑F)) q x := hxZs
    obtain ⟨a, wa⟩ := walkN_of_rtg (restrict E (Z \ ↑F)) hx'
    have wb : WalkN (restrict E (Z \ ↑F)) q y (a + 1) :=
      walkN_append (restrict E (Z \ ↑F)) wa
        (WalkN.cons ⟨hxy, hZsZ hxZs, hZsZ hyZs⟩ (WalkN.nil y))
    have hcx := hcol x hx a wa
    have hcy := hcol y hy (a + 1) wb
    have hc' : decide (∃ n, Odd n ∧ WalkN (restrict E (Z \ ↑F)) q x n) =
        decide (∃ n, Odd n ∧ WalkN (restrict E (Z \ ↑F)) q y n) := hc
    rw [hc'] at hcx
    have hkey : Odd a ↔ Odd (a + 1) := hcx.symm.trans hcy
    rw [Nat.odd_add_one] at hkey
    exact iff_not_self hkey
  have hAsKP : KernelPerfectOn E As := bipartite_kernelPerfectOn E _ As hbip
  -- `B` is closed
  have hBZs : B ⊆ reachIn E (Z \ ↑F) q := by
    rw [hB]
    exact sdiff_subset
  have hBcl : SuccClosedIn E (reachIn E (Z \ ↑F) q) B := by
    intro x hx y hy hxy
    rw [hB] at hx ⊢
    refine ⟨hy, fun hyA => hx.2 ?_⟩
    rw [hAs] at hyA ⊢
    obtain ⟨-, j, hj, hyj⟩ := hyA
    refine ⟨hx.1, j, hj, ?_⟩
    have hxF : x ∉ F := (hZsZ hx.1).2
    have hyF : y ∉ F := (hZsZ hy).2
    refine ⟨hxF, ReflTransGen.head ?_ hyj.2⟩
    exact ⟨hxy, hyF⟩
  -- the paradox is in `B`
  have hBnkp : ¬ KernelPerfectOn E B := by
    intro hBkp
    apply hZsnkp
    refine two_pieces E hBZs hBcl hBkp (kpOn_mono E hAsKP ?_)
    rintro x ⟨hxZ, hxB⟩
    by_contra hxA
    exact hxB (by rw [hB]; exact ⟨hxZ, hxA⟩)
  have hBfp : FinitePort E B := by
    refine hZsfp.subset ?_
    rintro w ⟨hwB, x, hx, hxw⟩
    exact ⟨fun hwZs => hwB (hBcl x hx w hwZs hxw), x, hBZs hx, hxw⟩
  refine ⟨B, ?_, hBfp, ?_, ?_, ladderRays_exist E hodd B hBnkp⟩
  · intro x hx
    have hxF := hZsZ (hBZs hx)
    exact ⟨hxF.1, fun hxA => hxF.2 (hAF x hxA)⟩
  · intro x hx
    have hsub : Z \ ↑F ⊆ Z \ ↑A := fun y hy => ⟨hy.1, fun hyA => hy.2 (hAF y hyA)⟩
    exact reachIn_mono E hsub q (hBZs hx)
  · intro S hS hSB hfeed
    obtain ⟨a, b, -, hb, hab⟩ := feeds_tails E hfeed F 0 m'
    have hSa := hSB a
    rw [hB] at hSa
    apply hSa.2
    rw [hAs]
    exact ⟨hSa.1, b, hb, hab⟩

/-- The invariant of the comb construction (Lemma 6.2) at stage `i`: `Zp = Z_{i-1}`,
    `Zc = Z_i`, and the path `F 0, …, F M` is `R_{i-1}`, ending at `q_{i-1}`. -/
def CombInv (Z Zp Zc : Set V) (F : ℕ → V) (M : ℕ) : Prop :=
  FinitePort E Zc ∧ (∃ R, IsLadderRay E R ∧ LiesIn R Zc) ∧ IsPathF E F M ∧
    (∀ t ≤ M, F t ∈ Z) ∧ Zc ⊆ Zp ∧ Zp ⊆ Z ∧ F M ∈ Zp ∧
    ∀ z ∈ Zc, z ∈ reachIn E (Zp \ {x | ∃ t < M, F t = x}) (F M)

/-- One stage of the diagonal comb: the tooth, the entry, along the tooth, the gate. -/
lemma comb_step (hS : IsParitySafe E) (Z Zp Zc : Set V) (F : ℕ → V) (M : ℕ)
    (hinv : CombInv E Z Zp Zc F M) (ei : Set (ℕ → V))
    (hei : ∃ R, IsRay E R ∧ ei = endOf E R) :
    ∃ (Z' : Set V) (F' : ℕ → V) (M' ap kp : ℕ), CombInv E Z Zc Z' F' M' ∧ Z' ⊆ Zc ∧
      M ≤ ap ∧ ap < kp ∧ kp < M' ∧ Essential E (F' kp) ∧ Prec E (F' kp) (F' M') ∧
      (∀ t ≤ M, F' t = F t) ∧ (∀ t, M < t → t ≤ M' → F' t ∈ Zp) ∧
      (∀ t, ap ≤ t → t ≤ M' → F' t ∈ Zc) ∧
      (∀ S, IsLadderRay E S → LiesIn S Z' → S ∉ ei) := by
  obtain ⟨hZcfp, hZclad, hFp, hFZ, hZcZp, hZpZ, hFMZp, hentry⟩ := hinv
  obtain ⟨R0, hR0, hei'⟩ := hei
  -- the tooth `L`: a ladder ray of `e_i` lying in `Zc` if there is one
  obtain ⟨L, hLlad, hLZc, hLe⟩ : ∃ L, IsLadderRay E L ∧ LiesIn L Zc ∧
      ((∃ R, IsLadderRay E R ∧ LiesIn R Zc ∧ R ∈ ei) → L ∈ ei) := by
    by_cases hlive : ∃ R, IsLadderRay E R ∧ LiesIn R Zc ∧ R ∈ ei
    · obtain ⟨R, h1, h2, h3⟩ := hlive
      exact ⟨R, h1, h2, fun _ => h3⟩
    · obtain ⟨R, h1, h2⟩ := hZclad
      exact ⟨R, h1, h2, fun h => absurd h hlive⟩
  obtain ⟨hLr, b, hb, hbess, hbprec⟩ := hLlad
  -- the entry: a path `g` from `F M` to `L`, avoiding the earlier vertices,
  -- stopped at its first vertex `g i0 = L s0` on `L`
  obtain ⟨W, hW⟩ : ∃ W : Set V, W = Zp \ {x | ∃ t < M, F t = x} := ⟨_, rfl⟩
  have hFMW : F M ∈ W := by
    rw [hW]
    refine ⟨hFMZp, ?_⟩
    rintro ⟨t, ht, hFt⟩
    have h' := hFp.2 t M (by omega) le_rfl hFt
    omega
  have hentry' : ∀ z ∈ Zc, z ∈ reachIn E W (F M) := by rw [hW]; exact hentry
  have hZcW : ∀ z ∈ Zc, z ∈ W := fun z hz => reachIn_subset E hFMW (hentry' z hz)
  have hWZp : W ⊆ Zp := by rw [hW]; exact sdiff_subset
  obtain ⟨g, Lg, hg0, hgL, hgp, hgW⟩ := exists_pathF E hFMW (hentry' (L 0) (hLZc 0))
  have hexL : ∃ i, i ≤ Lg ∧ ∃ s, g i = L s := ⟨Lg, le_rfl, 0, hgL⟩
  obtain ⟨hi0L, s0, hs0⟩ := Nat.find_spec hexL
  set i0 := Nat.find hexL with hi0
  have hbefore : ∀ t < i0, ∀ s, g t ≠ L s :=
    fun t ht s h => Nat.find_min hexL ht ⟨by omega, s, h⟩
  -- along the tooth: consecutive checkpoints `p = L (b k)`, `q = L (b (k+1))` beyond
  -- `L s0`, where `q` does not parity-dominate `L`
  have hfin : {n | ParityDominates E (L n) L}.Finite := Set.not_infinite.mp (hS.2 L hLr)
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ∈ {n | ParityDominates E (L n) L}, n < N := by
    obtain ⟨N, hN⟩ := hfin.bddAbove
    exact ⟨N + 1, fun n hn => Nat.lt_succ_of_le (hN hn)⟩
  obtain ⟨k, hk⟩ : ∃ k, k = s0 + N + 1 := ⟨_, rfl⟩
  have hbk : k ≤ b k := hb.id_le k
  have hbk1 : k + 1 ≤ b (k + 1) := hb.id_le (k + 1)
  have hbkk : b k < b (k + 1) := hb (show k < k + 1 by omega)
  have hqPD : ¬ ParityDominates E (L (b (k + 1))) L := fun h => by
    have h' := hN (b (k + 1)) h
    omega
  -- the new path: `F`, then `g` up to `i0`, then `L` from `s0` to `b (k+1)`
  have hπ : IsPathF E g i0 := isPathF_prefix E hgp hi0L
  have hFg : F M = g 0 := hg0.symm
  have hd1 : ∀ i ≤ M, ∀ j ≤ i0, F i = g j → i = M ∧ j = 0 := by
    intro i hi j hj hij
    have hgjW := hgW j (by omega)
    have hiM : i = M := by
      by_contra hne
      rw [hW] at hgjW
      exact hgjW.2 ⟨i, by omega, hij⟩
    refine ⟨hiM, ?_⟩
    rw [hiM, hFg] at hij
    exact (hgp.2 0 j (Nat.zero_le _) (by omega) hij).symm
  have hf1 : IsPathF E (concatF F g M) (M + i0) := concatF_path E hFp hπ hFg hd1
  have hseg : IsPathF E (fun j => L (s0 + j)) (b (k + 1) - s0) :=
    ⟨fun t _ => hLr.2 (s0 + t), fun i j _ _ hij => by have h' := hLr.1 hij; omega⟩
  have hf1end : concatF F g M (M + i0) = L s0 := by rw [concatF_right hFg, hs0]
  have hval1 : ∀ t ≤ M + i0, (t < M ∧ concatF F g M t = F t) ∨
      (M ≤ t ∧ concatF F g M t = g (t - M)) := by
    intro t ht
    by_cases h : t < M
    · exact Or.inl ⟨h, concatF_left (by omega)⟩
    · refine Or.inr ⟨by omega, ?_⟩
      obtain ⟨s, rfl⟩ : ∃ s, t = M + s := ⟨t - M, by omega⟩
      rw [concatF_right hFg, Nat.add_sub_cancel_left]
  have hd2 : ∀ i ≤ M + i0, ∀ j ≤ b (k + 1) - s0,
      concatF F g M i = L (s0 + j) → i = M + i0 ∧ j = 0 := by
    intro i hi j hj hij
    have hLW : L (s0 + j) ∈ W := hZcW _ (hLZc _)
    rcases hval1 i hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2] at hij
      rw [hW] at hLW
      exact (hLW.2 ⟨i, h1, hij⟩).elim
    · rw [h2] at hij
      by_cases hlt : i - M < i0
      · exact (hbefore (i - M) hlt (s0 + j) hij).elim
      · have he : i - M = i0 := by omega
        rw [he, hs0] at hij
        have h' := hLr.1 hij
        exact ⟨by omega, by omega⟩
  have hF'p : IsPathF E (concatF (concatF F g M) (fun j => L (s0 + j)) (M + i0))
      (M + i0 + (b (k + 1) - s0)) := concatF_path E hf1 hseg hf1end hd2
  have hF'seg : ∀ j, concatF (concatF F g M) (fun j => L (s0 + j)) (M + i0) (M + i0 + j) =
      L (s0 + j) := fun j => concatF_right hf1end j
  have hF'kp : concatF (concatF F g M) (fun j => L (s0 + j)) (M + i0)
      (M + i0 + (b k - s0)) = L (b k) := by
    rw [hF'seg, show s0 + (b k - s0) = b k by omega]
  have hF'M' : concatF (concatF F g M) (fun j => L (s0 + j)) (M + i0)
      (M + i0 + (b (k + 1) - s0)) = L (b (k + 1)) := by
    rw [hF'seg, show s0 + (b (k + 1) - s0) = b (k + 1) by omega]
  have hval : ∀ t ≤ M + i0 + (b (k + 1) - s0),
      (t ≤ M + i0 ∧ concatF (concatF F g M) (fun j => L (s0 + j)) (M + i0) t =
        concatF F g M t) ∨
      (M + i0 ≤ t ∧ concatF (concatF F g M) (fun j => L (s0 + j)) (M + i0) t =
        L (s0 + (t - (M + i0)))) := by
    intro t ht
    by_cases h : t ≤ M + i0
    · exact Or.inl ⟨h, concatF_left h⟩
    · refine Or.inr ⟨by omega, ?_⟩
      obtain ⟨s, rfl⟩ : ∃ s, t = M + i0 + s := ⟨t - (M + i0), by omega⟩
      rw [hF'seg, Nat.add_sub_cancel_left]
  -- the gate
  obtain ⟨A, hA⟩ : ∃ A : Finset V, A = (Finset.range (M + i0 + (b (k + 1) - s0))).image
      (concatF (concatF F g M) (fun j => L (s0 + j)) (M + i0)) := ⟨_, rfl⟩
  have hmemA : ∀ y, y ∈ A ↔ ∃ t, t < M + i0 + (b (k + 1) - s0) ∧
      concatF (concatF F g M) (fun j => L (s0 + j)) (M + i0) t = y := by
    intro y
    rw [hA, Finset.mem_image]
    simp only [Finset.mem_range]
  have hqA : L (b (k + 1)) ∉ A := by
    intro h
    obtain ⟨t, ht, hFt⟩ := (hmemA _).mp h
    rw [← hF'M'] at hFt
    have h' := hF'p.2 t _ (by omega) le_rfl hFt
    omega
  obtain ⟨Z', hZ'sub, hZ'fp, hZ'reach, hZ'feed, hZ'lad⟩ :=
    gate E hS.1 hZcfp hLr (hLZc _) (hbess (k + 1)) hqPD A hqA
  refine ⟨Z', concatF (concatF F g M) (fun j => L (s0 + j)) (M + i0),
    M + i0 + (b (k + 1) - s0), M + i0, M + i0 + (b k - s0),
    ⟨hZ'fp, hZ'lad, hF'p, ?_, fun z hz => (hZ'sub hz).1, hZcZp.trans hZpZ, ?_, ?_⟩,
    fun z hz => (hZ'sub hz).1, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the new path lies in `Z`
    intro t ht
    rcases hval t ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]
      rcases hval1 t h1 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [h4]
        exact hFZ t (by omega)
      · rw [h4]
        exact hZpZ (hWZp (hgW _ (by omega)))
    · rw [h2]
      exact hZpZ (hZcZp (hLZc _))
  · rw [hF'M']
    exact hLZc _
  · -- the entry condition for the next stage, from Lemma 6.1(1)
    rw [hF'M']
    intro z hz
    have hz' : z ∈ reachIn E (Zc \ ↑A) (L (b (k + 1))) := hZ'reach z hz
    have hsub : Zc \ ↑A ⊆ Zc \ {x | ∃ t < M + i0 + (b (k + 1) - s0),
        concatF (concatF F g M) (fun j => L (s0 + j)) (M + i0) t = x} := by
      intro w hw
      refine ⟨hw.1, ?_⟩
      rintro ⟨t, ht, hFt⟩
      exact hw.2 ((hmemA w).mpr ⟨t, ht, hFt⟩)
    exact reachIn_mono E hsub _ hz'
  · rw [hF'kp]
    exact hbess k
  · rw [hF'kp, hF'M']
    exact hbprec k (k + 1) (by omega)
  · intro t ht
    rw [concatF_left (show t ≤ M + i0 by omega), concatF_left ht]
  · intro t ht1 ht2
    rcases hval t ht2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]
      rcases hval1 t h1 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact absurd ht1 (by omega)
      · rw [h4]
        exact hWZp (hgW _ (by omega))
    · rw [h2]
      exact hZcZp (hLZc _)
  · intro t ht1 ht2
    obtain ⟨s, rfl⟩ : ∃ s, t = M + i0 + s := ⟨t - (M + i0), by omega⟩
    rw [hF'seg]
    exact hLZc _
  · -- (2): a ladder ray in `Z'` of `e_i` would feed the tooth, which the gate excludes
    intro S hSlad hSZ' hSe
    have hLe' := hLe ⟨S, hSlad, fun n => (hZ'sub (hSZ' n)).1, hSe⟩
    rw [hei'] at hSe hLe'
    exact hZ'feed S hSlad.1 hSZ' (feeds_trans E hR0 hSe.2.2 hLe'.2.1)

/-- Lemma 6.2 (diagonal comb). The ends `e i` are given as `≈`-classes. -/
lemma diagonal_comb (hS : IsParitySafe E) (Z : Set V) (hZ : FinitePort E Z)
    (hL : ∃ R, IsLadderRay E R ∧ LiesIn R Z)
    (e : ℕ → Set (ℕ → V)) (he : ∀ i, ∃ R, IsRay E R ∧ e i = endOf E R) :
    ∃ (Zs : ℕ → Set V) (R : ℕ → V),
      Zs 0 = Z ∧ (∀ i, FinitePort E (Zs i)) ∧ (∀ i, Zs (i + 1) ⊆ Zs i) ∧
      IsLadderRay E R ∧ LiesIn R Z ∧
      (∀ i, ∃ m, LiesIn (fun n => R (m + n)) (Zs i)) ∧
      (∀ i S, IsLadderRay E S → LiesIn S (Zs (i + 1)) → S ∉ e i) := by
  obtain ⟨R0, hR0, hR0Z⟩ := hL
  have hv0Z : R0 0 ∈ Z := hR0Z 0
  have he0 : R0 0 ∉ (∅ : Finset V) := by simp
  -- the initial stage: `Zp = Z`, `Zc` the cone at `R0 0` in `G[Z]`, and the trivial path
  have hinit : CombInv E Z Z (reachIn E (Z \ ↑(∅ : Finset V)) (R0 0)) (fun _ => R0 0) 0 := by
    refine ⟨cone_finitePort E hZ ∅ hv0Z he0, ⟨R0, hR0, ?_⟩,
      ⟨fun t ht => absurd ht (Nat.not_lt_zero t), fun i j hi hj _ => by omega⟩,
      fun _ _ => hv0Z, ?_, subset_rfl, hv0Z, ?_⟩
    · intro n
      induction n with
      | zero => exact mem_reachIn_self E _ _
      | succ n ih =>
        have ih' : ReflTransGen (restrict E (Z \ ↑(∅ : Finset V))) (R0 0) (R0 n) := ih
        have h : ReflTransGen (restrict E (Z \ ↑(∅ : Finset V))) (R0 0) (R0 (n + 1)) := by
          refine ReflTransGen.tail ih' ?_
          exact ⟨hR0.1.2 n, ⟨hR0Z n, by simp⟩, ⟨hR0Z (n + 1), by simp⟩⟩
        exact h
    · intro z hz
      have hv : R0 0 ∈ Z \ ↑(∅ : Finset V) := ⟨hv0Z, by simp⟩
      exact (reachIn_subset E hv hz).1
    · intro z hz
      refine reachIn_mono E ?_ (R0 0) hz
      intro w hw
      refine ⟨hw.1, ?_⟩
      rintro ⟨t, ht, _⟩
      omega
  -- iterate the stages
  have hstep : ∀ (n : ℕ) (s : Set V × Set V × (ℕ → V) × ℕ),
      CombInv E Z s.1 s.2.1 s.2.2.1 s.2.2.2 →
      ∃ s' : Set V × Set V × (ℕ → V) × ℕ, ∃ ap kp : ℕ,
        s'.1 = s.2.1 ∧ CombInv E Z s'.1 s'.2.1 s'.2.2.1 s'.2.2.2 ∧ s'.2.1 ⊆ s.2.1 ∧
        s.2.2.2 ≤ ap ∧ ap < kp ∧ kp < s'.2.2.2 ∧ Essential E (s'.2.2.1 kp) ∧
        Prec E (s'.2.2.1 kp) (s'.2.2.1 s'.2.2.2) ∧ (∀ t ≤ s.2.2.2, s'.2.2.1 t = s.2.2.1 t) ∧
        (∀ t, s.2.2.2 < t → t ≤ s'.2.2.2 → s'.2.2.1 t ∈ s.1) ∧
        (∀ t, ap ≤ t → t ≤ s'.2.2.2 → s'.2.2.1 t ∈ s.2.1) ∧
        (∀ S, IsLadderRay E S → LiesIn S s'.2.1 → S ∉ e n) := by
    intro n s hs
    obtain ⟨Z', F', M', ap, kp, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
      comb_step E hS Z s.1 s.2.1 s.2.2.1 s.2.2.2 hs (e n) (he n)
    exact ⟨(s.2.1, Z', F', M'), ap, kp, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  haveI : Nonempty (Set V × Set V × (ℕ → V) × ℕ) :=
    ⟨(Z, reachIn E (Z \ ↑(∅ : Finset V)) (R0 0), fun _ => R0 0, 0)⟩
  choose! nxt apf kpf hnxt using hstep
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ → Set V × Set V × (ℕ → V) × ℕ,
      Q = seqRec (Z, reachIn E (Z \ ↑(∅ : Finset V)) (R0 0), fun _ => R0 0, 0)
        (fun n s => nxt n s) := ⟨_, rfl⟩
  have hQ0 : Q 0 = (Z, reachIn E (Z \ ↑(∅ : Finset V)) (R0 0), fun _ => R0 0, 0) := by
    rw [hQ]; rfl
  have hQsucc : ∀ n, Q (n + 1) = nxt n (Q n) := by intro n; rw [hQ]; rfl
  have hinv : ∀ n, CombInv E Z (Q n).1 (Q n).2.1 (Q n).2.2.1 (Q n).2.2.2 := by
    intro n
    induction n with
    | zero => rw [hQ0]; exact hinit
    | succ n ih => rw [hQsucc]; exact (hnxt n (Q n) ih).2.1
  have hst : ∀ n, (Q (n + 1)).1 = (Q n).2.1 ∧
      CombInv E Z (Q (n + 1)).1 (Q (n + 1)).2.1 (Q (n + 1)).2.2.1 (Q (n + 1)).2.2.2 ∧
      (Q (n + 1)).2.1 ⊆ (Q n).2.1 ∧
      (Q n).2.2.2 ≤ apf n (Q n) ∧ apf n (Q n) < kpf n (Q n) ∧
      kpf n (Q n) < (Q (n + 1)).2.2.2 ∧ Essential E ((Q (n + 1)).2.2.1 (kpf n (Q n))) ∧
      Prec E ((Q (n + 1)).2.2.1 (kpf n (Q n))) ((Q (n + 1)).2.2.1 (Q (n + 1)).2.2.2) ∧
      (∀ t ≤ (Q n).2.2.2, (Q (n + 1)).2.2.1 t = (Q n).2.2.1 t) ∧
      (∀ t, (Q n).2.2.2 < t → t ≤ (Q (n + 1)).2.2.2 → (Q (n + 1)).2.2.1 t ∈ (Q n).1) ∧
      (∀ t, apf n (Q n) ≤ t → t ≤ (Q (n + 1)).2.2.2 → (Q (n + 1)).2.2.1 t ∈ (Q n).2.1) ∧
      (∀ S, IsLadderRay E S → LiesIn S (Q (n + 1)).2.1 → S ∉ e n) := by
    intro n
    rw [hQsucc]
    exact hnxt n (Q n) (hinv n)
  -- positions grow
  have hM : ∀ n, n ≤ (Q n).2.2.2 := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      obtain ⟨-, -, -, h1, h2, h3, -⟩ := hst n
      omega
  have hMmono : ∀ n d, (Q n).2.2.2 ≤ (Q (n + d)).2.2.2 := by
    intro n d
    induction d with
    | zero => exact le_rfl
    | succ d ih =>
      obtain ⟨-, -, -, h1, h2, h3, -⟩ := hst (n + d)
      show (Q n).2.2.2 ≤ (Q (n + d + 1)).2.2.2
      omega
  have hagree : ∀ n d, ∀ t ≤ (Q n).2.2.2, (Q (n + d)).2.2.1 t = (Q n).2.2.1 t := by
    intro n d
    induction d with
    | zero => intro t _; rfl
    | succ d ih =>
      intro t ht
      have h1 := hMmono n d
      obtain ⟨-, -, -, -, -, -, -, -, hagr, -⟩ := hst (n + d)
      show (Q (n + d + 1)).2.2.1 t = (Q n).2.2.1 t
      rw [hagr t (by omega)]
      exact ih t ht
  have hagree2 : ∀ a b t, t ≤ (Q a).2.2.2 → t ≤ (Q b).2.2.2 →
      (Q a).2.2.1 t = (Q b).2.2.1 t := by
    intro a b t ha hb
    by_cases hab : a ≤ b
    · obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
      exact (hagree a d t ha).symm
    · obtain ⟨d, rfl⟩ : ∃ d, a = b + d := ⟨a - b, by omega⟩
      exact hagree b d t hb
  have hZcmono : ∀ a d, (Q (a + d)).2.1 ⊆ (Q a).2.1 := by
    intro a d
    induction d with
    | zero => exact subset_rfl
    | succ d ih => exact (hst (a + d)).2.2.1.trans ih
  -- the spine `R t = (Q t).2.2.1 t`
  have hRray : IsRay E (fun t => (Q t).2.2.1 t) := by
    refine ⟨fun i j hij => ?_, fun t => ?_⟩
    · have hm := hM (i + j)
      have h1 : (Q (i + j)).2.2.1 i = (Q i).2.2.1 i := hagree2 (i + j) i i (by omega) (hM i)
      have h2 : (Q (i + j)).2.2.1 j = (Q j).2.2.1 j := hagree2 (i + j) j j (by omega) (hM j)
      have hij' : (Q i).2.2.1 i = (Q j).2.2.1 j := hij
      exact (hinv (i + j)).2.2.1.2 i j (by omega) (by omega) (by rw [h1, h2]; exact hij')
    · have hm := hM (t + 1)
      have h1 : (Q (t + 1)).2.2.1 t = (Q t).2.2.1 t := hagree2 (t + 1) t t (by omega) (hM t)
      show E ((Q t).2.2.1 t) ((Q (t + 1)).2.2.1 (t + 1))
      rw [← h1]
      exact (hinv (t + 1)).2.2.1.1 t (by omega)
  -- the regions: `Zs 0 = Z`, `Zs (i+1) = (Q (i+1)).2.1`
  obtain ⟨Zs, hZs⟩ : ∃ Zs : ℕ → Set V, Zs = fun i => if i = 0 then Z else (Q i).2.1 :=
    ⟨_, rfl⟩
  have hZs0 : Zs 0 = Z := by rw [hZs]; simp
  have hZsS : ∀ i, Zs (i + 1) = (Q (i + 1)).2.1 := by intro i; rw [hZs]; simp
  refine ⟨Zs, fun t => (Q t).2.2.1 t, hZs0, ?_, ?_, ?_, fun t => (hinv t).2.2.2.1 t (hM t),
    ?_, ?_⟩
  · intro i
    cases i with
    | zero => rw [hZs0]; exact hZ
    | succ i => rw [hZsS]; exact (hinv (i + 1)).1
  · intro i
    cases i with
    | zero =>
      rw [hZsS, hZs0]
      exact (hinv 1).2.2.2.2.1.trans (hinv 1).2.2.2.2.2.1
    | succ i =>
      rw [hZsS, hZsS]
      exact (hst (i + 1)).2.2.1
  · -- the spine is a ladder ray (Lemma 5.5(2))
    refine isLadderRay_splice E hRray (fun n => kpf n (Q n)) (fun n => (Q (n + 1)).2.2.2)
      (fun n => (hst n).2.2.2.2.2.1) (fun n => ?_) (fun n => ?_) (fun n => ?_)
    · obtain ⟨-, -, -, h1, h2, -⟩ := hst (n + 1)
      show (Q (n + 1)).2.2.2 ≤ kpf (n + 1) (Q (n + 1))
      omega
    · obtain ⟨-, -, -, -, -, h3, h4, -⟩ := hst n
      show Essential E ((Q (kpf n (Q n))).2.2.1 (kpf n (Q n)))
      rw [hagree2 (kpf n (Q n)) (n + 1) (kpf n (Q n)) (hM _) (le_of_lt h3)]
      exact h4
    · obtain ⟨-, -, -, -, -, h3, -, h5, -⟩ := hst n
      show Prec E ((Q (kpf n (Q n))).2.2.1 (kpf n (Q n)))
        ((Q ((Q (n + 1)).2.2.2)).2.2.1 ((Q (n + 1)).2.2.2))
      rw [hagree2 (kpf n (Q n)) (n + 1) (kpf n (Q n)) (hM _) (le_of_lt h3),
        hagree2 ((Q (n + 1)).2.2.2) (n + 1) ((Q (n + 1)).2.2.2) (hM _) le_rfl]
      exact h5
  · -- (1): from the entry point of stage `j+1` on, the spine stays in `Z_{j+1}`
    intro i
    cases i with
    | zero =>
      refine ⟨0, fun n => ?_⟩
      show (Q (0 + n)).2.2.1 (0 + n) ∈ Zs 0
      rw [hZs0]
      exact (hinv _).2.2.2.1 _ (hM _)
    | succ j =>
      have hclaim : ∀ d, ∀ t, apf (j + 1) (Q (j + 1)) ≤ t → t ≤ (Q (j + 2 + d)).2.2.2 →
          (Q (j + 2 + d)).2.2.1 t ∈ (Q (j + 1)).2.1 := by
        intro d
        induction d with
        | zero =>
          intro t ht1 ht2
          exact (hst (j + 1)).2.2.2.2.2.2.2.2.2.2.1 t ht1 ht2
        | succ d ih =>
          intro t ht1 ht2
          obtain ⟨-, -, -, -, -, -, -, -, hagr, hnew, -⟩ := hst (j + 2 + d)
          show (Q (j + 2 + d + 1)).2.2.1 t ∈ (Q (j + 1)).2.1
          by_cases hle : t ≤ (Q (j + 2 + d)).2.2.2
          · rw [hagr t hle]
            exact ih t ht1 hle
          · have hin := hnew t (by omega) ht2
            have hZpeq : (Q (j + 2 + d)).1 = (Q (j + 1 + d)).2.1 := by
              have h1 := (hst (j + 1 + d)).1
              rwa [show j + 1 + d + 1 = j + 2 + d by omega] at h1
            rw [hZpeq] at hin
            exact hZcmono (j + 1) d hin
      refine ⟨apf (j + 1) (Q (j + 1)), fun n => ?_⟩
      show (Q (apf (j + 1) (Q (j + 1)) + n)).2.2.1 (apf (j + 1) (Q (j + 1)) + n) ∈ Zs (j + 1)
      rw [hZsS]
      obtain ⟨T, hT⟩ : ∃ T, T = apf (j + 1) (Q (j + 1)) + n := ⟨_, rfl⟩
      rw [← hT]
      have hm := hM (j + 2 + T)
      rw [hagree2 T (j + 2 + T) T (hM T) (by omega)]
      exact hclaim T T (by omega) (by omega)
  · -- (2)
    intro i S hSlad hSZ
    rw [hZsS] at hSZ
    exact (hst i).2.2.2.2.2.2.2.2.2.2.2 S hSlad hSZ

/-- **Theorem 6.3.** In a parity-safe graph, a finite-port region containing an
    essential vertex has uncountably many ladder ends living in it. -/
theorem uncountable_ladderEnds (hS : IsParitySafe E) (Z : Set V) (hZ : FinitePort E Z)
    (v : V) (hvZ : v ∈ Z) (hv : Essential E v) :
    ¬ (LadderEndsIn E Z).Countable := by
  intro hc
  have hnkp : ¬ KernelPerfectOn E Z := hv Z hZ hvZ
  obtain ⟨R0, hR0, hR0Z⟩ := ladderRays_exist E hS.1 Z hnkp
  have hne : (LadderEndsIn E Z).Nonempty := ⟨endOf E R0, R0, hR0, hR0Z, rfl⟩
  obtain ⟨e, he⟩ := hc.exists_eq_range hne
  have he' : ∀ i, ∃ R, IsRay E R ∧ e i = endOf E R := by
    intro i
    have hi : e i ∈ LadderEndsIn E Z := by
      rw [he]
      exact Set.mem_range_self i
    obtain ⟨R, hR, -, hRe⟩ := hi
    exact ⟨R, hR.1, hRe⟩
  obtain ⟨Zs, R, -, -, -, hR, hRZ, htail, hnot⟩ :=
    diagonal_comb E hS Z hZ ⟨R0, hR0, hR0Z⟩ e he'
  have hmem : endOf E R ∈ LadderEndsIn E Z := ⟨R, hR, hRZ, rfl⟩
  rw [he] at hmem
  obtain ⟨i, hi⟩ := hmem
  obtain ⟨m, hm⟩ := htail (i + 1)
  apply hnot i (fun n => R (m + n)) (isLadderRay_tail E hR m) hm
  rw [hi]
  exact tail_mem_endOf E hR.1 m

/-! ## The main theorem -/

/-- **Theorem 1.2.** A parity-safe digraph with at most
    countably many ends is kernel-perfect. -/
theorem kernelPerfect_of_paritySafe_of_countable_ends
    (hS : IsParitySafe E) (hEnds : (Ends E).Countable) :
    KernelPerfect E := by
  by_contra hKP
  obtain ⟨v, hv⟩ := exists_essential E hS.1 hKP
  apply uncountable_ladderEnds E hS univ (finitePort_univ E) v (mem_univ v) hv
  refine hEnds.mono ?_
  rintro S ⟨R, hR, -, rfl⟩
  exact ⟨R, hR.1, rfl⟩

/-- **Theorem 1.2, second sentence.** A safe digraph with at most countably
    many ends is kernel-perfect. -/
theorem kernelPerfect_of_safe_of_countable_ends
    (hS : Safe E) (hEnds : (Ends E).Countable) :
    KernelPerfect E :=
  kernelPerfect_of_paritySafe_of_countable_ends E (isParitySafe_of_safe E hS) hEnds

end ParitySafe
