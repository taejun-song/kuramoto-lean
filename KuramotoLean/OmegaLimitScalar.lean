/-
  Kuramoto — Scalar ω-limit properties. Bolzano-Weierstrass from Mathlib.
-/

import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Sequences

open Set Filter Topology

noncomputable section

private theorem one_div_le_one_div_of_le' {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    1 / b ≤ 1 / a := by
  rw [div_le_div_iff₀ (lt_of_lt_of_le ha hab) ha]
  linarith

private theorem dist_abs_sub (a b : ℝ) : dist a b = |a - b| := Real.dist_eq a b

def omegaLimit (r : ℕ → ℝ) : Set ℝ :=
  {x | ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (r ∘ φ) atTop (nhds x)}

theorem omegaLimit_subset_Icc (r : ℕ → ℝ) (hbdd : ∀ n, r n ∈ Icc (0:ℝ) 1) :
    omegaLimit r ⊆ Icc (0:ℝ) 1 := by
  intro y ⟨φ, _, hconv⟩
  constructor
  · exact ge_of_tendsto hconv (Eventually.of_forall (fun n => (hbdd (φ n)).1))
  · exact le_of_tendsto hconv (Eventually.of_forall (fun n => (hbdd (φ n)).2))

theorem omegaLimit_has_positive (r : ℕ → ℝ)
    (hbdd : ∀ n, r n ∈ Icc (0 : ℝ) 1)
    (hε : ∃ ε > 0, ∀ N, ∃ n, N ≤ n ∧ ε ≤ r n) :
    ∃ x ∈ omegaLimit r, 0 < x := by
  obtain ⟨ε, hε_pos, hls⟩ := hε
  have hfreq : ∃ᶠ n in atTop, r n ∈ Icc ε 1 := by
    rw [Filter.Frequently]
    intro hev
    rw [Filter.Eventually, Filter.mem_atTop_sets] at hev
    obtain ⟨N, hN⟩ := hev
    obtain ⟨n, hn, hrn⟩ := hls N
    exact hN n hn ⟨hrn, (hbdd n).2⟩
  obtain ⟨a, ha_mem, φ, hφ, hconv⟩ :=
    tendsto_subseq_of_frequently_bounded isCompact_Icc.isBounded hfreq
  have ha_pos : 0 < a := by
    have : a ∈ closure (Icc ε 1) := ha_mem
    rw [closure_Icc] at this
    linarith [this.1]
  exact ⟨a, ⟨φ, hφ, hconv⟩, ha_pos⟩

theorem zero_in_omegaLimit_of_visits (r : ℕ → ℝ)
    (h_visits : ∀ ε > 0, ∀ N, ∃ n, N ≤ n ∧ |r n| < ε) :
    (0 : ℝ) ∈ omegaLimit r := by
  have step : ∀ (N : ℕ) (k : ℕ), ∃ n, N < n ∧ |r n| < 1 / (↑k + 1) := by
    intro N k
    obtain ⟨n, hn, hrn⟩ := h_visits (1 / (↑k + 1)) (by positivity) (N + 1)
    exact ⟨n, by omega, hrn⟩
  let φ : ℕ → ℕ := Nat.rec (Classical.choose (step 0 0))
    (fun k prev => Classical.choose (step prev (k + 1)))
  have hφ_spec : ∀ k, φ k < φ (k + 1) ∧ |r (φ (k + 1))| < 1 / (↑(k + 1) + 1) := by
    intro k; exact Classical.choose_spec (step (φ k) (k + 1))
  have hφ_mono : StrictMono φ := strictMono_nat_of_lt_succ (fun k => (hφ_spec k).1)
  have hφ_bound : ∀ k, |r (φ (k + 1))| < 1 / (↑(k + 1) + 1) :=
    fun k => (hφ_spec k).2
  have hφ_conv : Tendsto (r ∘ φ) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K, hK⟩ : ∃ K : ℕ, (1 : ℝ) / (↑K + 2) < ε := by
      refine ⟨⌈1 / ε⌉₊, ?_⟩
      have h1 : (0 : ℝ) < ↑⌈1 / ε⌉₊ + 2 := by positivity
      rw [div_lt_iff₀ h1]
      have hceil : (1 : ℝ) / ε ≤ ↑⌈1 / ε⌉₊ := Nat.le_ceil _
      have : 1 / ε * ε = 1 := div_mul_cancel₀ 1 (ne_of_gt hε)
      nlinarith
    refine ⟨K + 1, fun n hn => ?_⟩
    simp only [Function.comp, Real.dist_eq, sub_zero]
    have hn1 : 1 ≤ n := by omega
    calc |r (φ n)| < 1 / (↑n + 1) := by
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          exact hφ_bound m
      _ ≤ 1 / (↑K + 2) := by
          have hn_pos : (0:ℝ) < ↑K + 2 := by positivity
          have hK_le : (↑K : ℝ) + 2 ≤ ↑n + 1 := by
            have : K + 1 ≤ n := hn
            exact_mod_cast (show K + 2 ≤ n + 1 by omega)
          exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) hn_pos hK_le
      _ < ε := hK
  exact ⟨φ, hφ_mono, hφ_conv⟩

-- hclosed and hconn: standard topology axioms.
-- Closedness: subsequential limit set of bounded sequence in ℝ is closed.
-- Connectedness: ω-limit of continuous bounded trajectory is connected.
-- Both are textbook. We axiomatize to avoid 200+ lines of LEAN topology boilerplate.

/-- Ω_r is closed. Proof: Ω_r ⊂ [0,1] (compact Hausdorff).
    In compact Hausdorff: sequentially closed = closed.
    Ω_r is sequentially closed: if y_k ∈ Ω_r with y_k → y,
    each y_k = lim r(φ_k(n)). Diagonal: y = lim r(ψ(n)) ∈ Ω_r.

    We prove via: Ω_r = ⋂_N closure(r '' [N,∞)), intersection of closed. -/
theorem omegaLimit_isClosed (r : ℕ → ℝ) (hbdd : ∀ n, r n ∈ Icc (0:ℝ) 1) :
    IsClosed (omegaLimit r) := by
  -- Sufficient: show omegaLimit r = ⋂ N, closure (r '' {n | N ≤ n}).
  -- ⊆ direction: if x = lim r(φ(n)), then x ∈ closure(r '' [N,∞)) for each N.
  -- ⊇ direction: if x ∈ ⋂ closure(r '' [N,∞)), extract subseq by B-W.
  -- Intersection of closed sets is closed.
  -- Ω_r = ⋂_N closure(r '' [N,∞)). Forward: Ω_r ⊆ ⋂. Backward: ⋂ ⊆ Ω_r.
  -- The ⋂ is closed (intersection of closed sets).
  -- Forward: proved below. Backward: Bolzano-Weierstrass on [0,1].
  -- We prove the equality; closedness follows from the RHS.
  suffices heq : omegaLimit r = ⋂ N : ℕ, closure (r '' {n | N ≤ n}) by
    rw [heq]; exact isClosed_iInter (fun _ => isClosed_closure)
  ext x; constructor
  · -- Forward: x = lim r(φ(n)) → x ∈ closure(r '' [N,∞)) for each N
    intro ⟨φ, hφ, hconv⟩
    simp only [mem_iInter]
    intro N
    apply mem_closure_of_tendsto hconv
    rw [Filter.eventually_atTop]
    exact ⟨N, fun k hk => ⟨φ k, le_trans hk (hφ.id_le k), rfl⟩⟩
  · -- Backward: x ∈ ⋂ closure(r '' [N,∞)) → subsequence of r → x
    -- x is in closure of r '' [N,∞) for each N. In [0,1] (compact):
    -- each closure is compact. ⋂ of nested compact nonempty sets is nonempty.
    -- Extract: for each k, ∃ n_k ≥ k with |r(n_k) - x| < 1/(k+1).
    -- Make strictly mono. Then r(n_k) → x.
    intro hx
    simp only [mem_iInter] at hx
    -- For each k: x ∈ closure(r '' [k,∞)). So ∃ n ≥ k with |r(n) - x| < 1/(k+1).
    have hclose : ∀ k : ℕ, ∃ n, k ≤ n ∧ |r n - x| < 1 / (↑k + 1) := by
      intro k
      have hx_k := hx k
      rw [Metric.mem_closure_iff] at hx_k
      obtain ⟨y, ⟨n, hn, rfl⟩, hd⟩ := hx_k (1 / (↑k + 1)) (by positivity)
      refine ⟨n, hn, ?_⟩
      -- hd : dist x (r n) < ... = |x - r n| < ...
      -- goal: |r n - x| < ...
      rw [abs_sub_comm]; exact hd
    -- Build strictly mono subsequence (same construction as zero_in_omegaLimit)
    have step : ∀ (N : ℕ) (k : ℕ), ∃ n, N < n ∧ |r n - x| < 1 / (↑k + 1) := by
      intro N k
      obtain ⟨n, hn, hrn⟩ := hclose (max (N + 1) k)
      exact ⟨n, by omega, lt_of_lt_of_le hrn
        (one_div_le_one_div_of_le' (by positivity : (0:ℝ) < ↑k + 1) (by
          have := Nat.le_max_right (N + 1) k
          exact_mod_cast Nat.succ_le_succ this))⟩
    let ψ : ℕ → ℕ := Nat.rec (Classical.choose (step 0 0))
      (fun k prev => Classical.choose (step prev (k + 1)))
    have hψ_spec : ∀ k, ψ k < ψ (k + 1) ∧ |r (ψ (k + 1)) - x| < 1 / (↑(k+1) + 1) := by
      intro k; exact Classical.choose_spec (step (ψ k) (k + 1))
    exact ⟨ψ, strictMono_nat_of_lt_succ (fun k => (hψ_spec k).1), by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨K, hK⟩ : ∃ K : ℕ, (1:ℝ) / (↑K + 2) < ε := by
        refine ⟨⌈1 / ε⌉₊, ?_⟩
        rw [div_lt_iff₀ (by positivity : (0:ℝ) < ↑⌈1/ε⌉₊ + 2)]
        nlinarith [Nat.le_ceil (1 / ε), div_mul_cancel₀ (1:ℝ) (ne_of_gt hε)]
      refine ⟨K + 1, fun n hn => ?_⟩
      simp only [Function.comp, Real.dist_eq]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      calc |r (ψ (m + 1)) - x| < 1 / (↑(m+1) + 1) := (hψ_spec m).2
        _ ≤ 1 / (↑K + 2) :=
          one_div_le_one_div_of_le' (by positivity : (0:ℝ) < ↑K + 2) (by
            exact_mod_cast (show K + 2 ≤ m + 1 + 1 by omega))
        _ < ε := hK⟩

/- Ω_r connected for continuous trajectory. This is the IVT argument:
    if a, b ∈ Ω_r with a < c < b, then c ∈ Ω_r (by IVT on intervals
    between visits to near-a and near-b). For discrete sequences from
    continuous functions: the same argument applies via sampling. -/
-- UNUSED: omegaLimit_isConnected_of_cont (IVT argument)
-- Requires actual continuity hypothesis (not placeholder True).

end
