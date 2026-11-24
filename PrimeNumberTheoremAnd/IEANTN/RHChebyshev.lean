module

public import Architect
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.Harmonic.Bounds
public import PrimeNumberTheoremAnd.Defs
public import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
public import PrimeNumberTheoremAnd.IEANTN.KadiriZeroCounting

@[expose] public section

open Real Filter Asymptotics Finset
open scoped Chebyshev

blueprint_comment /--
\section{Chebyshev error bounds under the Riemann Hypothesis}\label{rh-chebyshev-sec}

This section is the entry point for RH-conditional explicit bounds on $\psi$.  The two
bounds below are \emph{stated as propositions} (not yet proved: the project has no explicit
formula for $\psi$ in terms of the zeroes of $\zeta$).  Downstream RH-conditional results can take
them as hypotheses, and the implication from Schoenfeld's explicit form to von Koch's $O$-form is
proved.
-/

@[blueprint
  "rh-psi-schoenfeld-bound"
  (title := "Schoenfeld's explicit bound for $\\psi$ under RH")
  (statement := /-- Assuming the Riemann Hypothesis, for all $x \geq 73.2$,
  \[ |\psi(x) - x| < \frac{\sqrt{x}\,\log^2 x}{8\pi}, \]
  see \cite[Corollary~1 of Theorem~10]{RS-chebyshev-II}. This is the statement of the
  proposition only; it is not proved here. -/)
  (latexEnv := "definition")]
def RHPsiSchoenfeldBound : Prop :=
  RiemannHypothesis → ∀ x : ℝ, 73.2 ≤ x → |ψ x - x| < √x * (log x) ^ 2 / (8 * π)

@[blueprint
  "rh-psi-von-koch-bound"
  (title := "von Koch's bound for $\\psi$ under RH")
  (statement := /-- Assuming the Riemann Hypothesis,
  $\psi(x) = x + O(\sqrt{x}\log^2 x)$ as $x \to \infty$ (von Koch 1901). This is the statement of
  the proposition only; it is not proved here. -/)
  (latexEnv := "definition")]
def RHPsiVonKochBound : Prop :=
  RiemannHypothesis → (fun x : ℝ ↦ ψ x - x) =O[atTop] fun x : ℝ ↦ √x * (log x) ^ 2

@[blueprint
  "rh-psi-von-koch-of-schoenfeld"
  (title := "Von Koch's bound from Schoenfeld's explicit bound")
  (statement := /-- Schoenfeld's explicit bound $|\psi(x)-x| < \sqrt{x}\log^2 x/(8\pi)$ for
  $x \ge 73.2$ implies von Koch's $\psi(x) = x + O(\sqrt{x}\log^2 x)$. -/)
  (proof := /-- Take the constant $1/(8\pi)$ and the eventual range $x \ge 73.2$. -/)
  (uses := ["rh-psi-schoenfeld-bound", "rh-psi-von-koch-bound"])
  (latexEnv := "theorem")]
theorem RHPsiVonKochBound_of_schoenfeld (h : RHPsiSchoenfeldBound) : RHPsiVonKochBound := by
  intro RH
  refine IsBigO.of_bound (1 / (8 * π)) ?_
  filter_upwards [eventually_ge_atTop (73.2 : ℝ)] with x hx
  have h1 := (h RH x hx).le
  have hx0 : 0 ≤ √x * (log x) ^ 2 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0]
  calc |ψ x - x| ≤ √x * (log x) ^ 2 / (8 * π) := h1
    _ = 1 / (8 * π) * (√x * (log x) ^ 2) := by ring

@[blueprint
  "rh-norm-cpow-zero"
  (title := "Modulus of $x^\\rho$ under RH")
  (statement := /-- Assuming the Riemann Hypothesis, if $\rho$ is a nontrivial zero of $\zeta$
  and $x > 0$, then $|x^\rho| = \sqrt{x}$. This is the size of each term of the explicit
  formula $\psi(x) = x - \sum_\rho x^\rho/\rho - \cdots$. -/)
  (proof := /-- $|x^\rho| = x^{\Re\rho}$ and $\Re \rho = 1/2$. -/)
  (latexEnv := "lemma")]
lemma RiemannHypothesis.norm_cpow_nontrivialZero (RH : RiemannHypothesis) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (htriv : ¬∃ n : ℕ, ρ = -2 * (n + 1)) (h1 : ρ ≠ 1)
    {x : ℝ} (hx : 0 < x) : ‖(x : ℂ) ^ ρ‖ = √x := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, RH ρ hρ htriv h1, Real.sqrt_eq_rpow]

@[blueprint
  "rh-theta-von-koch-bound"
  (title := "von Koch's bound for $\\theta$ under RH")
  (statement := /-- Assuming the Riemann Hypothesis,
  $\theta(x) = x + O(\sqrt{x}\log^2 x)$ as $x \to \infty$. This is the statement of the
  proposition only; it is not proved here. -/)
  (latexEnv := "definition")]
def RHThetaVonKochBound : Prop :=
  RiemannHypothesis → (fun x : ℝ ↦ θ x - x) =O[atTop] fun x : ℝ ↦ √x * (log x) ^ 2

@[blueprint
  "rh-theta-von-koch-of-psi"
  (title := "Von Koch's bound for $\\theta$ from that for $\\psi$")
  (statement := /-- The $O(\sqrt{x}\log^2 x)$ bound for $\psi(x)-x$ implies the same for
  $\theta(x)-x$. -/)
  (proof := /-- $0 \le \psi(x)-\theta(x) \le 2\sqrt{x}\log x \le 2\sqrt{x}\log^2 x$ for $x \ge e$,
  so $|\theta(x)-x| \le |\psi(x)-x| + 2\sqrt{x}\log^2 x$. -/)
  (uses := ["rh-psi-von-koch-bound", "rh-theta-von-koch-bound"])
  (latexEnv := "theorem")]
theorem RHThetaVonKochBound_of_psi (h : RHPsiVonKochBound) : RHThetaVonKochBound := by
  intro RH
  obtain ⟨C, hC⟩ := (h RH).bound
  refine IsBigO.of_bound (C + 2) ?_
  filter_upwards [hC, eventually_ge_atTop (3 : ℝ)] with x hxC hx3
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hlog : 1 ≤ log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_three
    linarith
  have hs : 0 ≤ √x := Real.sqrt_nonneg x
  have hd := Chebyshev.psi_sub_theta_le hx1
  have hd0 := sub_nonneg.mpr (Chebyshev.theta_le_psi x)
  have hpos : 0 ≤ √x * (log x) ^ 2 := by positivity
  have h2 : 2 * √x * log x ≤ 2 * (√x * (log x) ^ 2) := by
    nlinarith [mul_nonneg hs (sub_nonneg.mpr hlog), mul_nonneg hs (mul_nonneg (sub_nonneg.mpr hlog) (by linarith : (0:ℝ) ≤ log x))]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos] at hxC ⊢
  have : |θ x - x| ≤ |ψ x - x| + (ψ x - θ x) := by
    rw [abs_le]; constructor <;> cases abs_cases (ψ x - x) <;> linarith [neg_abs_le (ψ x - x), le_abs_self (ψ x - x)]
  nlinarith

@[blueprint
  "rh-norm-cpow-div-zero"
  (title := "Size of an explicit-formula term under RH")
  (statement := /-- Assuming the Riemann Hypothesis, if $\rho$ is a nontrivial zero of $\zeta$ and
  $x>0$, then $|x^\rho/\rho| = \sqrt{x}/|\rho|$, which is at most $2\sqrt{x}$, and at most
  $\sqrt{x}/|\Im\rho|$ when $\Im\rho \ne 0$. These bound the terms of the explicit formula
  $\psi(x) = x - \sum_\rho x^\rho/\rho - \cdots$. -/)
  (proof := /-- $|x^\rho| = \sqrt{x}$ by the previous lemma, and $|\rho| \ge |\Re\rho| = 1/2$ and
  $|\rho| \ge |\Im\rho|$. -/)
  (uses := ["rh-norm-cpow-zero"])
  (latexEnv := "lemma")]
lemma RiemannHypothesis.norm_cpow_div_nontrivialZero (RH : RiemannHypothesis) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (htriv : ¬∃ n : ℕ, ρ = -2 * (n + 1)) (h1 : ρ ≠ 1)
    {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ ρ / ρ‖ = √x / ‖ρ‖ ∧ ‖(x : ℂ) ^ ρ / ρ‖ ≤ 2 * √x ∧
      (ρ.im ≠ 0 → ‖(x : ℂ) ^ ρ / ρ‖ ≤ √x / |ρ.im|) := by
  have hre : ρ.re = 1 / 2 := RH ρ hρ htriv h1
  have hn : ‖(x : ℂ) ^ ρ‖ = √x := RH.norm_cpow_nontrivialZero hρ htriv h1 hx
  have hhalf : 1 / 2 ≤ ‖ρ‖ := by
    have := Complex.abs_re_le_norm ρ
    rw [hre, abs_of_pos (by norm_num)] at this
    exact this
  have hpos : 0 < ‖ρ‖ := by linarith
  have hs : 0 ≤ √x := Real.sqrt_nonneg x
  have heq : ‖(x : ℂ) ^ ρ / ρ‖ = √x / ‖ρ‖ := by rw [norm_div, hn]
  refine ⟨heq, ?_, fun him => ?_⟩
  · rw [heq, div_le_iff₀ hpos]; nlinarith
  · rw [heq]
    exact div_le_div_of_nonneg_left hs (abs_pos.mpr him) (Complex.abs_im_le_norm ρ)

@[blueprint
  "rh-sum-inv-heights-le"
  (title := "Sum of $1/|\\gamma|$ from a unit-window count")
  (statement := /-- Let $T \ge 1$ and let $\gamma_i$ ($i$ in a finite set) be heights with $1 \le |\gamma_i| \le T$,
  and suppose that for each integer $k \ge 1$ at most $A\log(k+2)$ of them satisfy
  $k \le |\gamma_i| < k+1$ (the Riemann--von Mangoldt count $N(t+1)-N(t) = O(\log t)$). Then
  $\sum_i 1/|\gamma_i| \le A\log(T+2)\,(1+\log T)$. This is the zero-sum step of von Koch's
  argument, isolated from the zeta function. -/)
  (proof := /-- Group by $k=\lfloor|\gamma_i|\rfloor$; each group contributes at most
  $A\log(k+2)/k \le A\log(T+2)/k$, and $\sum_{k\le T}1/k \le 1+\log T$. -/)
  (latexEnv := "lemma")]
lemma sum_inv_abs_le_of_window_count {ι : Type*} (s : Finset ι) (γ : ι → ℝ) {T A : ℝ}
    (hA : 0 ≤ A) (hT1 : 1 ≤ T) (hT : ∀ i ∈ s, 1 ≤ |γ i| ∧ |γ i| ≤ T)
    (hcount : ∀ k : ℕ, (#{i ∈ s | ⌊|γ i|⌋₊ = k} : ℝ) ≤ A * log (k + 2)) :
    ∑ i ∈ s, 1 / |γ i| ≤ A * log (T + 2) * (1 + log T) := by
  classical
  have hmaps : ∀ i ∈ s, ⌊|γ i|⌋₊ ∈ Icc 1 ⌊T⌋₊ := fun i hi => by
    rw [mem_Icc]
    exact ⟨Nat.le_floor (by simpa using (hT i hi).1), Nat.floor_le_floor (hT i hi).2⟩
  have hlogT : 0 ≤ log (T + 2) := Real.log_nonneg (by linarith)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ k ∈ Icc 1 ⌊T⌋₊, ∑ i ∈ s with ⌊|γ i|⌋₊ = k, 1 / |γ i|
      ≤ ∑ k ∈ Icc 1 ⌊T⌋₊, A * log (T + 2) * (1 / (k : ℝ)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
        have hkT : (k : ℝ) ≤ T := (Nat.le_floor_iff (by linarith)).mp (mem_Icc.mp hk).2
        have hterm : ∀ i ∈ ({i ∈ s | ⌊|γ i|⌋₊ = k} : Finset ι), 1 / |γ i| ≤ 1 / (k : ℝ) := by
          intro i hi
          have hik := (mem_filter.mp hi).2
          have : (k : ℝ) ≤ |γ i| := by rw [← hik]; exact Nat.floor_le (abs_nonneg _)
          exact one_div_le_one_div_of_le (by linarith) this
        calc ∑ i ∈ s with ⌊|γ i|⌋₊ = k, 1 / |γ i|
            ≤ #{i ∈ s | ⌊|γ i|⌋₊ = k} • (1 / (k : ℝ)) := Finset.sum_le_card_nsmul _ _ _ hterm
          _ = (#{i ∈ s | ⌊|γ i|⌋₊ = k} : ℝ) * (1 / (k : ℝ)) := by rw [nsmul_eq_mul]
          _ ≤ (A * log (k + 2)) * (1 / (k : ℝ)) :=
              mul_le_mul_of_nonneg_right (hcount k) (by positivity)
          _ ≤ A * log (T + 2) * (1 / (k : ℝ)) := by
              gcongr
    _ = A * log (T + 2) * (harmonic ⌊T⌋₊ : ℝ) := by
        rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
        simp
    _ ≤ A * log (T + 2) * (1 + log T) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hA hlogT)
        refine (harmonic_le_one_add_log _).trans ?_
        have : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le (by linarith)
        have hpos : (0 : ℝ) < ⌊T⌋₊ := by
          have : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by simpa using hT1)
          exact_mod_cast this
        have := Real.log_le_log hpos this
        linarith

@[blueprint
  "rh-zero-sum-sqrt-height"
  (title := "Zero sum truncated at height $\\sqrt{x}$")
  (statement := /-- In the setting of the previous lemma with $T=\sqrt{x}$ and $x \ge 16$,
  $\sqrt{x}\sum_i 1/|\gamma_i| \le A\sqrt{x}\log^2 x$. With each term of the explicit formula
  bounded by $\sqrt{x}/|\gamma_i|$ under RH, this is the $O(\sqrt{x}\log^2 x)$ contribution of
  the zeros with $|\gamma|\le\sqrt{x}$ in von Koch's theorem. -/)
  (proof := /-- Apply the previous lemma; $\log(\sqrt{x}+2) \le \log(2\sqrt{x}) \le \log x$ and
  $1+\log\sqrt{x} \le \log x$ for $x \ge 16$. -/)
  (uses := ["rh-sum-inv-heights-le"])
  (latexEnv := "lemma")]
lemma sqrt_mul_sum_inv_abs_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ) {x A : ℝ}
    (hA : 0 ≤ A) (hx : 16 ≤ x) (hT : ∀ i ∈ s, 1 ≤ |γ i| ∧ |γ i| ≤ √x)
    (hcount : ∀ k : ℕ, (#{i ∈ s | ⌊|γ i|⌋₊ = k} : ℝ) ≤ A * log (k + 2)) :
    √x * ∑ i ∈ s, 1 / |γ i| ≤ A * (√x * (log x) ^ 2) := by
  have hs4 : (4 : ℝ) ≤ √x := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hmain := sum_inv_abs_le_of_window_count s γ hA (by linarith) hT hcount
  have hlog2 : log 2 ≤ log x / 2 := by
    have h4 : log 4 ≤ log x := Real.log_le_log (by norm_num) (by linarith)
    have : log 4 = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hlogs : log (√x) = log x / 2 := by
    rw [Real.log_sqrt (by linarith)]
  have hlogx2 : 2 ≤ log x := by
    have h16 : log 16 ≤ log x := Real.log_le_log (by norm_num) hx
    have : log 16 = 4 * log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have h2 : (0.69 : ℝ) < log 2 := by
      have := Real.log_two_gt_d9; linarith
    linarith
  have hA1 : log (√x + 2) ≤ log x := by
    have : log (√x + 2) ≤ log (2 * √x) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith), hlogs] at this
    linarith
  have hB : 1 + log (√x) ≤ log x := by rw [hlogs]; linarith
  have hsq : 0 ≤ √x := by linarith
  have hlogpos : 0 ≤ log x := by linarith
  calc √x * ∑ i ∈ s, 1 / |γ i| ≤ √x * (A * log (√x + 2) * (1 + log √x)) :=
        mul_le_mul_of_nonneg_left hmain hsq
    _ ≤ √x * (A * log x * log x) := by
        refine mul_le_mul_of_nonneg_left ?_ hsq
        have h1 : 0 ≤ log (√x + 2) := Real.log_nonneg (by linarith)
        have h2 : 0 ≤ 1 + log (√x) := by rw [hlogs]; linarith
        calc A * log (√x + 2) * (1 + log √x) ≤ A * log x * (1 + log √x) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA1 hA) h2
          _ ≤ A * log x * log x :=
              mul_le_mul_of_nonneg_left hB (mul_nonneg hA hlogpos)
    _ = A * (√x * (log x) ^ 2) := by ring

@[blueprint
  "rh-psi-von-koch-of-explicit-formula"
  (title := "Von Koch from an explicit-formula bound and the window count")
  (statement := /-- Assume RH. Let $(\rho_i)_{i\in\iota}$ be nontrivial zeros of $\zeta$ and, for each
  $x\ge16$, let $s_x$ be a finite subset of indices with $1\le|\Im\rho_i|\le\sqrt{x}$ for $i\in s_x$.
  Suppose
  \[ |\psi(x)-x| \le \sum_{i\in s_x}|x^{\rho_i}/\rho_i| + C\sqrt{x}\log^2 x \quad(x\ge16)\]
  (the shape of the truncated explicit formula at height $\sqrt{x}$, with the zeros of height
  $<1$ and the truncation tail absorbed in $C\sqrt{x}\log^2 x$), and that at most $A\log(k+2)$
  indices of $s_x$ have $\lfloor|\Im\rho_i|\rfloor=k$. Then $\psi(x)=x+O(\sqrt{x}\log^2 x)$.
  The explicit-formula hypothesis is \emph{not} proved here. -/)
  (proof := /-- Bound each term by $\sqrt{x}/|\Im\rho_i|$ and apply the previous lemma. -/)
  (uses := ["rh-norm-cpow-div-zero", "rh-zero-sum-sqrt-height", "rh-psi-von-koch-bound"])
  (latexEnv := "theorem")]
theorem psi_sub_self_isBigO_of_explicit_formula (RH : RiemannHypothesis) {ι : Type*}
    (ρ : ι → ℂ) (hρ : ∀ i, riemannZeta (ρ i) = 0)
    (htriv : ∀ i, ¬∃ n : ℕ, ρ i = -2 * (n + 1)) (h1 : ∀ i, ρ i ≠ 1)
    (s : ℝ → Finset ι) {A C : ℝ} (hA : 0 ≤ A)
    (hs : ∀ x, 16 ≤ x → ∀ i ∈ s x, 1 ≤ |(ρ i).im| ∧ |(ρ i).im| ≤ √x)
    (hexp : ∀ x, 16 ≤ x →
      |ψ x - x| ≤ ∑ i ∈ s x, ‖(x : ℂ) ^ ρ i / ρ i‖ + C * (√x * (log x) ^ 2))
    (hcount : ∀ x, 16 ≤ x → ∀ k : ℕ,
      (#{i ∈ s x | ⌊|(ρ i).im|⌋₊ = k} : ℝ) ≤ A * log (k + 2)) :
    (fun x : ℝ ↦ ψ x - x) =O[atTop] fun x : ℝ ↦ √x * (log x) ^ 2 := by
  refine IsBigO.of_bound (A + C) ?_
  filter_upwards [eventually_ge_atTop (16 : ℝ)] with x hx
  have hsq : 0 ≤ √x := Real.sqrt_nonneg x
  have hpos : 0 ≤ √x * (log x) ^ 2 := by positivity
  have hx0 : 0 < x := by linarith
  have hterm : ∀ i ∈ s x, ‖(x : ℂ) ^ ρ i / ρ i‖ ≤ √x * (1 / |(ρ i).im|) := by
    intro i hi
    have him : (ρ i).im ≠ 0 := by
      have := (hs x hx i hi).1
      intro h0; rw [h0] at this; simp at this; linarith
    have := (RH.norm_cpow_div_nontrivialZero (hρ i) (htriv i) (h1 i) hx0).2.2 him
    rw [mul_one_div]; exact this
  have hsum : ∑ i ∈ s x, ‖(x : ℂ) ^ ρ i / ρ i‖ ≤ A * (√x * (log x) ^ 2) := by
    calc ∑ i ∈ s x, ‖(x : ℂ) ^ ρ i / ρ i‖ ≤ ∑ i ∈ s x, √x * (1 / |(ρ i).im|) :=
          Finset.sum_le_sum hterm
      _ = √x * ∑ i ∈ s x, 1 / |(ρ i).im| := by rw [← Finset.mul_sum]
      _ ≤ A * (√x * (log x) ^ 2) :=
          sqrt_mul_sum_inv_abs_le (s x) (fun i => (ρ i).im) hA hx (hs x hx) (hcount x hx)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos]
  linarith [hexp x hx]

@[blueprint
  "rh-window-count-of-rvm"
  (title := "Unit-window zero count from a Riemann--von Mangoldt estimate")
  (statement := /-- If $|N(T)-\frac{T}{2\pi}\log\frac{T}{2\pi e}-\frac78| \le b_1\log T+b_2\log\log T+b_3$
  for all $T\ge2$ with $b_1,b_2,b_3\ge0$, then for all $T\ge2$
  \[ N(T+1)-N(T) \le A\log(T+2),\qquad A = 1+2b_1+2b_2+2b_3/\log 2. \] -/)
  (proof := /-- Subtract the two estimates. The main terms differ by at most
  $\frac1{2\pi}\log\frac{T+1}{2\pi}$ since $\log(1+1/T)\le1/T$, and each error term is at most
  $(b_1+b_2)\log(T+2)+b_3$. -/)
  (uses := ["Riemann-von-Mangoldt-estimate"])
  (latexEnv := "lemma")]
lemma riemannZeta.N_add_one_sub_N_le {b₁ b₂ b₃ : ℝ} (h1 : 0 ≤ b₁) (h2 : 0 ≤ b₂) (h3 : 0 ≤ b₃)
    (hR : riemannZeta.Riemann_vonMangoldt_bound b₁ b₂ b₃) {T : ℝ} (hT : 2 ≤ T) :
    riemannZeta.N (T + 1) - riemannZeta.N T ≤
      (1 + 2 * b₁ + 2 * b₂ + 2 * b₃ / log 2) * log (T + 2) := by
  have hT0 : 0 < T := by linarith
  have hπ : 1 < 2 * π := by linarith [Real.pi_gt_three]
  have hπ0 : 0 < 2 * π := by linarith
  set L := log (T + 2) with hL
  have hL2 : log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hLpos : 0 ≤ L := by linarith
  have hlogT : log T ≤ L := Real.log_le_log hT0 (by linarith)
  have hlogT1 : log (T + 1) ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hlogT_nonneg : 0 ≤ log T := Real.log_nonneg (by linarith)
  have hlogT1_nonneg : 0 ≤ log (T + 1) := Real.log_nonneg (by linarith)
  have hll : log (log T) ≤ L :=
    (Real.log_le_self hlogT_nonneg).trans hlogT
  have hll1 : log (log (T + 1)) ≤ L :=
    (Real.log_le_self hlogT1_nonneg).trans hlogT1
  have hb3 : b₃ ≤ b₃ / log 2 * L := by
    calc b₃ = b₃ / log 2 * log 2 := by field_simp
      _ ≤ b₃ / log 2 * L := mul_le_mul_of_nonneg_left hL2 (by positivity)
  have e1 := hR (T + 1) (by linarith)
  have e0 := hR T hT
  unfold riemannZeta.RvM at e1 e0
  have hmain : (T + 1) / (2 * π) * log ((T + 1) / (2 * π)) - T / (2 * π) * log (T / (2 * π))
      - 1 / (2 * π) ≤ 1 / (2 * π) * log (T + 1) := by
    have hdiff : log ((T + 1) / (2 * π)) - log (T / (2 * π)) ≤ 1 / T := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have := Real.log_le_sub_one_of_pos (show 0 < (T + 1) / (2 * π) / (T / (2 * π)) by positivity)
      have heq : (T + 1) / (2 * π) / (T / (2 * π)) = 1 + 1 / T := by field_simp
      rw [heq] at this ⊢; linarith
    have ha : log ((T + 1) / (2 * π)) ≤ log (T + 1) :=
      Real.log_le_log (by positivity) (by rw [div_le_iff₀ hπ0]; nlinarith)
    have key : (T + 1) * log ((T + 1) / (2 * π)) - T * log (T / (2 * π)) ≤
        log ((T + 1) / (2 * π)) + 1 := by
      have := mul_le_mul_of_nonneg_left hdiff hT0.le
      rw [mul_one_div_cancel hT0.ne'] at this
      nlinarith
    have : (T + 1) / (2 * π) * log ((T + 1) / (2 * π)) - T / (2 * π) * log (T / (2 * π))
        - 1 / (2 * π) = ((T + 1) * log ((T + 1) / (2 * π)) - T * log (T / (2 * π)) - 1) / (2 * π) := by
      field_simp
    rw [this, div_le_iff₀ hπ0]
    have : 1 / (2 * π) * log (T + 1) * (2 * π) = log (T + 1) := by field_simp
    linarith
  have hπinv : 1 / (2 * π) ≤ 1 := by rw [div_le_one hπ0]; exact hπ.le
  have hA : 1 / (2 * π) * log (T + 1) ≤ L := by
    calc 1 / (2 * π) * log (T + 1) ≤ 1 * log (T + 1) :=
          mul_le_mul_of_nonneg_right hπinv hlogT1_nonneg
      _ ≤ L := by linarith
  have hb1 : b₁ * log (T + 1) ≤ b₁ * L := mul_le_mul_of_nonneg_left hlogT1 h1
  have hb1' : b₁ * log T ≤ b₁ * L := mul_le_mul_of_nonneg_left hlogT h1
  have hb2 : b₂ * log (log (T + 1)) ≤ b₂ * L := mul_le_mul_of_nonneg_left hll1 h2
  have hb2' : b₂ * log (log T) ≤ b₂ * L := mul_le_mul_of_nonneg_left hll h2
  have habs1 := (abs_le.mp e1).2
  have habs0 := (abs_le.mp e0).1
  have hexpand : (1 + 2 * b₁ + 2 * b₂ + 2 * b₃ / log 2) * L =
      L + 2 * (b₁ * L) + 2 * (b₂ * L) + 2 * (b₃ / log 2 * L) := by ring
  have hid : (T + 1) / (2 * π) = T / (2 * π) + 1 / (2 * π) := by ring
  rw [hexpand]
  linarith

/-- On a finite zero rectangle, `zeroes_sum` is the finite sum of the orders. -/
lemma riemannZeta.zeroes_sum_one_eq_finset (I J : Set ℝ) (h : (zeroes_rect I J).Finite) :
    zeroes_sum I J (fun _ ↦ (1 : ℝ)) = ∑ ρ ∈ h.toFinset, (order ρ : ℝ) := by
  classical
  unfold zeroes_sum
  have : Finite (zeroes_rect I J) := h.to_subtype
  let _ := Fintype.ofFinite (zeroes_rect I J)
  rw [tsum_fintype]
  simp only [one_mul]
  exact (Finset.sum_subtype h.toFinset (p := (· ∈ zeroes_rect I J)) (fun x => by simp)
    (fun x => (order x : ℝ))).symm

@[blueprint
  "rh-zeroes-sum-window"
  (title := "Zeros in a height window as a difference of $N$")
  (statement := /-- For $0<a\le b$, the number of zeros of $\zeta$ (with multiplicity) with
  $a\le\Im\rho<b$ equals $N(b)-N(a)$. -/)
  (proof := /-- The zero rectangle of height $(0,b)$ is the disjoint union of those of heights
  $(0,a)$ and $[a,b)$, all finite. -/)
  (latexEnv := "lemma")]
lemma riemannZeta.zeroes_sum_Ico_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    zeroes_sum (Set.univ : Set ℝ) (Set.Ico a b) (fun _ ↦ (1 : ℝ)) = N b - N a := by
  classical
  have hb := Kadiri.zeroes_rect_univ_positive_height_finite b
  have ha' := Kadiri.zeroes_rect_univ_positive_height_finite a
  have hI : (zeroes_rect (Set.univ : Set ℝ) (Set.Ico a b)).Finite :=
    (Kadiri.zeroes_rect_univ_positive_height_finite (b + 1)).subset fun z hz =>
      ⟨hz.1, ⟨by linarith [hz.2.1.1], by linarith [hz.2.1.2]⟩, hz.2.2⟩
  have hfin : hb.toFinset = ha'.toFinset ∪ hI.toFinset := by
    ext z
    simp only [Set.Finite.mem_toFinset, Finset.mem_union, zeroes_rect, Set.mem_ofPred_eq,
      Set.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h0, h1⟩, hz⟩
      by_cases h : z.im < a
      · exact Or.inl ⟨⟨h0, h⟩, hz⟩
      · exact Or.inr ⟨⟨not_lt.mp h, h1⟩, hz⟩
    · rintro (⟨⟨h0, h1⟩, hz⟩ | ⟨⟨h0, h1⟩, hz⟩)
      · exact ⟨⟨h0, by linarith⟩, hz⟩
      · exact ⟨⟨by linarith, h1⟩, hz⟩
  have hdisj : Disjoint ha'.toFinset hI.toFinset := by
    rw [Finset.disjoint_left]
    intro z h1 h2
    simp only [Set.Finite.mem_toFinset, zeroes_rect, Set.mem_ofPred_eq] at h1 h2
    linarith [h1.2.1.2, h2.2.1.1]
  rw [zeroes_sum_one_eq_finset _ _ hI]
  unfold N
  rw [zeroes_sum_one_eq_finset _ _ hb, zeroes_sum_one_eq_finset _ _ ha', hfin,
    Finset.sum_union hdisj]
  ring

@[blueprint
  "rh-zeroes-sum-window-le"
  (title := "Zeros with height in $[k,k+1)$ under an RvM estimate")
  (statement := /-- Under the hypotheses of the window-count lemma, for every integer $k\ge2$ the
  number of zeros (with multiplicity) with $k\le\Im\rho<k+1$ is at most
  $(1+2b_1+2b_2+2b_3/\log2)\log(k+2)$. -/)
  (proof := /-- Combine the window identity with the bound on $N(k+1)-N(k)$. -/)
  (uses := ["rh-zeroes-sum-window", "rh-window-count-of-rvm"])
  (latexEnv := "lemma")]
lemma riemannZeta.zeroes_sum_Ico_nat_le {b₁ b₂ b₃ : ℝ} (h1 : 0 ≤ b₁) (h2 : 0 ≤ b₂) (h3 : 0 ≤ b₃)
    (hR : riemannZeta.Riemann_vonMangoldt_bound b₁ b₂ b₃) {k : ℕ} (hk : 2 ≤ k) :
    zeroes_sum (Set.univ : Set ℝ) (Set.Ico (k : ℝ) (k + 1)) (fun _ ↦ (1 : ℝ)) ≤
      (1 + 2 * b₁ + 2 * b₂ + 2 * b₃ / log 2) * log (k + 2) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rw [zeroes_sum_Ico_eq (by linarith) (by linarith)]
  exact N_add_one_sub_N_le h1 h2 h3 hR hk'

@[blueprint
  "rh-weighted-sum-inv-heights-le"
  (title := "Weighted sum of $1/|\\gamma|$ from a unit-window count")
  (statement := /-- The weighted version of the unit-window lemma: for $T\ge1$, weights $w_i\ge0$ and
  heights with $1\le|\gamma_i|\le T$ such that $\sum_{\lfloor|\gamma_i|\rfloor=k}w_i\le A\log(k+2)$
  for every $k$, one has $\sum_i w_i/|\gamma_i| \le A\log(T+2)(1+\log T)$. Taking $w_i$ to be the
  order of the zero $\rho_i$ accounts for multiplicity. -/)
  (proof := /-- Identical to the unweighted case, grouping by $\lfloor|\gamma_i|\rfloor$. -/)
  (latexEnv := "lemma")]
lemma sum_div_abs_le_of_weighted_window_count {ι : Type*} (s : Finset ι) (γ w : ι → ℝ)
    {T A : ℝ} (hA : 0 ≤ A) (hT1 : 1 ≤ T) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hT : ∀ i ∈ s, 1 ≤ |γ i| ∧ |γ i| ≤ T)
    (hcount : ∀ k : ℕ, ∑ i ∈ s with ⌊|γ i|⌋₊ = k, w i ≤ A * log (k + 2)) :
    ∑ i ∈ s, w i / |γ i| ≤ A * log (T + 2) * (1 + log T) := by
  classical
  have hmaps : ∀ i ∈ s, ⌊|γ i|⌋₊ ∈ Icc 1 ⌊T⌋₊ := fun i hi => by
    rw [mem_Icc]
    exact ⟨Nat.le_floor (by simpa using (hT i hi).1), Nat.floor_le_floor (hT i hi).2⟩
  have hlogT : 0 ≤ log (T + 2) := Real.log_nonneg (by linarith)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ k ∈ Icc 1 ⌊T⌋₊, ∑ i ∈ s with ⌊|γ i|⌋₊ = k, w i / |γ i|
      ≤ ∑ k ∈ Icc 1 ⌊T⌋₊, A * log (T + 2) * (1 / (k : ℝ)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
        have hkT : (k : ℝ) ≤ T := (Nat.le_floor_iff (by linarith)).mp (mem_Icc.mp hk).2
        have hterm : ∀ i ∈ ({i ∈ s | ⌊|γ i|⌋₊ = k} : Finset ι),
            w i / |γ i| ≤ w i * (1 / (k : ℝ)) := by
          intro i hi
          have his := (mem_filter.mp hi).1
          have hik := (mem_filter.mp hi).2
          have : (k : ℝ) ≤ |γ i| := by rw [← hik]; exact Nat.floor_le (abs_nonneg _)
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by linarith) this) (hw i his)
        calc ∑ i ∈ s with ⌊|γ i|⌋₊ = k, w i / |γ i|
            ≤ ∑ i ∈ s with ⌊|γ i|⌋₊ = k, w i * (1 / (k : ℝ)) := Finset.sum_le_sum hterm
          _ = (∑ i ∈ s with ⌊|γ i|⌋₊ = k, w i) * (1 / (k : ℝ)) := by rw [← Finset.sum_mul]
          _ ≤ (A * log (k + 2)) * (1 / (k : ℝ)) :=
              mul_le_mul_of_nonneg_right (hcount k) (by positivity)
          _ ≤ A * log (T + 2) * (1 / (k : ℝ)) := by
              gcongr
    _ = A * log (T + 2) * (harmonic ⌊T⌋₊ : ℝ) := by
        rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
        simp
    _ ≤ A * log (T + 2) * (1 + log T) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hA hlogT)
        refine (harmonic_le_one_add_log _).trans ?_
        have : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le (by linarith)
        have hpos : (0 : ℝ) < ⌊T⌋₊ := by
          have : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by simpa using hT1)
          exact_mod_cast this
        have := Real.log_le_log hpos this
        linarith

/-- On a finite zero rectangle, `zeroes_sum` is the finite sum of the weighted orders. -/
lemma riemannZeta.zeroes_sum_eq_finset (I J : Set ℝ) (f : ℂ → ℝ)
    (h : (zeroes_rect I J).Finite) :
    zeroes_sum I J f = ∑ ρ ∈ h.toFinset, f ρ * (order ρ : ℝ) := by
  classical
  unfold zeroes_sum
  have : Finite (zeroes_rect I J) := h.to_subtype
  let _ := Fintype.ofFinite (zeroes_rect I J)
  rw [tsum_fintype]
  exact (Finset.sum_subtype h.toFinset (p := (· ∈ zeroes_rect I J)) (fun x => by simp)
    (fun x => f x * (order x : ℝ))).symm

@[blueprint
  "rh-zeroes-sum-inv-im-le"
  (title := "$\\sum_\\rho 1/|\\Im\\rho|$ over zeros of height in $[2,n)$ from an RvM estimate")
  (statement := /-- Under an estimate
  $|N(T)-\frac{T}{2\pi}\log\frac{T}{2\pi e}-\frac78|\le b_1\log T+b_2\log\log T+b_3$ ($T\ge2$,
  $b_i\ge0$), for every integer $n\ge2$ the sum over zeros $\rho$ (with multiplicity) with
  $2\le\Im\rho<n$ satisfies
  \[ \sum_\rho \frac1{|\Im\rho|} \le A\log(n+2)(1+\log n),\quad A=1+2b_1+2b_2+2b_3/\log2. \] -/)
  (proof := /-- Apply the weighted unit-window lemma with weights the orders of the zeros; the
  window count is the bound on $N(k+1)-N(k)$. -/)
  (uses := ["rh-weighted-sum-inv-heights-le", "rh-zeroes-sum-window-le"])
  (latexEnv := "lemma")]
lemma riemannZeta.zeroes_sum_inv_im_le {b₁ b₂ b₃ : ℝ} (h1 : 0 ≤ b₁) (h2 : 0 ≤ b₂) (h3 : 0 ≤ b₃)
    (hR : riemannZeta.Riemann_vonMangoldt_bound b₁ b₂ b₃) {n : ℕ} (hn : 2 ≤ n) :
    zeroes_sum (Set.univ : Set ℝ) (Set.Ico (2 : ℝ) n) (fun ρ ↦ 1 / |ρ.im|) ≤
      (1 + 2 * b₁ + 2 * b₂ + 2 * b₃ / log 2) * log (n + 2) * (1 + log n) := by
  classical
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hI : (zeroes_rect (Set.univ : Set ℝ) (Set.Ico (2 : ℝ) n)).Finite :=
    (Kadiri.zeroes_rect_univ_positive_height_finite n).subset fun z hz =>
      ⟨hz.1, ⟨by linarith [hz.2.1.1], hz.2.1.2⟩, hz.2.2⟩
  set A := 1 + 2 * b₁ + 2 * b₂ + 2 * b₃ / log 2 with hAdef
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by positivity
  rw [zeroes_sum_eq_finset _ _ _ hI]
  have hmain := sum_div_abs_le_of_weighted_window_count hI.toFinset (fun ρ : ℂ => ρ.im)
    (fun ρ => (order ρ : ℝ)) (T := n) (A := A) hA (by linarith)
    (fun ρ hρ => by
      simp only [Set.Finite.mem_toFinset, zeroes_rect, Set.mem_ofPred_eq] at hρ
      have hz : ρ ∈ zeroes_rect (Set.univ : Set ℝ) (Set.Ioo 0 (n : ℝ)) :=
        ⟨Set.mem_univ _, ⟨by linarith [hρ.2.1.1], hρ.2.1.2⟩, hρ.2.2⟩
      have : (1 : ℤ) ≤ order ρ :=
        Kadiri.riemannZeta_one_le_order_nontrivialZero ⟨ρ,
          Kadiri.positiveHeightZero_re_mem_Ioo ⟨ρ, hz⟩, Set.mem_univ _, hρ.2.2⟩
      exact_mod_cast (by omega : (0 : ℤ) ≤ order ρ))
    (fun ρ hρ => by
      simp only [Set.Finite.mem_toFinset, zeroes_rect, Set.mem_ofPred_eq] at hρ
      have h2' := hρ.2.1.1
      rw [abs_of_pos (by linarith)]
      exact ⟨by linarith, hρ.2.1.2.le⟩)
    (fun k => by
      by_cases hk : 2 ≤ k ∧ (k : ℝ) < n
      · have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
        have hW : (zeroes_rect (Set.univ : Set ℝ) (Set.Ico (k : ℝ) (k + 1))).Finite :=
          (Kadiri.zeroes_rect_univ_positive_height_finite (k + 1)).subset fun z hz =>
            ⟨hz.1, ⟨by linarith [hz.2.1.1], hz.2.1.2⟩, hz.2.2⟩
        have hset : (hI.toFinset.filter fun ρ : ℂ => ⌊|ρ.im|⌋₊ = k) = hW.toFinset := by
          ext ρ
          simp only [Finset.mem_filter, Set.Finite.mem_toFinset, zeroes_rect, Set.mem_ofPred_eq,
            Set.mem_univ, true_and, Set.mem_Ico]
          have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk.2
          constructor
          · rintro ⟨⟨⟨h0, h1⟩, hz⟩, hf⟩
            have hf' := (Nat.floor_eq_iff (abs_nonneg _)).mp hf
            rw [abs_of_pos (by linarith)] at hf'
            exact ⟨⟨hf'.1, hf'.2⟩, hz⟩
          · rintro ⟨⟨h0, h1⟩, hz⟩
            refine ⟨⟨⟨by linarith, by linarith⟩, hz⟩, ?_⟩
            rw [Nat.floor_eq_iff (abs_nonneg _), abs_of_pos (by linarith)]
            exact ⟨h0, h1⟩
        rw [hset, ← zeroes_sum_one_eq_finset _ _ hW]
        exact zeroes_sum_Ico_nat_le h1 h2 h3 hR hk.1
      · have hempty : (hI.toFinset.filter fun ρ : ℂ => ⌊|ρ.im|⌋₊ = k) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro ρ hρ hf
          simp only [Set.Finite.mem_toFinset, zeroes_rect, Set.mem_ofPred_eq, Set.mem_univ,
            true_and, Set.mem_Ico] at hρ
          have hf' := (Nat.floor_eq_iff (abs_nonneg _)).mp hf
          rw [abs_of_pos (by linarith [hρ.1.1])] at hf'
          apply hk
          have hk2 : 2 ≤ k := by
            rw [← hf]
            exact Nat.le_floor (by rw [abs_of_pos (by linarith [hρ.1.1])]; exact_mod_cast hρ.1.1)
          exact ⟨hk2, by linarith [hρ.1.2, hf'.1]⟩
        rw [hempty, Finset.sum_empty]
        have : 0 ≤ log ((k : ℝ) + 2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
        positivity)
  refine le_of_eq_of_le (Finset.sum_congr rfl fun ρ _ => ?_) hmain
  ring

lemma riemannZeta.order_nonneg_of_pos_im {ρ : ℂ} (hz : riemannZeta ρ = 0) (him : 0 < ρ.im) :
    (0 : ℝ) ≤ order ρ := by
  have hmem : ρ ∈ riemannZeta.zeroes_rect (Set.univ : Set ℝ) (Set.Ioo 0 (ρ.im + 1)) :=
    ⟨Set.mem_univ _, ⟨him, by linarith⟩, hz⟩
  have : (1 : ℤ) ≤ order ρ :=
    Kadiri.riemannZeta_one_le_order_nontrivialZero ⟨ρ,
      Kadiri.positiveHeightZero_re_mem_Ioo ⟨ρ, hmem⟩, Set.mem_univ _, hz⟩
  exact_mod_cast (by omega : (0 : ℤ) ≤ order ρ)

@[blueprint
  "rh-psi-von-koch-of-explicit-formula-zeroes-sum"
  (title := "Von Koch from an explicit-formula bound and an RvM estimate")
  (statement := /-- Assume RH and an estimate
  $|N(T)-\frac{T}{2\pi}\log\frac{T}{2\pi e}-\frac78|\le b_1\log T+b_2\log\log T+b_3$ ($T\ge2$,
  $b_i\ge0$). Suppose that for $x\ge16$ and $n=\lfloor\sqrt{x}\rfloor$,
  \[ |\psi(x)-x| \le 2\sum_{2\le\Im\rho<n}\Bigl|\frac{x^\rho}{\rho}\Bigr| + C\sqrt{x}\log^2 x \]
  (sum over zeros with multiplicity; the factor $2$ accounts for the conjugate zeros, and the
  zeros of height $<2$ together with the truncation tail are absorbed in $C\sqrt{x}\log^2 x$).
  Then $\psi(x)=x+O(\sqrt{x}\log^2 x)$. The explicit-formula hypothesis is \emph{not} proved
  here; the Riemann--von Mangoldt estimate is a hypothesis. -/)
  (proof := /-- Bound each term by $\sqrt{x}/\Im\rho$ and apply the sum estimate for $1/|\Im\rho|$. -/)
  (uses := ["rh-norm-cpow-div-zero", "rh-zeroes-sum-inv-im-le"])
  (latexEnv := "theorem")]
theorem psi_sub_self_isBigO_of_explicit_formula_zeroes_sum (RH : RiemannHypothesis)
    {b₁ b₂ b₃ C : ℝ} (h1 : 0 ≤ b₁) (h2 : 0 ≤ b₂) (h3 : 0 ≤ b₃)
    (hR : riemannZeta.Riemann_vonMangoldt_bound b₁ b₂ b₃)
    (hexp : ∀ x : ℝ, 16 ≤ x →
      |ψ x - x| ≤ 2 * riemannZeta.zeroes_sum (Set.univ : Set ℝ) (Set.Ico (2 : ℝ) ⌊√x⌋₊)
        (fun ρ ↦ ‖(x : ℂ) ^ ρ / ρ‖) + C * (√x * (log x) ^ 2)) :
    (fun x : ℝ ↦ ψ x - x) =O[atTop] fun x : ℝ ↦ √x * (log x) ^ 2 := by
  classical
  set A := 1 + 2 * b₁ + 2 * b₂ + 2 * b₃ / log 2 with hAdef
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by positivity
  refine IsBigO.of_bound (2 * A + C) ?_
  filter_upwards [eventually_ge_atTop (16 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hsq : 0 ≤ √x := Real.sqrt_nonneg x
  have hpos : 0 ≤ √x * (log x) ^ 2 := by positivity
  have hs4 : (4 : ℝ) ≤ √x := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  set n := ⌊√x⌋₊ with hn
  have hn4 : 4 ≤ n := Nat.le_floor (by exact_mod_cast hs4)
  have hn2 : 2 ≤ n := by omega
  have hnx : (n : ℝ) ≤ √x := Nat.floor_le hsq
  have hI : (riemannZeta.zeroes_rect (Set.univ : Set ℝ) (Set.Ico (2 : ℝ) n)).Finite :=
    (Kadiri.zeroes_rect_univ_positive_height_finite n).subset fun z hz =>
      ⟨hz.1, ⟨by linarith [hz.2.1.1], hz.2.1.2⟩, hz.2.2⟩
  -- termwise comparison
  have hterm : riemannZeta.zeroes_sum (Set.univ : Set ℝ) (Set.Ico (2 : ℝ) n)
      (fun ρ ↦ ‖(x : ℂ) ^ ρ / ρ‖) ≤
      √x * riemannZeta.zeroes_sum (Set.univ : Set ℝ) (Set.Ico (2 : ℝ) n)
        (fun ρ ↦ 1 / |ρ.im|) := by
    rw [riemannZeta.zeroes_sum_eq_finset _ _ _ hI, riemannZeta.zeroes_sum_eq_finset _ _ _ hI,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    simp only [Set.Finite.mem_toFinset, riemannZeta.zeroes_rect, Set.mem_ofPred_eq, Set.mem_univ,
      true_and, Set.mem_Ico] at hρ
    obtain ⟨⟨h2im, hlt⟩, hz⟩ := hρ
    have him : ρ.im ≠ 0 := by linarith
    have hord := riemannZeta.order_nonneg_of_pos_im hz (by linarith)
    have htriv : ¬∃ m : ℕ, ρ = -2 * (m + 1) := by
      rintro ⟨m, hm⟩
      apply him
      rw [hm]; simp
    have hne1 : ρ ≠ 1 := by
      intro h; apply him; rw [h]; simp
    have hb := (RH.norm_cpow_div_nontrivialZero hz htriv hne1 hx0).2.2 him
    calc ‖(x : ℂ) ^ ρ / ρ‖ * (riemannZeta.order ρ : ℝ)
        ≤ √x / |ρ.im| * (riemannZeta.order ρ : ℝ) := mul_le_mul_of_nonneg_right hb hord
      _ = √x * (1 / |ρ.im| * (riemannZeta.order ρ : ℝ)) := by ring
  have hmain := riemannZeta.zeroes_sum_inv_im_le h1 h2 h3 hR hn2
  -- arithmetic: log(n+2)(1+log n) ≤ log^2 x
  have hlogx2 : 2 ≤ log x := by
    have h16 : log 16 ≤ log x := Real.log_le_log (by norm_num) hx
    have : log 16 = 4 * log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have h2' : (0.69 : ℝ) < log 2 := by
      have := Real.log_two_gt_d9; linarith
    linarith
  have hlogs : log (√x) = log x / 2 := Real.log_sqrt (by linarith)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hA1 : log ((n : ℝ) + 2) ≤ log x := by
    have : log ((n : ℝ) + 2) ≤ log (2 * √x) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith), hlogs] at this
    have h2' : log 2 ≤ log x / 2 := by
      have h4 : log 4 ≤ log x := Real.log_le_log (by norm_num) (by linarith)
      have : log 4 = 2 * log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith
    linarith
  have hB : 1 + log (n : ℝ) ≤ log x := by
    have := Real.log_le_log hnpos hnx
    rw [hlogs] at this
    linarith
  have hlogn : 0 ≤ log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hlogxnn : 0 ≤ log x := by linarith
  have hsum : A * log ((n : ℝ) + 2) * (1 + log (n : ℝ)) ≤ A * (log x) ^ 2 := by
    calc A * log ((n : ℝ) + 2) * (1 + log (n : ℝ)) ≤ A * log x * (1 + log (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA1 hA)
            (by have := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast (by omega : 1 ≤ n)); linarith)
      _ ≤ A * log x * log x := mul_le_mul_of_nonneg_left hB (mul_nonneg hA hlogxnn)
      _ = A * (log x) ^ 2 := by ring
  have hZ : riemannZeta.zeroes_sum (Set.univ : Set ℝ) (Set.Ico (2 : ℝ) n)
      (fun ρ ↦ ‖(x : ℂ) ^ ρ / ρ‖) ≤ A * (√x * (log x) ^ 2) := by
    calc _ ≤ √x * riemannZeta.zeroes_sum (Set.univ : Set ℝ) (Set.Ico (2 : ℝ) n)
          (fun ρ ↦ 1 / |ρ.im|) := hterm
      _ ≤ √x * (A * (log x) ^ 2) :=
          mul_le_mul_of_nonneg_left (hmain.trans hsum) hsq
      _ = A * (√x * (log x) ^ 2) := by ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos]
  have := hexp x hx
  nlinarith

/-- The zeros with positive height in `[2, n)` form a finite set. -/
lemma riemannZeta.zeroes_rect_Ico_two_finite (n : ℝ) :
    (zeroes_rect (Set.univ : Set ℝ) (Set.Ico (2 : ℝ) n)).Finite :=
  (Kadiri.zeroes_rect_univ_positive_height_finite n).subset fun z hz =>
    ⟨hz.1, ⟨by linarith [hz.2.1.1], hz.2.1.2⟩, hz.2.2⟩

/-- Zeros of height in `(-n, -2]` are the conjugates of those of height in `[2, n)`. -/
lemma riemannZeta.zeroes_rect_Ioc_neg_finite (n : ℝ) :
    (zeroes_rect (Set.univ : Set ℝ) (Set.Ioc (-n) (-2 : ℝ))).Finite := by
  refine ((zeroes_rect_Ico_two_finite n).image (starRingEnd ℂ)).subset fun z hz => ?_
  refine ⟨starRingEnd ℂ z, ⟨Set.mem_univ _, ?_, ?_⟩, Complex.conj_conj z⟩
  · simp only [Complex.conj_im, Set.mem_Ico]
    constructor <;> linarith [hz.2.1.1, hz.2.1.2]
  · have h : riemannZeta z = 0 := hz.2.2
    change riemannZeta (starRingEnd ℂ z) = 0
    rw [riemannZeta_conj, h, map_zero]

@[blueprint
  "rh-zeroes-sum-neg-eq"
  (title := "Zeros of negative height by conjugation")
  (statement := /-- If $f(\bar\rho)=f(\rho)$ for all $\rho$, then the sum of $f$ over the zeros of
  $\zeta$ (with multiplicity) with $-n<\Im\rho\le-2$ equals the sum over those with
  $2\le\Im\rho<n$. -/)
  (proof := /-- Complex conjugation is a bijection between the two finite sets of zeros, and
  preserves the order of a zero. -/)
  (latexEnv := "lemma")]
lemma riemannZeta.zeroes_sum_neg_eq (n : ℝ) (f : ℂ → ℝ) (hf : ∀ ρ, f (starRingEnd ℂ ρ) = f ρ) :
    zeroes_sum (Set.univ : Set ℝ) (Set.Ioc (-n) (-2 : ℝ)) f =
      zeroes_sum (Set.univ : Set ℝ) (Set.Ico (2 : ℝ) n) f := by
  classical
  have hP := zeroes_rect_Ico_two_finite n
  have hN := zeroes_rect_Ioc_neg_finite n
  rw [zeroes_sum_eq_finset _ _ _ hN, zeroes_sum_eq_finset _ _ _ hP]
  refine Finset.sum_nbij' (starRingEnd ℂ) (starRingEnd ℂ) ?_ ?_ ?_ ?_ ?_
  · intro ρ hρ
    simp only [Set.Finite.mem_toFinset, zeroes_rect, Set.mem_ofPred_eq, Set.mem_univ, true_and,
      Set.mem_Ioc, Set.mem_Ico, Complex.conj_im] at hρ ⊢
    refine ⟨⟨by linarith [hρ.1.2], by linarith [hρ.1.1]⟩, ?_⟩
    change riemannZeta (starRingEnd ℂ ρ) = 0
    rw [riemannZeta_conj, show riemannZeta ρ = 0 from hρ.2, map_zero]
  · intro ρ hρ
    simp only [Set.Finite.mem_toFinset, zeroes_rect, Set.mem_ofPred_eq, Set.mem_univ, true_and,
      Set.mem_Ioc, Set.mem_Ico, Complex.conj_im] at hρ ⊢
    refine ⟨⟨by linarith [hρ.1.2], by linarith [hρ.1.1]⟩, ?_⟩
    change riemannZeta (starRingEnd ℂ ρ) = 0
    rw [riemannZeta_conj, show riemannZeta ρ = 0 from hρ.2, map_zero]
  · intro ρ _; exact Complex.conj_conj ρ
  · intro ρ _; exact Complex.conj_conj ρ
  · intro ρ hρ
    simp only [Set.Finite.mem_toFinset, zeroes_rect, Set.mem_ofPred_eq, Set.mem_univ, true_and,
      Set.mem_Ioc] at hρ
    have hne : ρ ≠ 1 := by
      intro h; have := hρ.1.2; rw [h] at this; simp at this; linarith
    rw [hf, Kadiri.riemannZeta_order_conj hne]

@[blueprint
  "rh-zeroes-sum-abs-eq-two-mul"
  (title := "Symmetric height window is twice the positive one")
  (statement := /-- If $f(\bar\rho)=f(\rho)$ for all $\rho$, the sum of $f$ over the zeros with
  $2\le|\Im\rho|<n$ is twice the sum over those with $2\le\Im\rho<n$. -/)
  (proof := /-- Split the symmetric window into positive and negative heights and apply the
  conjugation lemma. -/)
  (uses := ["rh-zeroes-sum-neg-eq"])
  (latexEnv := "lemma")]
lemma riemannZeta.zeroes_sum_abs_eq_two_mul (n : ℝ) (f : ℂ → ℝ)
    (hf : ∀ ρ, f (starRingEnd ℂ ρ) = f ρ) :
    zeroes_sum (Set.univ : Set ℝ) {t : ℝ | 2 ≤ |t| ∧ |t| < n} f =
      2 * zeroes_sum (Set.univ : Set ℝ) (Set.Ico (2 : ℝ) n) f := by
  classical
  have hP := zeroes_rect_Ico_two_finite n
  have hN := zeroes_rect_Ioc_neg_finite n
  have hset : zeroes_rect (Set.univ : Set ℝ) {t : ℝ | 2 ≤ |t| ∧ |t| < n} =
      zeroes_rect (Set.univ : Set ℝ) (Set.Ico (2 : ℝ) n) ∪
        zeroes_rect (Set.univ : Set ℝ) (Set.Ioc (-n) (-2 : ℝ)) := by
    ext z
    simp only [zeroes_rect, Set.mem_ofPred_eq, Set.mem_univ, true_and, Set.mem_union,
      Set.mem_Ico, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨h2, hn⟩, hz⟩
      rcases le_or_gt 0 z.im with h0 | h0
      · rw [abs_of_nonneg h0] at h2 hn; exact Or.inl ⟨⟨h2, hn⟩, hz⟩
      · rw [abs_of_neg h0] at h2 hn
        exact Or.inr ⟨⟨by linarith, by linarith⟩, hz⟩
    · rintro (⟨⟨h2, hn⟩, hz⟩ | ⟨⟨h2, hn⟩, hz⟩)
      · rw [abs_of_nonneg (by linarith)]; exact ⟨⟨h2, hn⟩, hz⟩
      · rw [abs_of_neg (by linarith)]; exact ⟨⟨by linarith, by linarith⟩, hz⟩
  have hJ : (zeroes_rect (Set.univ : Set ℝ) {t : ℝ | 2 ≤ |t| ∧ |t| < n}).Finite := by
    rw [hset]; exact hP.union hN
  have hdisj : Disjoint hP.toFinset hN.toFinset := by
    rw [Finset.disjoint_left]
    intro z h1 h2
    simp only [Set.Finite.mem_toFinset, zeroes_rect, Set.mem_ofPred_eq] at h1 h2
    linarith [h1.2.1.1, h2.2.1.2]
  have hfs : hJ.toFinset = hP.toFinset ∪ hN.toFinset := by
    ext z; simp [hset]
  have hneg := zeroes_sum_neg_eq n f hf
  rw [zeroes_sum_eq_finset _ _ _ hJ, hfs, Finset.sum_union hdisj,
    ← zeroes_sum_eq_finset _ _ _ hP, ← zeroes_sum_eq_finset _ _ _ hN, hneg]
  ring

@[blueprint
  "rh-psi-von-koch-of-symmetric-explicit-formula"
  (title := "Von Koch from a symmetric explicit-formula bound and an RvM estimate")
  (statement := /-- Assume RH and an estimate
  $|N(T)-\frac{T}{2\pi}\log\frac{T}{2\pi e}-\frac78|\le b_1\log T+b_2\log\log T+b_3$
  ($T\ge2$, $b_i\ge0$). Suppose that for $x\ge16$ and $n=\lfloor\sqrt{x}\rfloor$,
  \[ |\psi(x)-x| \le \sum_{2\le|\Im\rho|<n}\Bigl|\frac{x^\rho}{\rho}\Bigr|
     + C\sqrt{x}\log^2 x \]
  (sum over all zeros of both signs of height, with multiplicity). Then
  $\psi(x)=x+O(\sqrt{x}\log^2 x)$. The explicit-formula hypothesis is \emph{not} proved here. -/)
  (proof := /-- The terms for $\rho$ and $\bar\rho$ have equal norm, so the symmetric sum is twice
  the sum over positive heights; apply the one-sided result. -/)
  (uses := ["rh-psi-von-koch-of-explicit-formula-zeroes-sum", "rh-zeroes-sum-abs-eq-two-mul"])
  (latexEnv := "theorem")]
theorem psi_sub_self_isBigO_of_symmetric_explicit_formula (RH : RiemannHypothesis)
    {b₁ b₂ b₃ C : ℝ} (h1 : 0 ≤ b₁) (h2 : 0 ≤ b₂) (h3 : 0 ≤ b₃)
    (hR : riemannZeta.Riemann_vonMangoldt_bound b₁ b₂ b₃)
    (hexp : ∀ x : ℝ, 16 ≤ x →
      |ψ x - x| ≤ riemannZeta.zeroes_sum (Set.univ : Set ℝ)
        {t : ℝ | 2 ≤ |t| ∧ |t| < (⌊√x⌋₊ : ℝ)} (fun ρ ↦ ‖(x : ℂ) ^ ρ / ρ‖) +
        C * (√x * (log x) ^ 2)) :
    (fun x : ℝ ↦ ψ x - x) =O[atTop] fun x : ℝ ↦ √x * (log x) ^ 2 := by
  refine psi_sub_self_isBigO_of_explicit_formula_zeroes_sum RH h1 h2 h3 hR (C := C) fun x hx => ?_
  have hx0 : 0 < x := by linarith
  have hsym := riemannZeta.zeroes_sum_abs_eq_two_mul (⌊√x⌋₊ : ℝ)
    (fun ρ ↦ ‖(x : ℂ) ^ ρ / ρ‖) fun ρ => by
      simp only [Complex.norm_div]
      congr 1
      · rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        simp
      · simp
  have := hexp x hx
  rw [hsym] at this
  exact this

@[blueprint
  "rh-psi-explicit-formula-bound"
  (title := "Truncated explicit formula for $\\psi$, in bounded form")
  (statement := /-- For $C\in\mathbb{R}$, the statement that for all $x\ge16$,
  \[ |\psi(x)-x| \le \sum_{2\le|\Im\rho|<\lfloor\sqrt{x}\rfloor}\Bigl|\frac{x^\rho}{\rho}\Bigr|
     + C\sqrt{x}\log^2 x, \]
  the sum running over the zeros of $\zeta$ with multiplicity. This is the consequence of the
  truncated explicit formula for $\psi$ needed for von Koch's theorem; it is the statement of the
  proposition only and is not proved here. -/)
  (latexEnv := "definition")]
def PsiSymmetricExplicitFormulaBound (C : ℝ) : Prop :=
  ∀ x : ℝ, 16 ≤ x →
    |ψ x - x| ≤ riemannZeta.zeroes_sum (Set.univ : Set ℝ)
      {t : ℝ | 2 ≤ |t| ∧ |t| < (⌊√x⌋₊ : ℝ)} (fun ρ ↦ ‖(x : ℂ) ^ ρ / ρ‖) +
      C * (√x * (log x) ^ 2)

@[blueprint
  "rh-psi-von-koch-of-explicit-formula"
  (title := "Von Koch's bound from the explicit-formula bound and an RvM estimate")
  (statement := /-- If the bounded explicit formula holds for some $C$ and the
  Riemann--von Mangoldt estimate holds with some $b_1,b_2,b_3\ge0$, then von Koch's bound
  $\psi(x)=x+O(\sqrt{x}\log^2x)$ holds under RH. -/)
  (proof := /-- Apply the symmetric explicit-formula theorem. -/)
  (uses := ["rh-psi-von-koch-of-symmetric-explicit-formula", "rh-psi-explicit-formula-bound",
    "rh-psi-von-koch-bound"])
  (latexEnv := "theorem")]
theorem RHPsiVonKochBound_of_explicit_formula {b₁ b₂ b₃ C : ℝ} (h1 : 0 ≤ b₁) (h2 : 0 ≤ b₂)
    (h3 : 0 ≤ b₃) (hR : riemannZeta.Riemann_vonMangoldt_bound b₁ b₂ b₃)
    (hE : PsiSymmetricExplicitFormulaBound C) : RHPsiVonKochBound :=
  fun RH => psi_sub_self_isBigO_of_symmetric_explicit_formula RH h1 h2 h3 hR hE

/-- Theta version of `RHPsiVonKochBound_of_explicit_formula`. -/
theorem RHThetaVonKochBound_of_explicit_formula {b₁ b₂ b₃ C : ℝ} (h1 : 0 ≤ b₁) (h2 : 0 ≤ b₂)
    (h3 : 0 ≤ b₃) (hR : riemannZeta.Riemann_vonMangoldt_bound b₁ b₂ b₃)
    (hE : PsiSymmetricExplicitFormulaBound C) : RHThetaVonKochBound :=
  RHThetaVonKochBound_of_psi (RHPsiVonKochBound_of_explicit_formula h1 h2 h3 hR hE)

@[blueprint
  "rh-theta-explicit-of-schoenfeld-psi"
  (title := "Explicit bound for $\\theta$ from Schoenfeld's bound for $\\psi$")
  (statement := /-- Schoenfeld's explicit bound for $\psi$ under RH implies, for $x\ge73.2$ (so that
  $x\ge1$),
  \[ |\theta(x)-x| < \frac{\sqrt{x}\log^2x}{8\pi} + 2\sqrt{x}\log x. \] -/)
  (proof := /-- $0\le\psi(x)-\theta(x)\le2\sqrt{x}\log x$, so
  $|\theta(x)-x|\le|\psi(x)-x|+(\psi(x)-\theta(x))$. -/)
  (uses := ["rh-psi-schoenfeld-bound"])
  (latexEnv := "theorem")]
theorem RHPsiSchoenfeldBound.theta_explicit (h : RHPsiSchoenfeldBound) (RH : RiemannHypothesis)
    {x : ℝ} (hx : 73.2 ≤ x) :
    |θ x - x| < √x * (log x) ^ 2 / (8 * π) + 2 * √x * log x := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hd := Chebyshev.psi_sub_theta_le hx1
  have hd0 := sub_nonneg.mpr (Chebyshev.theta_le_psi x)
  have hψ := h RH x hx
  have : |θ x - x| ≤ |ψ x - x| + (ψ x - θ x) := by
    rw [abs_le]; constructor <;> cases abs_cases (ψ x - x) <;>
      linarith [neg_abs_le (ψ x - x), le_abs_self (ψ x - x)]
  linarith
