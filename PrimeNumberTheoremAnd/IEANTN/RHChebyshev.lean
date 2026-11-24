module

public import Architect
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Asymptotics.Lemmas
public import PrimeNumberTheoremAnd.Defs

@[expose] public section

open Real Filter Asymptotics
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
