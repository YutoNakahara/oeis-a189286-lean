# Formal Proof of OEIS A189286 Conjectures (Lean 4)

Complete Lean 4 formalization of two conjectures proposed by Zhi-Wei Sun (2011) for [OEIS A189286](https://oeis.org/A189286), matching the statements in [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/189286.lean):

- `OeisA189286.conjecture_1`: $a(n) \in \mathbb{Z}$ for all $n \ge 0$ (an independent elementary proof of the integrality result earlier proved in T. Adamczewski, [arXiv:2608.11941](https://arxiv.org/abs/2608.11941)).
- `OeisA189286.conjecture_3`: For all $n \ge 1$, $8 \mid a(n)$, and $a(n)/8$ is odd if and only if $n = 2^k$ for some $k \ge 0$ (our original 2-adic proof; listed without proof on OEIS A189286 and marked `research open` in `formal-conjectures` as of November 2026, without claiming an exhaustive literature search ruling out other proofs).

## Verification

    lake exe cache get
    lake build Challenge Solution

Both theorems depend only on the standard Lean axioms `[propext, Classical.choice, Quot.sound]`.

## AI Disclosure

The proofs were developed with AI assistance (`Gemini 4 Neon` via Google Antigravity) and verified by the Lean 4 kernel, with an independent mathematical review of the proof outline using `GPT-5.6 Sol`.
