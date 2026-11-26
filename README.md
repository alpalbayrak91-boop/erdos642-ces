# The Chen–Erdős–Staton bound for Erdős Problem 642, in Lean 4

Let $f(n)$ be the maximal number of edges of a graph on $n$ vertices in which every cycle has
more vertices than chords. [Erdős Problem 642](https://www.erdosproblems.com/642) (Hamburger and
Szegedy) asks whether $f(n) \ll n$. That question is open.

This repository contains a machine-checked proof of the bound attributed to Chen, Erdős and Staton,

$$f(n) \ll n^{3/2},$$

in the explicit form $f(n) \le 2(\lfloor\sqrt n\rfloor + 1)\,n$ for every $n$.

The asymptotic statement is `Erdos642.erdos_642.variants.upper_bound_n_pow_three_halves` of
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/ErdosProblems/642.lean),
where it is stated without proof. The definitions and that statement are copied verbatim.

## Layout

- `Challenge.lean`: the two definitions and the two statements, with `sorry`. This is the part to audit.
- `Solution.lean`: the same statements, proved.
- `Erdos642CES/LongestPath.lean`: the argument.
- `Erdos642CES/Main.lean`: the explicit bound and the asymptotic statement.
- `comparator.json`, `formalization.yaml`: [Palomar](https://palomar-registry.org/) metadata.

## The argument

Delete vertices of degree at most $d$ one at a time. If this removes every edge, the graph has at
most $dn$ edges. Otherwise we reach a graph in which every non-isolated vertex has degree at least
$d$. Take a longest path $x_1 \dots x_m$ in it and let $x_j$ be the last neighbour of $x_1$, the
pair being chosen so that $j$ is maximal. If $x_i$ is a neighbour of $x_1$, then
$x_{i-1} \dots x_1 x_i \dots x_m$ is again a longest path, so by the choice of $j$ all neighbours
of $x_{i-1}$ lie on the cycle $x_1 \dots x_j$. This gives $d$ vertices of the cycle all of whose
at least $d$ neighbours lie on the cycle, hence at least $d^2/2$ edges among its $j \le n$
vertices. If $d^2 \ge 4n$, at least $j$ of them are chords.

## Checking

```text
lake exe cache get
lake build
./scripts/verify-comparator.sh
```

Lean `v4.37.0-rc1`, Mathlib pinned in `lake-manifest.json`. Both theorems depend only on
`propext`, `Classical.choice` and `Quot.sound`.

## Provenance and disclosure

The proof was written by an AI agent (Claude, via Claude Code) and checked by Lean; no human
edited the Lean source, and no human has reviewed the mathematics line by line. It is a longest
path rotation argument written without consulting the Chen–Erdős–Staton paper, so it is not
claimed to be the proof given there. Details are in `formalization.yaml`.

Palomar submissions go through <https://submit.palomar-registry.org/>.

## References

- G. Chen, P. Erdős, W. Staton, *Proof of a conjecture of Bollobás on nested cycles*,
  J. Combin. Theory Ser. B 66 (1996), 38–43.
- N. Draganić, A. Methuku, D. Munhá Correia, B. Sudakov, *Cycles with many chords*,
  Random Structures Algorithms 64 (2024), 3–16.
