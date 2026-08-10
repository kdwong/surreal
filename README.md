# A Baby Construction of Surreal Numbers in Lean 4

A baby construction of surreal numbers in Lean 4, initiated as an undergraduate
independent study project in Fall 2025.

We formalize addition and multiplication on surreal numbers and prove that the
resulting structure is a linearly ordered commutative ring.

## Blueprint

The mathematical blueprint and theorem dependency graph live in
[`blueprint/`](blueprint/). They document the Lean proof path from finite games and
the recursive order, through the simultaneous Conway A/B/C induction, to the linearly
ordered commutative ring structure on short surreal numbers.

Read the [published web blueprint](https://kdwong.github.io/surreal/blueprint/) or
follow [`blueprint/README.md`](blueprint/README.md) to build it locally. The web
blueprint includes an interactive dependency graph and links each formalized item to
its corresponding Lean declaration.

## References

1. John H. Conway, *[On Numbers and Games](onag1.pdf)*, 2nd ed., A K Peters,
   Natick, Massachusetts, 2001. ISBN 1-56881-127-6.
2. Dierk Schleicher and Michael Stoll, “An Introduction to Conway’s Games and
   Numbers,” *Moscow Mathematical Journal* **6** (2006), no. 2, 359–388.
   [doi:10.17323/1609-4514-2006-6-2-359-388](https://doi.org/10.17323/1609-4514-2006-6-2-359-388).
   A [local copy](Schleicher%20Stoll.pdf) is included in this repository.
3. The mathlib Community,
   [`Mathlib.SetTheory.Surreal.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/Surreal/Basic.html)
   and
   [`Mathlib.SetTheory.Surreal.Multiplication`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/Surreal/Multiplication.html),
   mathlib4 documentation for surreal numbers and their multiplication.
4. ViHdzP, “[Inductive hypothesis in surreal multiplication
   proof](https://math.stackexchange.com/questions/4434631/inductive-hypothesis-in-surreal-multiplication-proof),”
   *Mathematics Stack Exchange*, question 4434631, asked April 23, 2022; answer
   posted May 17, 2022. The answer describes the multiset induction as a hydra
   relation and subsequently identifies it with the Dershowitz–Manna ordering; this
   project uses mathlib’s existing Dershowitz–Manna multiset order directly.
