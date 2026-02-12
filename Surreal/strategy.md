## **Yes — to make the toy model precise you must re-index both (i)/(ii) *and* (iii) by the *same* ordinal “stage”, not by the raw tuple**

You’re right that as written:

- (i),(ii) are naturally indexed by a **pair** $(x,y)$,
- (iii) is naturally indexed by a **quadruple** $(x_1,x_2,y_1,y_2)$,

so it’s not literally $A_n$ vs $B_n$ with the *same* kind of $n$.

The standard way to make Conway’s argument completely non-circular is:

1. pick a single well-founded **complexity measure for a product** $uv$ (so it’s about **pairs**),
2. use that single measure as the outer induction index $\alpha$,
3. at each stage $\alpha$, prove:
   - all product facts (i),(ii) for products of complexity $<\alpha$,
   - then all $P$-inequalities (iii) whose products all have complexity $<\alpha$.

That makes the “toy model” exact: the shared index is the **stage** $\alpha$.

---

# 1) A single complexity measure for products

Let $\beta(x)$ be the birthday of a number $x$.

Define the **product-rank** (many choices work) e.g.
$$
\rho(u,v) := \beta(u)+\beta(v)
$$
(ordinal addition).

Key property: if $u'$ is an option of $u$, then $\beta(u')<\beta(u)$, hence
$$
\rho(u',v) < \rho(u,v),
\qquad
\rho(u,v') < \rho(u,v)
$$
whenever $v'$ is an option of $v$.

So **replacing either factor by an option strictly lowers** $\rho$.

---

# 2) Re-index both families of statements by the same stage $\alpha$

Now define two *stage-indexed* assertions, both indexed by the same ordinal $\alpha$:

### **$A(\alpha)$**  (products up to stage $\alpha$)
> For all pairs $(x,y)$ with $\rho(x,y)<\alpha$, statements **(i)** and **(ii)** hold for $xy$.

### **$B(\alpha)$**  (all $P$-inequalities up to stage $\alpha$)
> For all quadruples $(x_1,x_2,y_1,y_2)$ such that
> $\rho(x_i,y_j)<\alpha$ for all $i,j\in\{1,2\}$, statement **(iii)** (i.e. $P(x_1,x_2:y_1,y_2)$) holds.

So in the “toy model” language:

- the role of **$n$** is played by **$\alpha$**,
- $A(\alpha)$ quantifies over *all pairs* below stage $\alpha$,
- $B(\alpha)$ quantifies over *all quadruples* whose **four products** lie below stage $\alpha$.

This is how you put (i)/(ii) and (iii) on a common induction timeline.

---

# 3) The induction step and where the apparent circle is broken

We prove, by transfinite induction on $\alpha$, the pair of statements:

> **For every $\alpha$: first prove $A(\alpha)$, then prove $B(\alpha)$.**

Assume for all $\beta<\alpha$ we already have both $A(\beta)$ and $B(\beta)$.

---

## 3.1 Proving **$A(\alpha)$** uses only **earlier** $B(\beta)$’s

Fix $(x,y)$ with $\rho(x,y)<\alpha$. In Conway’s proof of (i) for $xy$, he uses instances of (iii) like
$$
P(x^{L_2},x : y^L,y^R).
$$

Look at the **four products** inside that $P$:

- $x^{L_2}y^L$, $x^{L_2}y^R$, $xy^L$, $xy^R$.

Each has strictly smaller rank than $xy$ because **at least one factor is an option**:
$$
\rho(x,y^L)<\rho(x,y),\quad \rho(x^{L_2},y^R)<\rho(x,y),\ \text{etc.}
$$

So that particular $P$-statement lies inside **$B(\rho(x,y))$**, and since $\rho(x,y)<\alpha$, we have $\rho(x,y)<\alpha$ hence **$B(\rho(x,y))$ is already known** from the induction hypothesis (it’s a “previous stage” because its index is $<\alpha$).

**Conclusion:** when proving (i),(ii) for $xy$ at stage $\alpha$, you only ever use (iii) for strictly smaller product-ranks, i.e. already-proved $B(\beta)$ with $\beta<\alpha$.
So there is no need to assume $B(\alpha)$ while proving $A(\alpha)$.

That’s the crucial non-circular direction.

---

## 3.2 Proving **$B(\alpha)$** is allowed to use **$A(\alpha)$**

Now take a quadruple with all four product ranks $<\alpha$.

Conway reduces (iii) to base cases like
$$
P(x^L,x : y^L,y).
$$
Rearranging gives
$$
x^Ly + xy^L - x^Ly^L < xy,
$$
and the left-hand side is literally a **left option** of $xy$.

So to finish the base case, he uses: “left options of $xy$ are $<xy$”, i.e. **(i) for $xy$**.

But notice: here $xy$ has $\rho(x,y)<\alpha$, so **(i) for $xy$ is part of $A(\alpha)$**, and we have already proved $A(\alpha)$ *before* starting $B(\alpha)$.

So inside stage $\alpha$, the dependency is:

- first establish all product facts $A(\alpha)$,
- then use them to discharge the base cases in $B(\alpha)$.

This is exactly the toy-model pattern “prove $A_n$ first, then $B_n$ can use $A_n$”.

(Within $B(\alpha)$ there is also an *inner* induction on “simplicity of the quadruple” when Conway replaces $x_1$ by $x_1^R$, etc.; that inner induction stays inside the same $\alpha$ and is well-founded because options have smaller birthdays.)

---

# 4) Summary: the precise correspondence to the toy model

- The shared “index” is **$\alpha$**, an ordinal stage controlling which **products** are already available.
- $A(\alpha)$ = “(i),(ii) hold for all products of rank $<\alpha$”.
- $B(\alpha)$ = “(iii) holds for all $P$-statements whose four products have rank $<\alpha$”.
- Proof order at each stage: **$A(\alpha)$ first**, then **$B(\alpha)$**.
- Thus:
  - $A(\alpha)$ uses only $B(\beta)$ for $\beta<\alpha$,
  - $B(\alpha)$ may use $A(\alpha)$ (same stage) without circularity.
