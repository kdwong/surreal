# 1) A single complexity measure for products

Let $\beta(x)$ be the birthday of a number $x$. Define the **product-rank** e.g.

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

This is how you put (i)/(ii) and (iii) on a common induction timeline.

---

# 3) The induction step

We prove, by transfinite induction on $\alpha$, the pair of statements:

> **For every $\alpha$: first prove $A(\alpha)$, then prove $B(\alpha)$.**

Assume for all $\beta<\alpha$ we already have both $A(\beta)$ and $B(\beta)$.

---

## 3.1 Proving **$A(\alpha)$** uses only **earlier** $B(\beta)$’s

## 3.1.1 Proof of (i)
Fix $(x,y)$ with $\rho(x,y)<\alpha$. In Conway’s proof of (i) for $xy$, one needs to prove 

$$ (xy)^L < (xy)^R $$

which in turn is to prove

$$ x^{L_1}y + xy^L - x^{L_1}y^L < x^{L_2}y + xy^R - x^{L_2}y^R $$

and three other strict inequalities. Here one splits into two cases:

- If $x^{L_1} \leq x^{L_2}$, then combining $y^L < y$, one applies $P(x^{L_1}, x^{L_2} : y^L, y)$ (given by $B(\beta)$) and get

$$x^{L_1}y + x^{L_2}y^L \leq x^{L_1}y^L + x^{L_2}y \quad \Rightarrow x^{L_1}y - x^{L_1}y^L \leq x^{L_2}y - x^{L_2}y^L$$

and hence

$$ x^{L_1}y + xy^L - x^{L_1}y^L \leq x^{L_2}y + xy^L - x^{L_2}y^L < x^{L_2}y + xy^R - x^{L_2}y^R $$

where the last strict inequality comes from $P(x^{L_2},x : y^L,y^R)$.

- If $x^{L_2} \leq x^{L_1}$, we have

$$ x^{L_1}y + xy^L - x^{L_1}y^L \leq x^{L_1}y + xy^R - x^{L_1}y^R < x^{L_2}y + xy^R - x^{L_2}y^R $$

by $P(x^{L_1}, x : y^L, y)$ and $P(x^{L_2}, x^{L_1} : y, y^R)$ respectively.

Check the other three cases. This concludes (i).

## 3.1.2 Proof of (ii)
Assume $x_1=x_2$ as numbers. We have $x_1^L< x_1= x_2$ and $x_2=x_1< x_1^R$, and likewise swapping $1\leftrightarrow 2$.


### **$(x_1y)^L <x_2y$**

Take a left option of $x_1y$ of the first type:

$$
L:=x_1^Ly + x_1y^L - x_1^Ly^L.
$$

Using $x_1^L< x_2$ and $y^L < y$, apply $P(x_1^L,x_2:y^L,y)$:

$$
x_1^Ly + x_2y^L < x_1^Ly^L + x_2y.
$$

Rearrange:

$$
x_1^Ly + x_2y^L - x_1^Ly^L < x_2y.
$$

Now use the induction hypothesis for (ii) on the **simpler** factor $y^L$ (since $y^L$ is an option of $y$):

$$
x_2y^L = x_1y^L.
$$

So

$$
x_1^Ly + x_1y^L - x_1^Ly^L < x_2y,
$$

i.e. $L< x_2y$.

The second family of left options (using $x_1^R,y^R$) is analogous.

### **Right options of $x_1y < (x_2y)^R$**

Take a right option of $x_2y$ of the form

$$
R:=x_2^Ly + x_2y^R - x_2^Ly^R.
$$

Since $x_2^L< x_2=x_1$ and $y< y^R$, apply $P(x_2^L,x_1:y,y^R)$:

$$
x_2^Ly^R + x_1y < x_2^Ly + x_1y^R.
$$

Rearrange:

$$
x_1y < x_2^Ly + x_1y^R - x_2^Ly^R.
$$

Then use (ii) (induction) on the simpler factor $y^R$ to get $x_1y^R = x_2y^R$, giving:

$$
x_1y < x_2^Ly + x_2y^R - x_2^Ly^R = R.
$$

Thus $x_1y\le x_2y$. Finally, swap the roles of $x_1$ and $x_2$. Hence $x_1y=x_2y$.

That proves **(ii)**.


**Conclusion:** when proving (i),(ii) for $xy$ at stage $\alpha$, you only ever use (iii) for strictly smaller product-ranks, i.e. already-proved $B(\beta)$ with $\beta<\alpha$.
So there is no need to assume $B(\alpha)$ while proving $A(\alpha)$.


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

So to finish the base case, he uses: “left options of $xy$ are $< xy$”, i.e. **(i) for $xy$**.

But notice: here $xy$ has $\rho(x,y) < \alpha$, so **(i) for $xy$ is part of $A(\alpha)$**, and we have already proved $A(\alpha)$ *before* starting $B(\alpha)$.

So inside stage $\alpha$, the dependency is:

- first establish all product facts $A(\alpha)$,
- then use them to discharge the base cases in $B(\alpha)$.

(Within $B(\alpha)$ there is also an *inner* induction on “simplicity of the quadruple” when Conway replaces $x_1$ by $x_1^R$, etc.; that inner induction stays inside the same $\alpha$ and is well-founded because options have smaller birthdays.)

---

