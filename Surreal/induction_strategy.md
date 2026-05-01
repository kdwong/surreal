
---

# Corrected 3-variable $C$-dependency list

Recall the statements: If $x, x_1, x_2, y, y_1, y_2$ are surreal numbers

$$A(x,y): xy \text{ surreal}.$$

$$B(x_1,x_2,y): \quad x_1 = x_2 \Longrightarrow x_1y = x_2y.$$

$$
C(x_1,x_2,y):
\quad
x_1<x_2
\Longrightarrow
\begin{cases}
x_1y+x_2y^L<x_1y^L+x_2y,\\
x_1y^R+x_2y<x_1y+x_2y^R.
\end{cases}
$$

And the original Conway's $C_4$ statement is

$$
C_4(x_1,x_2,y_1,y_2):
\quad
x_1<x_2
\Longrightarrow
x_1y_2+x_2y_1<x_1y_1+x_2y_2
$$

We will only use the $A$, $B$ and $C$ statements and use the Dershowitz–Manna ordering for well-founded induction. Here are the dependency in the proof of these statements, which relies on two important facts needed for the Dershowitz–Manna order $\prec$ on multiset of $\mathbb{N}$:

$\bullet$ If $a' < a$, then $\{a', b\} \prec \{a,b\}$.

$\bullet$ If $a' < a$, then $\{a', b, c\} \prec \{a,b, c\}$.

$\bullet$ If $a_1, a_2 < a$, then $\{a_1, a_2,b\} \prec \{a,b\}$.

$\bullet$ $\{a,b\} \prec \{a,b,c\}$.

---

# 1. Dependencies for $A(x,y)$

## 1a. Smaller $A$-instances

Unchanged:

$$
A(x^L,y),\quad A(x^R,y),\quad A(x,y^L),\quad A(x,y^R),
$$

and

$$
A(x^L,y^L),\quad A(x^L,y^R),\quad A(x^R,y^L),\quad A(x^R,y^R).
$$

---

## 1b. Left/right comparison branches

## Family F1: $(x_{L1},y^L)$ versus $(x_{L2},y^R)$

### If $x_{L1}\sim x_{L2}$

Original file had:

$$
B(x_{L1},x_{L2},y),\quad
B(x_{L1},x_{L2},y^R),\quad
C_4(x_{L1},x;y^L,y^R).
$$

Corrected:

$$
B(x_{L1},x_{L2},y),\quad
B(x_{L1},x_{L2},y^R),\quad
C(y^L,y^R,y).
$$

---

### If $x_{L1}<x_{L2}$

Original file had:

$$
C_4(x_{L1},x_{L2};y^L,y),\quad
C_4(x_{L2},x;y^L,y^R).
$$

Corrected:

$$
C(x_{L1},x_{L2},y),\quad
C(y^L,y^R,x).
$$

---

### If $x_{L1}>x_{L2}$

Original file had:

$$
C_4(x_{L1},x;y^L,y^R),\quad
C_4(x_{L2},x_{L1};y,y^R).
$$

Corrected:

$$
C(y^L, y^R, x),\quad
C(x_{L2},x_{L1},y).
$$

---

## Family F2: $(x^L,y_{L1})$ versus $(x^R,y_{L2})$

Here $y_{L1},y_{L2}$ are both left options of $y$. So whenever the first pair is $x^L,x$, $x,x^R$, or $x^L,x^R$ and the second pair is $y_{L1},y_{L2}$, we use symmetry and replace by $C(y_{L1},y_{L2},x)$.

### If $y_{L1}\sim y_{L2}$

Original file had:

$$
B(y_{L1},y_{L2},x),\quad
B(y_{L1},y_{L2},x^R),\quad
C_4(x^L,x^R;y_{L1},y).
$$


Corrected:

$$
B(y_{L1},y_{L2},x),\quad
B(y_{L1},y_{L2},x^R),\quad
C(x^L,x^R,y).
$$

---

### If $y_{L1}<y_{L2}$

Original file had:

$$
C_4(x^L,x;y_{L1},y_{L2}),\quad
C_4(x^L,x^R;y_{L2},y).
$$

The first term is switched by symmetry; the second term contains $y$, so it is kept in place.

Corrected:

$$
C(y_{L1},y_{L2},x),\quad
C(x^L,x^R,y).
$$

---

### If $y_{L1}>y_{L2}$

Original file had:

$$
C_4(x^L,x^R;y_{L1},y),\quad
C_4(x,x^R;y_{L2},y_{L1}).
$$

The first term contains $y$, so it stays in the $x$-position. The second term has both $y_{L2},y_{L1}$ as options of $y$, so it is switched by symmetry.

Corrected:

$$
C(x^L,x^R,y),\quad
C(y_{L2},y_{L1},x).
$$

---

## Family F3: $(x^R,y_{R1})$ versus $(x^L,y_{R2})$

Now $y_{R1},y_{R2}$ are right options of $y$.

### If $y_{R1}\sim y_{R2}$

Original file had:

$$
B(y_{R1},y_{R2},x),\quad
B(y_{R1},y_{R2},x^L),\quad
C_4(x^L,x^R;y,y_{R1}).
$$

Since the second pair contains $y$, keep the first pair.

Corrected:

$$
B(y_{R1},y_{R2},x),\quad
B(y_{R1},y_{R2},x^L),\quad
C(x^L,x^R,y).
$$

---

### If $y_{R1}<y_{R2}$

Original file had:

$$
C_4(x^L,x^R;y,y_{R1}),\quad
C_4(x^L,x;y_{R1},y_{R2}).
$$

Corrected:

$$
C(x^L,x^R,y),\quad
C(y_{R1},y_{R2},x).
$$

---

### If $y_{R1}>y_{R2}$

Original file had:

$$
C_4(x,x^R;y_{R2},y_{R1}),\quad
C_4(x^L,x^R;y,y_{R2}).
$$

Corrected:

$$
C(y_{R2},y_{R1},x),\quad
C(x^L,x^R,y).
$$

---

## Family F4: $(x_{R1},y^R)$ versus $(x_{R2},y^L)$

### If $x_{R1}\sim x_{R2}$

Original file had:

$$
B(x_{R1},x_{R2},y),\quad
B(x_{R1},x_{R2},y^L),\quad
C_4(x,x_{R1};y^L,y^R).
$$

Corrected:

$$
B(x_{R1},x_{R2},y),\quad
B(x_{R1},x_{R2},y^L),\quad
C(y^L,y^R,x).
$$

---

### If $x_{R1}<x_{R2}$

Original file had:

$$
C_4(x_{R1},x_{R2};y,y^R),\quad
C_4(x,x_{R2};y^L,y^R).
$$

Corrected:

$$
C(x_{R1},x_{R2},y),\quad
C(y^L,y^R,x).
$$

---

### If $x_{R1}>x_{R2}$

Original file had:

$$
C_4(x,x_{R1};y^L,y^R),\quad
C_4(x_{R2},x_{R1};y^L,y).
$$

Corrected:

$$
C(y^L,y^R,x),\quad
C(x_{R2},x_{R1},y).
$$

---

# 2. Dependencies for $B(x_1,x_2,y)$

The ambient numberhood calls are unchanged:

$$
A(x_1,y),\qquad A(x_2,y).
$$

## Branches from options of $x_1y$

### $x_1$-LL branch

Original:

$$
B(x_1,x_2,y^L),\quad C_4(x_1^L,x_2;y^L,y).
$$

Corrected:

$$
B(x_1,x_2,y^L),\quad C(x_1^L,x_2,y).
$$

---

### $x_1$-RR branch

Original:

$$
B(x_1,x_2,y^R),\quad C_4(x_2,x_1^R;y,y^R).
$$

Corrected:

$$
B(x_1,x_2,y^R),\quad C(x_2,x_1^R,y).
$$

---

### $x_1$-LR branch

Original:

$$
B(x_1,x_2,y^R),\quad C_4(x_1^L,x_2;y,y^R).
$$

Corrected:

$$
B(x_1,x_2,y^R),\quad C(x_1^L,x_2,y).
$$

---

### $x_1$-RL branch

Original:

$$
B(x_1,x_2,y^L),\quad C_4(x_2,x_1^R;y^L,y).
$$

Corrected:

$$
B(x_1,x_2,y^L),\quad C(x_2,x_1^R,y).
$$

---

## Symmetric branches from options of $x_2y$

### $x_2$-LL branch

Original:

$$
B(x_2,x_1,y^L),\quad C_4(x_2^L,x_1;y^L,y).
$$

Corrected:

$$
B(x_2,x_1,y^L),\quad C(x_2^L,x_1,y).
$$

---

### $x_2$-RR branch

Original:

$$
B(x_2,x_1,y^R),\quad C_4(x_1,x_2^R;y,y^R).
$$

Corrected:

$$
B(x_2,x_1,y^R),\quad C(x_1,x_2^R,y).
$$

---

### $x_2$-LR branch

Original:

$$
B(x_2,x_1,y^R),\quad C_4(x_2^L,x_1;y,y^R).
$$

Corrected:

$$
B(x_2,x_1,y^R),\quad C(x_2^L,x_1,y).
$$

---

### $x_2$-RL branch

Original:

$$
B(x_2,x_1,y^L),\quad C_4(x_1,x_2^R;y^L,y).
$$

Corrected:

$$
B(x_2,x_1,y^L),\quad C(x_1,x_2^R,y).
$$

---

# 3. Corrected dependencies for the old $C(x_1,x_2,y)$

The old $C(x_1,x_2,y)$ has two halves:

$$
x_1y+x_2y^L<x_1y^L+x_2y,
$$

and

$$
x_1y^R+x_2y<x_1y+x_2y^R.
$$

To prove these, one bridges between $x_1$ and $x_2$.

Assume $x_1<x_2$. Then either there is a right option $x_1^R$ with

$$
x_1<x_1^R\le x_2,
$$

or there is a left option $x_2^L$ with

$$
x_1\le x_2^L<x_2.
$$

---

## Bridge through $x_1^R\le x_2$

### If $x_1^R\sim x_2$

Use the equality replacements

$$
B(x_1^R,x_2,y^L),\quad B(x_1^R,x_2,y),\quad B(x_1^R,x_2,y^R),
$$

together with the adjacent $C$-step

$$
C(x_1,x_1^R,y).
$$

So the dependency list is:

$$
B(x_1^R,x_2,y^L),\quad
B(x_1^R,x_2,y),\quad
B(x_1^R,x_2,y^R),\quad
C(x_1,x_1^R,y)\rightsquigarrow A(x_1,y).
$$

---

### If $x_1^R<x_2$

Use the two old $C$-instances

$$
C(x_1,x_1^R,y),\quad C(x_1^R,x_2,y).
$$

So the dependency list is:

$$
C(x_1,x_1^R,y) \rightsquigarrow A(x_1,y),\quad C(x_1^R,x_2,y).
$$

---

## Bridge through $x_1\le x_2^L$

### If $x_1\sim x_2^L$

Use

$$
B(x_1,x_2^L,y^L),\quad B(x_1,x_2^L,y),\quad B(x_1,x_2^L,y^R),
$$

together with

$$
C(x_2^L,x_2,y).
$$

So the dependency list is:

$$
B(x_1,x_2^L,y^L),\quad
B(x_1,x_2^L,y),\quad
B(x_1,x_2^L,y^R),\quad
C(x_2^L,x_2,y) \rightsquigarrow A(x_2,y).
$$

---

### If $x_1<x_2^L$

Use

$$
C(x_1,x_2^L,y),\quad C(x_2^L,x_2,y).
$$

So the dependency list is:

$$
C(x_1,x_2^L,y),\quad C(x_2^L,x_2,y) \leftrightarrow A(x_2,y).
$$

---
Note that in the proof of $C$ case, the ``adjacent C
`` cases ($C(x_1^L, x_1, y)$, $C(x_2, x_2^R, y)$ ) follows from $A(x_1, y)$, since the two inequalities of $C$ are just coming from the fact that $x_1y$ is a surreal number. 