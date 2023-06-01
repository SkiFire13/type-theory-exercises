#import "/common.typ": *

= Chapter 3.6 Exercise 10
#v(1em)
It can be shown that there exists a proof-term #pf of the type \
#align(center, $pf in P (y) hctx [x in A, y in A, z in P(x), w in Id(A, x, y)]$)
for every $P(y) type hctx [y in A]$ derivable?

*Solution.* \

#let A_type = axiom($A type hctx [#h(3pt)]$)

We first prove that a couple of helper judgements are derivable, assuming $A type hctx [#h(3pt)]$ and $P(y) type hctx [y in A]$ derivable:

- $x in A, y in A, z in P(x) cont$ derivable:

#align(center, box(prooftree(
  axiom($P(x) type hctx [x in A]$),
  A_type,
  A_type,
  rule(label: "F-C", $x in A cont$),
  rule(n: 2, label: "ind-ty", $A type hctx [x in A]$),
  rule(label: "F-C", $x in A, y in A cont$),
  rule(n: 2, label: "ind-ty", $P(x) type hctx [x in A, y in A]$),
  rule(label: "F-C", $x in A, y in A, z in P(x) cont$),
)))

- $x in A, y in A, z in P(x), w in Id(A, x, y) cont$ derivable:
#align(center, box(prooftree(
  A_type,
  axiom($x in A, y in A, z in P(x) cont$),
  rule(n: 2, label: "ind-ty", $A type hctx [x in A, y in A, z in P(x)]$),
  axiom($x in A, y in A, z in P(x) cont$),
  rule(label: "var", $x in A hctx [x in A, y in A, z in P(x)]$),
  axiom($x in A, y in A, z in P(x) cont$),
  rule(label: "var", $y in A hctx [x in A, y in A, z in P(x)]$),
  rule(n: 3, label: "F-Id", $Id(A, x, y) type hctx [x in A, y in A, z in P(x)]$),
  rule(label: "F-C", $x in A, y in A, z in P(x), w in Id(A, x, y) cont$),
)))

Let $Gamma = x in A, y in A, z in P(x), w in Id(A, x, y)$ for brevity. \

- $Gamma, z_1 in A, z_2 in A cont$ derivable:

#align(center, box(prooftree(
  A_type,
    A_type,
    axiom($Gamma cont$),
    rule(n: 2, label: "ind-ty", $A type hctx [Gamma]$),
    rule(label: "F-C", $Gamma, z_1 in A cont$),
  rule(n: 2, label: "ind-ty", $A type hctx [Gamma, z_1 in A]$),
  rule(label: "F-C", $Gamma, z_1 in A, z_2 in A cont$),
)))

- $Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2) cont$ derivable:

#align(center, box(prooftree(
      A_type,
      axiom($Gamma, z_1 in A, z_2 in A cont$),
    rule(n:2, label: "ind-ty", $A type hctx [Gamma, z_1 in A, z_2 in A]$),

    axiom($Gamma, z_1 in A, z_2 in A cont$),
    rule(label: "var", $z_1 in A hctx [Gamma, z_1 in A, z_2 in A]$),
    
    axiom($Gamma, z_1 in A, z_2 in A cont$),
    rule(label: "var", $z_2 in A hctx [Gamma, z_1 in A, z_2 in A]$),
  rule(n: 3, label: "F-Id", $Id(A, z_1, z_2) type hctx [Gamma, z_1 in A, z_2 in A]$),
  rule(label: "F-C", $Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2) cont$),
)))

- $P(z_2) type hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), x_2 in P(z_1)]$ derivable:

#align(center, box(prooftree(
  axiom($P(z_2) type hctx [z_2 in A]$),
  axiom($P(z_1) type hctx [z_1 in A]$),
  axiom($Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2) cont$),
  rule(n: 2, label: "ind-ty", $P(z_1) type hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2)]$),
  rule(label: "F-C", $Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), x_2 in P(z_1) cont$),
  rule(n: 2, label: "ind-ty", $P(z_2) type hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), x_2 in P(z_1)]$),
)))

- $Gamma, x_1 in A, x_2 in P(x_1) cont$ derivable:

#align(center, box(prooftree(
  axiom($P(x_1) type hctx [x_1 in A]$),
  A_type,
  axiom($Gamma cont$),
  rule(n: 2, label: "ind-ty", $A type hctx [Gamma]$),
  rule(label: "F-C", $Gamma, x_1 in A cont$),
  rule(n: 2, label: "ind-ty", $P(x_1) type hctx [Gamma, x_1 in A]$),
  rule(label: "F-C", $Gamma, x_1 in A, x_2 in P(x_1) cont$),
)))

Finally, we can derive an element of type $P(y)$ in $Gamma$:

#align(center, box(prooftree(
  axiom($Gamma cont$),
  rule(label: "var", $z in P(x) hctx [Gamma]$),

    axiom($P(z_2) type hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), x_2 in P(z_1)]$),
    rule(label: "F-"+PI, $Pi_(x_2 in P(z_1)) P(z_2) type hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2)]$),
    
    axiom($Gamma cont$),
    rule(label: "var", $x in A hctx [Gamma]$),
    
    axiom($Gamma cont$),
    rule(label: "var", $y in A hctx [Gamma]$),
    
    axiom($Gamma cont$),
    rule(label: "var", $w in Id(A, x, y) hctx [Gamma]$),

    axiom($Gamma, x_1 in A, x_2 in P(x_1)$),
    rule(label: "var", $x_2 in P(x_1) hctx [Gamma, x_1 in A, x_2 in P(x_1)]$),
    rule(label: "I-"+PI, $lambda x_2. x_2 in Pi_(x_2 in P(x_1)) P(x_1) hctx [Gamma, x_1 in A]$),
  rule(n: 5, label: "E-Id", $El_Id(w, (x). (lambda x_2. x_2)) in Pi_(x_2 in P(x)) P(y) hctx [Gamma]$),

rule(n: 2, label: "E-"+PI, $Ap(El_Id(w, (x). (lambda x_2. x_2)), z) in P(y) hctx [Gamma]$),
)))