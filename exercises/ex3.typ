#import "/common.typ": *

= Chapter 3.6 Exercise 11
#v(1em)
It can be shown that there exists a proof-term #pf of the type \
#align(center, $pf in Id(A, x, z) hctx [x in A, y in A, z in A, w_1 in Id(A, x, y), w_2 in Id(A, y, z)]$)
for every $A type hctx [#h(3pt)]$ derivable?

*Solution.* \

#let A_type = axiom($A type hctx [#h(3pt)]$)

We first prove that a couple of helper judgements are derivable, assuming $A type hctx [#h(3pt)]$ derivable:

- $x in A, y in A, z in A cont$ derivable

#align(center, box(prooftree(
  A_type,
  A_type,
  A_type,
  rule(label: "F-C", $x in A cont$),
  rule(n: 2, label: "ind-ty", $A type hctx [x in A]$),
  rule(label: "F-C", $x in A, y in A cont$),
  rule(n: 2, label: "ind-ty", $A type hctx [x in A, y in A]$),
  rule(label: "F-C", $x in A, y in A, z in A cont$),
)))

- $x in A, y in A, z in A, w_1 in Id(A, x, y) cont$ derivable

#align(center, box(prooftree(
  A_type,
  axiom($x in A, y in A, z in A cont$),
  rule(n: 2, label: "ind-ty", $A type hctx [x in A, y in A, z in A]$),

  axiom($x in A, y in A, z in A cont$),
  rule(label: "var", $x in A hctx [x in A, y in A, z in A]$),
  
  axiom($x in A, y in A, z in A cont$),
  rule(label: "var", $y in A hctx [x in A, y in A, z in A]$),

  rule(n: 3, label: "F-Id", $Id(A, x, y) type hctx [x in A, y in A, z in A]$),
  rule(label: "F-C", $x in A, y in A, z in A, w_1 in Id(A, x, y) cont$),
)))

- $x in A, y in A, z in A, w_1 in Id(A, x, y), w_2 in Id(A, y, z) cont$ derivable
  
#align(center, box(prooftree(
  A_type,
  axiom($x in A, y in A, z in A, w_1 in Id(A, x, y) cont$),
  rule(n: 2, label: "ind-ty", $A type hctx [x in A, y in A, z in A, w_1 in Id(A, x, y)]$),

  axiom($x in A, y in A, z in A, w_1 in Id(A, x, y) cont$),
  rule(label: "var", $y in A hctx [x in A, y in A, z in A, w_1 in Id(A, x, y)]$),
  
  axiom($x in A, y in A, z in A, w_1 in Id(A, x, y) cont$),
  rule(label: "var", $z in A hctx [x in A, y in A, z in A, w_1 in Id(A, x, y)]$),

  rule(n: 3, label: "F-Id", $Id(A, y, z) type hctx [x in A, y in A, z in A, w_1 in Id(A, x, y)]$),
  rule(label: "F-C", $x in A, y in A, z in A, w_1 in Id(A, x, y), w_2 in Id(A, y, z) cont$),
)))

Let $Gamma = x in A, y in A, z in A, w_1 in Id(A, x, y), w_2 in Id(A, y, z)$ for brevity. \

- $Gamma, z_1 in A, z_2 in A cont$ derivable:

#align(center, box(prooftree(
  A_type,
  A_type,
  axiom($Gamma cont$),
  rule(n: 2, label: "ind-ty", $A type hctx [Gamma]$),
  rule(label: "F-C", $Gamma, z_1 in A cont$),
  rule(n: 2, label: "ind-ty", $A type hctx [Gamma, z_1 in A]$),
  rule(label: "F-C", $Gamma, z_1 in A, z_2 in A$),
)))


- $Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2) cont$ derivable:

#align(center, box(prooftree(
  A_type,
  axiom($Gamma, z_1 in A, z_2 in A cont$),
  rule(n: 2, label: "ind-ty", $A type hctx [Gamma, z_1 in A, z_2 in A]$),
  axiom($Gamma, z_1 in A, z_2 in A cont$),
  rule(label: "var", $z_1 in A hctx [Gamma, z_1 in A, z_2 in A]$),
  axiom($Gamma, z_1 in A, z_2 in A cont$),
  rule(label: "var", $z_2 in A hctx [Gamma, z_1 in A, z_2 in A]$),
  rule(n: 3, label: "F-Id", $Id(A, z_1, z_2) type hctx [Gamma, z_1 in A, z_2 in A]$),
  rule(label: "F-C", $Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2) cont$)
)))

- $Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), x_2 in Id(A, x, z_1) cont$ derivable:

#align(center, box(prooftree(
  A_type,
  axiom($Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2) cont$),
  rule(n: 2, label: "ind-ty", $A type hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2)]$),
  axiom($Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2) cont$),
  rule(label: "var", $x in A hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2)]$),
  axiom($Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2) cont$),
  rule(label: "var", $z_1 in A hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2)]$),
  rule(n: 3, label: "F-Id", $Id(A, x, z_1) type hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2)]$),
  rule(label: "F-C", $Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), x_2 in Id(A, x, z_1) cont$),
)))

- $Id(A, x, z_2) type hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), x_2 in Id(A, x, z_1)]$ derivable:

#align(center, box(prooftree(
  hspacing: 0.5em,
  A_type,
  axiom($Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), x_2 in Id(A, x, z_1) cont$),
  rule(n: 2, label: "ind-ty", $A type hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), x_2 in Id(A, x, z_1)]$),
  axiom($Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), x_2 in Id(A, x, z_1)] cont$),
  rule(label: "var", $x in A hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), x_2 in Id(A, x, z_1)]$),
  axiom($Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), x_2 in Id(A, x, z_1)] cont$),
  rule(label: "var", $z_2 in A hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), x_2 in Id(A, x, z_1)]$),
  rule(n: 3, label: "F-Id", $Id(A, x, z_2) type hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), x_2 in Id(A, x, z_1)]$),
)))

- $Gamma, x_1 in A, x_2 in Id(A, x, x_1) cont$ derivable:

#let ga_cont_tree = (
  A_type,
  axiom($Gamma cont$),
  rule(n: 2, label: "ind-ty", $A type hctx [Gamma]$),
  rule(label: "F-C", $Gamma, x_1 in A cont$),
)

#align(center, box(prooftree(
  A_type,
  ..ga_cont_tree,
  rule(n: 2, label: "ind-ty", $A type hctx [Gamma, x_1 in A]$),

  ..ga_cont_tree,
  rule(label: "var", $x in A hctx [Gamma, x_1 in A]$),

  ..ga_cont_tree,
  rule(label: "var", $x_1 in A hctx [Gamma, x_1 in A]$),

  rule(n: 3, label: "F-Id", $Id(A, x, x_1) type hctx [Gamma, x_1 in A]$),
  rule(label: "F-C", $Gamma, x_1 in A, x_2 in Id(A, x, x_1) cont$),
)))

- $El_Id (w_2, (x). (lambda x_2. x_2)) in Pi_(x_2 in Id(A, x, y)) Id(A, x, z) hctx [Gamma]$ derivable:

#align(center, box(prooftree(
    axiom($Id(A, x, z_2) type hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), x_2 in Id(A, x, z_1)]$),
    rule(label: "F-"+PI, $Pi_(x_2 in Id(A, x, z_1)) Id(A, x, z_2) type hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2)]$),
    
    axiom($Gamma cont$),
    rule(label: "var", $y in A hctx [Gamma]$),
    
    axiom($Gamma cont$),
    rule(label: "var", $z in A hctx [Gamma]$),
    
    axiom($Gamma cont$),
    rule(label: "var", $w_2 in Id(A, y, z) hctx [Gamma]$),

    axiom($Gamma, x_1 in A, x_2 in Id(A, x, x_1) cont$),
    rule(label: "var", $x_2 in Id(A, x, x_1) hctx [Gamma, x_1 in A, x_2 in Id(A, x, x_1)]$),
    rule(label: "I-"+PI, $lambda x_2. x_2 in Pi_(x_2 in Id(A, x, x_1)) Id(A, x, x_1) hctx [Gamma, x_1 in A]$),

  rule(n: 5, label: "El-Id", $El_Id (w_2, (x). (lambda x_2. x_2)) in Pi_(x_2 in Id(A, x, y)) Id(A, x, z) hctx [Gamma]$),
)))

Finally, we can derive an element of type $Id(A, x, z)$ in $Gamma$:
  
#align(center, box(prooftree(
    axiom($Gamma cont$),
    rule(label: "var", $w_1 in Id(A, x, y) hctx [Gamma]$),

    axiom($El_Id (w_2, (x). (lambda x_2. x_2)) in Pi_(x_2 in Id(A, x, y)) Id(A, x, z) hctx [Gamma]$),

  rule(n: 2, label: "E-"+PI, $Ap(El_Id (w_2, (x). (lambda x_2. x_2)), w_1) in Id(A, x, z) hctx [Gamma]$),
)))
