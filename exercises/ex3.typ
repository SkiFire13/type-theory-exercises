#import "/common.typ": *

= Chapter 3.6 Exercise 11
#v(1em)
It can be shown that there exists a proof-term #pf of the type \
#align(center, $pf in Id(A, x, z) [x in A, y in A, z in A, w_1 in Id(A, x, y), w_2 in Id(A, y, z)]$)
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

- $Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), c in Id(A, x, z_1) cont$ derivable:

#align(center, box(prooftree(
  A_type,
  axiom($Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2) cont$),
  rule(n: 2, label: "ind-ty", $A type hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2)]$),
  axiom($Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2) cont$),
  rule(label: "var", $x in A hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2)]$),
  axiom($Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2) cont$),
  rule(label: "var", $z_1 in A hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2)]$),
  rule(n: 3, label: "F-Id", $Id(A, x, z_1) type hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2)]$),
  rule(label: "F-C", $Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), c in Id(A, x, z_1) cont$),
)))

- $Id(A, x, z_2) type hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), c in Id(A, x, z_1)]$ derivable:

#align(center, box(prooftree(
  hspacing: 0.5em,
  A_type,
  axiom($Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), c in Id(A, x, z_1) cont$),
  rule(n: 2, label: "ind-ty", $A type hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), c in Id(A, x, z_1)]$),
  axiom($Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), c in Id(A, x, z_1)] cont$),
  rule(label: "var", $x in A hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), c in Id(A, x, z_1)]$),
  axiom($Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), c in Id(A, x, z_1)] cont$),
  rule(label: "var", $z_2 in A hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), c in Id(A, x, z_1)]$),
  rule(n: 3, label: "F-Id", $Id(A, x, z_2) type hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), c in Id(A, x, z_1)]$),
)))

- $Gamma, a in A cont$ derivable:

#align(center, box(prooftree(
  A_type,
  axiom($Gamma cont$),
  rule(n: 2, label: "ind-ty", $A type hctx [Gamma]$),
  rule(label: "F-C", $Gamma, a in A cont$),
)))

- $Gamma, a in A, c in Id(A, x, a) cont$ derivable:

#align(center, box(prooftree(
  A_type,
  axiom($Gamma, a in A cont$),
  rule(n: 2, label: "ind-ty", $A type hctx [Gamma, a in A]$),

  axiom($Gamma, a in A cont$),
  rule(label: "var", $x in A hctx [Gamma, a in A]$),

  axiom($Gamma, a in A cont$),
  rule(label: "var", $a in A hctx [Gamma, a in A]$),

  rule(n: 3, label: "F-Id", $Id(A, x, a) type hctx [Gamma, a in A]$),
  rule(label: "F-C", $Gamma, a in A, c in Id(A, x, a) cont$),
)))

- $El_Id(w_2, (x). (lambda c. c)) in Pi_(c in Id(A, x, y)) Id(A, x, z) hctx [Gamma]$ derivable:

#align(center, box(prooftree(
    axiom($Id(A, x, z_2) type hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), c in Id(A, x, z_1)]$),
    rule(label: "F-"+PI, $Pi_(c in Id(A, x, z_1)) Id(A, x, z_2) type hctx [Gamma, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2)]$),
    
    axiom($Gamma cont$),
    rule(label: "var", $y in A hctx [Gamma]$),
    
    axiom($Gamma cont$),
    rule(label: "var", $z in A hctx [Gamma]$),
    
    axiom($Gamma cont$),
    rule(label: "var", $w_2 in Id(A, y, z) hctx [Gamma]$),

    axiom($Gamma, a in A, c in Id(A, x, a) cont$),
    rule(label: "var", $c in Id(A, x, a) hctx [Gamma, a in A, c in Id(A, x, a)]$),
    rule(label: "I-"+PI, $lambda c. c in Pi_(c in Id(A, x, a)) Id(A, x, a) hctx [Gamma, a in A]$),

  rule(n: 5, label: "El-Id", $El_Id(w_2, (x). (lambda c. c)) in Pi_(c in Id(A, x, y)) Id(A, x, z) hctx [Gamma]$),
)))

Finally, we can derive an element of type $Id(A, x, z)$ in $Gamma$:
  
#align(center, box(prooftree(
    axiom($Gamma cont$),
    rule(label: "var", $w_1 in Id(A, x, y) hctx [Gamma$),

    axiom($El_Id(w_2, (x). (lambda c. c)) in Pi_(c in Id(A, x, y)) Id(A, x, z) hctx [Gamma]$),

  rule(n: 2, label: "E-"+PI, $Ap(El_Id(w_2, (x). (lambda c. c)), w_1) in Id(A, x, z) hctx [Gamma]$),
)))
