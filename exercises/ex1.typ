#import "/common.typ": *

#let h2 = $bold(upright(h_2))$

= Chapter 3.6 Exercise 3
#v(1em)
Prove that there exists a proof-term $h2$ for \
#align(center, $h_2(z_1, z_2, z_3) in Id(Nat, succ(z_1), succ(z_2)) hctx [z_1 in Nat, z_2 in Nat, z_3 in Id(Nat, z_1, z_2)]$)

*Solution.* \

We first prove that a couple of helper judgements are derivable:

- $z_1 in Nat, z_2 in Nat, z_3 in Id(Nat, z_1, z_2) cont$ derivable:

#let z1z2_cont_tree = (
  axiom($[#h(3pt)] cont$),
  rule(label: "F-Nat", $Nat type hctx [#h(3pt)]$),
  rule(label: "F-C", $z_1 in Nat cont$),
  rule(label: "F-Nat", $Nat type hctx [z_1 in Nat]$),
  rule(label: "F-C", $z_1 in Nat, z_2 in Nat cont$),
)

#align(center, box(prooftree(
    ..z1z2_cont_tree,
    rule(label: "F-Nat", $Nat type hctx [z_1 in Nat, z_2 in Nat]$),

    ..z1z2_cont_tree,
    rule(label: "var", $z_1 in Nat hctx [z_1 in Nat, z_2 in Nat]$),

    ..z1z2_cont_tree,
    rule(label: "var", $z_2 in Nat hctx [z_1 in Nat, z_2 in Nat]$),

  rule(n: 3, label: "F-Id", $Id(Nat, z_1, z_2) type hctx [z_1 in Nat, z_2 in Nat]$),
  rule(label: "F-C", $z_1 in Nat, z_2 in Nat, z_3 in Id(Nat, z_1, z_2) cont$),
)))

Let $Gamma = z_1 in Nat, z_2 in Nat, z_3 in Id(Nat, z_1, z_2)$ for brevity.

- $Gamma, w_1 in Nat, w_2 in Nat, w_3 in Id(Nat, w_1, w_2) cont$ derivable:

#let gw1w2_cont_tree = (
  axiom($Gamma cont$),
  rule(label: "F-Nat", $Nat type hctx [Gamma]$),
  rule(label: "F-C", $Gamma, w_1 in Nat cont$),
  rule(label: "F-Nat", $Nat type hctx [Gamma, w_1 in Nat]$),
  rule(label: "F-C", $Gamma, w_1 in Nat, w_2 in Nat cont$),
)

#align(center, box(prooftree(
    ..gw1w2_cont_tree,
    rule(label: "F-Nat", $Nat type hctx [Gamma, w_1 in Nat, w_2 in Nat]$),

    ..gw1w2_cont_tree,
    rule(label: "var", $w_1 in Nat type hctx [Gamma, w_1 in Nat, w_2 in Nat]$),

    ..gw1w2_cont_tree,
    rule(label: "var", $w_2 in Nat type hctx [Gamma, w_1 in Nat, w_2 in Nat]$),

  rule(n: 3, label: "F-Id", $Id(Nat, w_1, w_2) type hctx [Gamma, w_1 in Nat, w_2 in Nat]$),
  rule(label: "F-C", $Gamma, w_1 in Nat, w_2 in Nat, w_3 in Id(Nat, w_1, w_2) cont$),
)))

- $Id(Nat, succ(w_1), succ(w_2)) type hctx [Gamma, w_1 in Nat, w_2 in Nat, w_3 in Id(Nat, w_1, w_2)]$ derivable:

#align(center, box(prooftree(
  hspacing: 0.5em,
    axiom($Gamma, w_1 in Nat, w_2 in Nat, w_3 in Id(Nat, w_1, w_2) cont$),
    rule(label: "F-Nat", $Nat type hctx [Gamma, w_1 in Nat, w_2 in Nat, w_3 in Id(Nat, w_1, w_2)]$),

    axiom($Gamma, w_1 in Nat, w_2 in Nat, w_3 in Id(Nat, w_1, w_2) cont$),
    rule(label: "var", $w_1 in Nat hctx [Gamma, w_1 in Nat, w_2 in Nat, w_3 in Id(Nat, w_1, w_2)]$),
    rule(label: $upright(I)_2"-"Nat$, $succ(w_1) in Nat hctx [Gamma, w_1 in Nat, w_2 in Nat, w_3 in Id(Nat, w_1, w_2)]$),

    axiom($Gamma, w_1 in Nat, w_2 in Nat, w_3 in Id(Nat, w_1, w_2) cont$),
    rule(label: "var", $w_2 in Nat hctx [Gamma, w_1 in Nat, w_2 in Nat, w_3 in Id(Nat, w_1, w_2)]$),
    rule(label: $upright(I)_2"-"Nat$, $succ(w_2) in Nat hctx [Gamma, w_1 in Nat, w_2 in Nat, w_3 in Id(Nat, w_1, w_2)]$),

  rule(n: 3, label: "F-Id", $Id(Nat, succ(w_1), succ(w_2)) type hctx [Gamma, w_1 in Nat, w_2 in Nat, w_3 in Id(Nat, w_1, w_2)]$),
)))

Finally, we can derive an element of type $Id(Nat, succ(z_1), succ(z_2))$ in $Gamma$:

#align(center, box(prooftree(
    axiom($Id(Nat, succ(w_1), succ(w_2)) type hctx [Gamma, w_1 in Nat, w_2 in Nat, w_3 in Id(Nat, w_1, w_2)]$),

    axiom($Gamma cont$),
    rule(label: "var", $z_1 in Nat hctx [Gamma]$),

    axiom($Gamma cont$),
    rule(label: "var", $z_2 in Nat hctx [Gamma]$),

    axiom($Gamma cont$),
    rule(label: "var", $z_3 in Id(Nat, z_1, z_2) hctx [Gamma]$),

    axiom($Gamma cont$),
    rule(label: "F-Nat", $Nat type hctx [Gamma]$),
    rule(label: "F-C", $Gamma, x in Nat cont$),
    rule(label: "var", $x in Nat hctx [Gamma, x in Nat]$),
    rule(label: "I-Id", $id(x) in Id(Nat, x, x) hctx [Gamma, x in Nat]$),

  rule(n: 5, label: "E-Id", $E_Id(z_3, (x). id(x)) in Id(Nat, succ(z_1), succ(z_2)) hctx [Gamma]$),
)))
