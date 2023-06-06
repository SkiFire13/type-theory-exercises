#import "template.typ": template
#import "/common.typ": *

#set page(paper: "a2")

#show: template(
  title: "Type Theory Exercises for the Exam",
  author: "Stevanato Giacomo",
  date: "2nd Semester 2022/23",
)

= Chapter 5 Exercise 12
#v(1em)
Given the types $B type hctx [Gamma]$ and $C type hctx [Gamma]$ deduce from the previous exercise a term
#align(center, $
  pf_1 in Id(B, x, x') hctx [x in B, x' in B, z in Id(B + C, inl(x), inl(x'))]
$)

*Solution.* \

We first prove that a couple of helper judgements are derivable, assuming $B type hctx [#h(3pt)]$ and $C type hctx [#h(3pt)]$ derivable:

- $x in B, x' in B cont$ derivable:

#align(center, box(prooftree(
  axiom($B type hctx [#h(3pt)]$),
  axiom($B type hctx [#h(3pt)]$),
  rule(label: "F-C", $x in B cont$),
  rule(n: 2, label: "ind-ty", $B type hctx [x in B]$),
  rule(label: "F-C", $x in B, x' in B cont$),
)))

- $inl(x) in B + C hctx [x in B, x' in B]$ derivable:

#align(center, box(prooftree(
  axiom($x in B, x' in B cont$),
  rule(label: "var", $x in B hctx [x in B, x' in B]$),
  axiom($B type hctx [#h(3pt)]$),
  axiom($x in B, x' in B cont$),
  rule(n: 2, label: "ind-ty", $B type hctx [x in B, x' in B]$),
  axiom($C type hctx [#h(3pt)]$),
  axiom($x in B, x' in B cont$),
  rule(n: 2, label: "ind-ty", $C type hctx [x in B, x' in B]$),
  rule(n: 3, label: $upright("I")_1$ + "-+", $inl(x) in B + C hctx [x in B, x' in B]$),
)))

- $inl(x') in B + C hctx [x in B, x' in B]$ derivable:

#align(center, box(prooftree(
  axiom($x in B, x' in B cont$),
  rule(label: "var", $x' in B hctx [x in B, x' in B]$),
  axiom($B type hctx [#h(3pt)]$),
  axiom($x in B, x' in B cont$),
  rule(n: 2, label: "ind-ty", $B type hctx [x in B, x' in B]$),
  axiom($C type hctx [#h(3pt)]$),
  axiom($x in B, x' in B cont$),
  rule(n: 2, label: "ind-ty", $C type hctx [x in B, x' in B]$),
  rule(n: 3, label: $upright("I")_1$ + "-+", $inl(x') in B + C hctx [x in B, x' in B]$),
)))

- $x in B, x' in B, z in Id(B + C, inl(x), inl(x')) cont$: 

#align(center, box(prooftree(
  axiom($B type hctx [#h(3pt)]$),
  axiom($C type hctx [#h(3pt)]$),
  rule(n: 2, label: "F-+", $B + C type hctx [#h(3pt)]$),
  axiom($x in B, x' in B cont$),
  rule(n: 2, label: "ind-ty", $B + C type hctx [x in B, x' in B]$),
  axiom($inl(x) in B + C hctx [x in B, x' in B]$),
  axiom($inl(x') in B + C hctx [x in B, x' in B]$),
  rule(n: 3, label: "F-Id", $Id(B + C, inl(x), inl(x')) type hctx [x in B, x' in B]$),
  rule(label: "F-C", $x in B, x' in B, z in Id(B + C, inl(x), inl(x')) cont$),
)))

Let $Gamma = x in B, x' in B, z in Id(B + C, inl(x), inl(x'))$ for brevity.

- $Gamma, w_1 in B + C, w_2 in B + C cont$

#align(center, box(prooftree(
  axiom($B type hctx [#h(3pt)]$),

  axiom($B type hctx [#h(3pt)]$),
  axiom($Gamma cont$),
  rule(n: 2, label: "ind-ty", $B type hctx [Gamma]$),
  axiom($C type hctx [#h(3pt)]$),
  axiom($Gamma cont$),
  rule(n: 2, label: "ind-ty", $C type hctx [Gamma]$),
  rule(n: 2, label: "F-+", $B + C type hctx [Gamma]$),
  rule(label: "F-C", $Gamma, w_1 in B + C cont$),

  rule(n: 2, label: "ind-ty", $B type hctx [Gamma, w_1 in B + C]$),
  axiom($C type hctx [#h(3pt)]$),

  axiom($B type hctx [#h(3pt)]$),
  axiom($Gamma cont$),
  rule(n: 2, label: "ind-ty", $B type hctx [Gamma]$),
  axiom($C type hctx [#h(3pt)]$),
  axiom($Gamma cont$),
  rule(n: 2, label: "ind-ty", $C type hctx [Gamma]$),
  rule(n: 2, label: "F-+", $B + C type hctx [Gamma]$),
  rule(label: "F-C", $Gamma, w_1 in B + C cont$),

  rule(n: 2, label: "ind-ty", $C type hctx [Gamma, w_1 in B + C]$),
  rule(n: 2, label: "F-+", $B + C type hctx [Gamma, w_1 in B + C]$),
  rule(label: "F-C", $Gamma, w_1 in B + C, w_2 in B + C cont$),
)))

- $Gamma, w_1 in B + C, w_2 in B + C, w_3 in Id(B + C, w_1, w_2) cont$:

#align(center, box(prooftree(
  axiom($B type hctx [#h(3pt)]$),
  axiom($C type hctx [#h(3pt)]$),
  rule(n: 2, label: "F-+", $B + C type hctx [#h(3pt)]$),
  axiom($Gamma, w_1 in B + C, w_2 in B + C cont$),
  rule(n: 2, label: "ind-ty", $B + C type hctx [Gamma, w_1 in B + C, w_2 in B + C]$),
  axiom($Gamma, w_1 in B + C, w_2 in B + C cont$),
  rule(label: "var", $w_1 in B + C hctx [Gamma, w_1 in B + C, w_2 in B + C]$),
  axiom($Gamma, w_1 in B + C, w_2 in B + C cont$),
  rule(label: "var", $w_2 in B + C hctx [Gamma, w_1 in B + C, w_2 in B + C]$),
  rule(n: 3, label: "F-Id", $Id(B + C, w_1, w_2) type hctx [Gamma, w_1 in B + C, w_2 in B + C]$),
  rule(label: "F-C", $Gamma, w_1 in B + C, w_2 in B + C, w_3 in Id(B + C, w_1, w_2) cont$),
)))

Let $Sigma = Gamma, w_1 in B + C, w_2 in B + C, w_3 in Id(B + C, w_1, w_2)$ for brevity.

- $z_1 in B + C, z_2 in B cont$:

#align(center, box(prooftree(
  axiom($B type hctx [#h(3pt)]$),
  axiom($B type hctx [#h(3pt)]$),
  axiom($C type hctx [#h(3pt)]$),
  rule(n: 2, label: "F-+", $B + C type hctx [#h(3pt)]$),
  rule(label: "F-C", $z_1 in B + C cont$),
  rule(n: 2, label: "ind-ty", $B type hctx [z_1 in B + C]$),
  rule(label: "F-C", $z_1 in B + C, z_2 in B cont$)
)))

- $El_+(z_1, (x_1). x_1, (x_2). z_2) in B hctx [z_1 in B + C, z_2 in B]$ derivable:

#align(center, box(prooftree(
      axiom($B type hctx [#h(3pt)]$),
      axiom($z_1 in B + C, z_2 in B cont$),
    rule(n: 2, label: "ind-ty", $B type hctx [z_1 in B + C, z_2 in B]$),
      axiom($z_1 in B + C, z_2 in B cont$),
    rule(label: "var", $z_1 in B + C hctx [z_1 in B + C, z_2 in B]$),
      axiom($B type hctx [#h(3pt)]$),
      axiom($z_1 in B + C, z_2 in B cont$),
      rule(n: 2, label: "ind-ty", $B type hctx [z_1 in B + C, z_2 in B]$),
      rule(label: "F-C", $z_1 in B + C, z_2 in B, x_1 in B cont$),
    rule(label: "var", $x_1 in B hctx [z_1 in B + C, z_2 in B, x_1 in B]$),
      axiom($B type hctx [#h(3pt)]$),
      axiom($z_1 in B + C, z_2 in B cont$),
      rule(n: 2, label: "ind-ty", $B type hctx [z_1 in B + C, z_2 in B]$),
      rule(label: "F-C", $z_1 in B + C, z_2 in B, x_2 in B cont$),
    rule(label: "var", $z_2 in B hctx [z_1 in B + C, z_2 in B, x_2 in B]$),
  rule(n: 4, label: "E-+", $El_+(z_1, (x_1). x_1, (x_2). z_2) in B hctx [z_1 in B + C, z_2 in B]$)
)))

Let $c(z_1, z_2) = El_+(z_1, (x_1). x_1, (x_2). z_2)$ for brevity.

- $Id(B, c(w_1, x), c(w_2, x)) type hctx [Sigma]$ derivable:

#align(center, box(prooftree(
    axiom($B type hctx [#h(3pt)]$),
    axiom($Sigma cont$),
  rule(n: 2, label: "ind-ty", $B type hctx [Sigma]$),
    axiom($c(w_1, x) in B hctx [w_1 in B + C, x in B]$),
    axiom($Sigma cont$),
  rule(n: 2, label: "ind-te", $c(w_1, x) in B hctx [Sigma]$),
    axiom($c(w_2, x) in B hctx [w_2 in B + C, x in B]$),
    axiom($Sigma cont$),
  rule(n: 2, label: "ind-te", $c(w_2, x) in B hctx [Sigma]$),
  rule(n: 3, label: "F-Id", $Id(B, c(w_1, x), c(w_2, x)) type hctx [Sigma]$),
)))

- $inl(x) in B + C hctx [Gamma]$ derivable:

#align(center, box(prooftree(
  axiom($Gamma cont$),
  rule(label: "var", $x in B hctx [Gamma]$),
  axiom($B type hctx [#h(3pt)]$),
  axiom($Gamma cont$),
  rule(n: 2, label: "ind-ty", $B type hctx [Gamma]$),
  axiom($C type hctx [#h(3pt)]$),
  axiom($Gamma cont$),
  rule(n: 2, label: "ind-ty", $C type hctx [Gamma]$),
  rule(n: 3, label: $upright("I")_1$ + "-+", $inl(x) in B + C hctx [Gamma]$),
)))

- $inl(x') in B + C hctx [Gamma]$ derivable:

#align(center, box(prooftree(
  axiom($Gamma cont$),
  rule(label: "var", $x' in B hctx [Gamma]$),
  axiom($B type hctx [#h(3pt)]$),
  axiom($Gamma cont$),
  rule(n: 2, label: "ind-ty", $B type hctx [Gamma]$),
  axiom($C type hctx [#h(3pt)]$),
  axiom($Gamma cont$),
  rule(n: 2, label: "ind-ty", $C type hctx [Gamma]$),
  rule(n: 3, label: $upright("I")_1$ + "-+", $inl(x') in B + C hctx [Gamma]$),
)))

- $id(c(y, x)) in Id(B, c(y, x), c(y, x)) hctx [Gamma, y in B + C]$ derivable:

#align(center, box(prooftree(
  axiom($c(y, x) in B hctx [y in B + C, x in B]$),
  axiom($B type hctx [#h(3pt)]$),
  axiom($Gamma cont$),
  rule(n: 2, label: "ind-ty", $B type hctx [Gamma]$),
  axiom($C type hctx [#h(3pt)]$),
  axiom($Gamma cont$),
  rule(n: 2, label: "ind-ty", $C type hctx [Gamma]$),
  rule(n: 2, label: "F-+", $B + C type hctx [Gamma]$),
  rule(label: "F-C", $Gamma, y in B + C cont$),
  rule(n: 2, label: "ind-te", $c(y, x) in B hctx [Gamma, y in B + C]$),
  rule(label: "I-Id", $id(c(y, x)) in Id(B, c(y, x), c(y, x)) hctx [Gamma, y in B + C]$),
)))

- $El_Id(z, (y). id(c(y, x))) in Id(B, c(inl(x), x), c(inl(x'), x)) hctx [Gamma]$ derivable:

#align(center, box(prooftree(
  axiom($Id(B, c(w_1, x), c(w_2, x)) type hctx [Sigma]$),
  axiom($inl(x) in B + C hctx [Gamma]$),
  axiom($inl(x') in B + C hctx [Gamma]$),
  axiom($Gamma cont$),
  rule(label: "var", $z in Id(B + C, inl(x), inl(x')) hctx [Gamma]$),
  axiom($id(c(y, x)) in Id(B, c(y, x), c(y, x)) hctx [Gamma, y in B + C]$),
  rule(n: 5, label: "E-Id", $El_Id(z, (y). id(c(y, x))) in Id(B, c(inl(x), x), c(inl(x'), x)) hctx [Gamma]$),
)))

- $z_1 in B, z_2 in B cont$ derivable:

#align(center, box(prooftree(
  axiom($B type hctx [#h(3pt)]$),
  axiom($B type hctx [#h(3pt)]$),
  rule(label: "F-C", $z_1 in B cont$),
  rule(n: 2, label: "ind-ty", $B type hctx [z_1 in B]$),
  rule(label: "F-C", $z_1 in B, z_2 in B cont$),
)))

- $inl(z_1) in B hctx [z_1 in B, z_2 in B]$ derivable:

#align(center, box(prooftree(
  axiom($z_1 in B, z_2 in B cont$),
  rule(label: "var", $z_1 in B hctx [z_1 in B, z_2 in B]$),
  axiom($B type hctx [#h(3pt)]$),
  axiom($z_1 in B, z_2 in B cont$),
  rule(n: 2, label: "ind-ty", $B type hctx [z_1 in B, z_2 in B]$),
  axiom($C type hctx [#h(3pt)]$),
  axiom($z_1 in B, z_2 in B cont$),
  rule(n: 2, label: "ind-ty", $C type hctx [z_1 in B, z_2 in B]$),
  rule(n: 3, label: $upright("I")_1$ + "-+", $inl(z_1) in B + C hctx [z_1 in B, z_2 in B]$),
)))

- $c(inl(z_1), z_2) = z_1 in B hctx [z_1 in B, z_2 in B]$ derivable:

#align(center, box(prooftree(
    axiom($B type hctx [#h(3pt)]$),
    axiom($z_1 in B, z_2 in B cont$),
    rule(n: 2, label: "ind-ty", $B type hctx [z_1 in B, z_2 in B]$),
    axiom($inl(z_1) in B hctx [z_1 in B, z_2 in B]$),
    axiom($B type hctx [#h(3pt)]$),
    axiom($z_1 in B, z_2 in B cont$),
    rule(n: 2, label: "ind-ty", $B type hctx [z_1 in B, z_2 in B]$),
    rule(label: "F-C", $z_1 in B, z_2 in B, x_1 in B cont$),
    rule(label: "var", $x_1 in B hctx [z_1 in B, z_2 in B, x_1 in B]$),
    axiom($B type hctx [#h(3pt)]$),
    axiom($z_1 in B, z_2 in B cont$),
    rule(n: 2, label: "ind-ty", $B type hctx [z_1 in B, z_2 in B]$),
    rule(label: "F-C", $z_1 in B, z_2 in B, x_2 in B cont$),
    rule(label: "var", $z_2 in B hctx [z_1 in B, z_2 in B, x_2 in B]$),
  rule(n: 4, label: $upright("C")_1$ + "-+", $El_+(inl(z_1), (x_1). x_1, (x_2). z_2) = z_1 in B hctx [z_1 in B, z_2 in B]$),
)))

Finally, we can derive an element of type $Id(B, x, x')$ in $Gamma$:

#align(center, box(prooftree(
    axiom($El_Id(z, (y). id(c(y, x))) in Id(B, c(inl(x), x), c(inl(x'), x)) hctx [Gamma]$),
      axiom($B type hctx [Gamma]$),
      rule(label: "ref", $B = B type hctx [Gamma]$),
      axiom($c(inl(x), x) = x in B hctx [Gamma]$),
      axiom($c(inl(x'), x) = x' in B hctx [Gamma]$),
    rule(n: 3, label: "eq-F-Id", $Id(B, c(inl(x), x), c(inl(x'), x)) = Id(B, x, x') hctx [Gamma]$),
  rule(n: 2, label: "conv", $El_Id(z, (y). id(c(y, x))) in Id(B, x, x') hctx [Gamma]$),
)))
