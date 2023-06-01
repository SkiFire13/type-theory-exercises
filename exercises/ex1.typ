#import "/common.typ": *

#let title = "Chapter 3.6 Exercise 10"

#let exercise(full) = [
  It can be shown that there exists a proof-term #pf of the type \
  #h(1.5cm) $pf ∈ P (y) [x ∈ in, y in A, z in P(x), w in Id(A, x, y)]$ \
  for every $P(y) type hctx [x in A]$ derivable?

  #if full [
    *Full version*
  ] else [
    *Short version*
  ]

  #let xyzw = if full {
    $x in A, y in A, z in P(x), w in Id(A, x, y)$
  } else {
    $Gamma$
  }

  #let xyzw_cont_tree = if full {
    let xyz_cont_tree = (
      axiom($P(x) type hctx [x in A]$),
      axiom($A type hctx [#h(3pt)]$),
      axiom($A type hctx [#h(3pt)]$),
      rule(label: "F-C", $x in A cont$),
      rule(n: 2, label: "ind-ty", $A type hctx [x in A]$),
      rule(label: "F-C", $x in A, y in A cont$),
      rule(n: 2, label: "ind-ty", $P(x) type hctx [x in A, y in A]$),
      rule(label: "F-C", $x in A, y in A, z in P(x) cont$),
    )

    (
      axiom($A type [#h(3pt)]$),
      ..xyz_cont_tree,
      rule(n: 2, label: "ind-ty", $A type hctx [x in A, y in A, z in P(x)]$),
      ..xyz_cont_tree,
      rule(label: "var", $x in A hctx [x in A, y in A, z in P(x)]$),
      ..xyz_cont_tree,
      rule(label: "var", $y in A hctx [x in A, y in A, z in P(x)]$),
      rule(n: 3, label: "F-Id", $Id(A, x, y) type hctx [x in A, y in A, z in P(x)]$),
      rule(label: "F-C", $xyzw cont$),
    )
  } else {
    (
      axiom(label: "...", $xyzw cont$),
    )
  }

  #let pz2_type_tree = if full {
    let xyzwz1z2_cont_rule = (
      axiom($A type hctx [#h(3pt)]$),
        axiom($A type hctx [#h(3pt)]$),
        ..xyzw_cont_tree,
        rule(n: 2, label: "ind-ty", $A type hctx [xyzw]$),
        rule(label: "F-C", $xyzw, z_1 in A cont$),
      rule(n: 2, label: "ind-ty", $A type hctx [xyzw, z_1 in A]$),
      rule(label: "F-C", $xyzw, z_1 in A, z_2 in A cont$),
    )

    (
      axiom($P(z_2) type hctx [z_2 in A]$),
      axiom($P(z_1) type hctx [z_1 in A]$),
          axiom($A type hctx [#h(3pt)]$),
          ..xyzwz1z2_cont_rule,
        rule(n:2, label: "ind-ty", $A type hctx [xyzw, z_1 in A, z_2 in A]$),

        ..xyzwz1z2_cont_rule,
        rule(label: "var", $z_1 in A hctx [xyzw, z_1 in A, z_2 in A]$),
        
        ..xyzwz1z2_cont_rule,
        rule(label: "var", $z_2 in A hctx [xyzw, z_1 in A, z_2 in A]$),
      rule(n: 3, label: "F-Id", $Id(A, z_1, z_2) type hctx [xyzw, z_1 in A, z_2 in A]$),
      rule(label: "F-C", $xyzw, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2) cont$),
      rule(n: 2, label: "ind-ty", $P(z_1) type hctx [xyzw, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2)]$),
      rule(label: "F-C", $xyzw, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), c in P(z_1) cont$),
      rule(n: 2, label: "ind-ty", $P(z_2) type hctx [xyzw, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), c in P(z_1)]$),
    )
  } else {
    (
      axiom(label: "...", $P(z_2) type hctx [xyzw, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2), c in P(z_1)]$),
    )
  }

  #let xyzwa_cont_tree = if full {
    (
      axiom($P(a) type hctx [a in A]$),
      axiom($A type hctx [#h(3pt)]$),
      ..xyzw_cont_tree,
      rule(n: 2, label: "ind-ty", $A type hctx [xyzw]$),
      rule(label: "F-C", $xyzw, a in A cont$),
      rule(n: 2, label: "ind-ty", $P(a) type hctx [xyzw, a in A]$),
      rule(label: "F-C", $xyzw, a in A, c in P(a) cont$),
    )
  } else {
    (
      axiom(label: "...", $xyzw, a in A, c in P(a) cont$),
    )
  }

  #prooftree(
      ..xyzw_cont_tree,
      rule(label: "var", $z in P(x) hctx [xyzw]$),

        ..pz2_type_tree,
        rule(label: $"F-"Pi$, $Pi_(c in P(z_1)) P(z_2) type hctx [xyzw, z_1 in A, z_2 in A, z_3 in Id(A, z_1, z_2)]$),
        
        ..xyzw_cont_tree,
        rule(label: "var", $x in A hctx [xyzw]$),
        
        ..xyzw_cont_tree,
        rule(label: "var", $y in A hctx [xyzw]$),
        
        ..xyzw_cont_tree,
        rule(label: "var", $w in Id(A, x, y) hctx [xyzw]$),

        ..xyzwa_cont_tree,
        rule(label: "var", $c in P(a) hctx [xyzw, a in A, c in P(a)]$),
        rule(label: $"I-"Pi$, $lambda c. c in Pi_(c in P(a)) P(a) hctx [xyzw, a in A]$),
      rule(n: 5, label: "E-Id", $El_Id(w, (x). lambda c. c) in Pi_(c in P(x)) P(y) hctx [xyzw]$),

    rule(n: 2, label: $"E-"Pi$, $Ap(El_Id(w, (x). lambda c. c), z) in P(y) hctx [x in A, y in A, z in P(x), w in Id(A, x, y)]$),
  )
]
