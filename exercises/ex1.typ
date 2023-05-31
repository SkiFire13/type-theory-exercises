#import "/common.typ": *

#let Id = $"Id"$
#let id = "id"
#let type = $italic("type")$
#let cont = $italic("cont")$
#let El = "El"
#let Ap = "Ap"

#let xyzw = $Gamma$

#let hctx = h(0.5em)

#prooftree(
    axiom(label: "...", $xyzw cont$),
    rule(label: "var", $z in P(x) hctx [xyzw]$),

      axiom(label: "...", $P(z_2) type hctx [xyzw, z_1 in A, z_2 in A, z_3 in A, c in P(z_1)]$),
      rule(label: $"F-"Pi$, $Pi_(c in P(z_1)) P(z_2) type hctx [xyzw, z_1 in A, z_2 in A, z_3 in A]$),
      
      axiom(label: "...", $xyzw cont$),
      rule(label: "var", $x in A hctx [xyzw]$),
      
      axiom(label: "...", $xyzw cont$),
      rule(label: "var", $y in A hctx [xyzw]$),
      
      axiom(label: "...", $xyzw cont$),
      rule(label: "var", $w in Id(A, x, y) hctx [xyzw]$),

      axiom(label: "...", $xyzw, a in A, c in P(a) cont$),
      rule(label: "var", $c in P(a) hctx [xyzw, a in A, c in P(a)]$),
      rule(label: $"I-"Pi$, $lambda c. c in Pi_(c in P(a)) P(a) hctx [xyzw, a in A]$),
    rule(n: 5, label: "E-Id", $El_Id(w, (x). lambda c. c) in Pi_(c in P(x)) P(y) hctx [xyzw]$),

  rule(n: 2, label: $"E-"Pi$, $Ap(El_Id(w, (x). lambda c. c), z) in P(y) hctx [x in A, y in A, z in P(x), w in Id(A, x, y)]$),
)
