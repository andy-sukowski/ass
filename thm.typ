/* Customized great-theorems mathblocks */

#import "@preview/great-theorems:0.1.2": *
#import "@preview/rich-counters:0.2.1": *

#let mathcounter = rich-counter(
  identifier: "mathblocks",
  inherited_levels: 1,
)

#let plain_mathblock(blocktitle: none, prefix: none, ..args) = mathblock(
  blocktitle: blocktitle,
  prefix: if prefix == none {
            count => smallcaps([#blocktitle #count])
          } else {
            prefix
          },
  titlix: title => title,
  bodyfmt: body => [#h(0pt,weak: true) . #body],
  counter: mathcounter,
  ..args,
)

#let fancy_mathblock = plain_mathblock.with(
  inset: (left: 1em, y: 0.6em),
  outset: (left: -1pt),
  stroke: (left: black),
  breakable: false,
)
