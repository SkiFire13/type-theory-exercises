#import "template.typ": template

#set text(font: "New Computer Modern", size: 12pt)
#set enum(indent: 1em)
#set list(indent: 1em)
#set page(margin: 1in)

#let title = "Type Theory exercises"
#let author = "Stevanato Giacomo"
#let date = "2nd Semester 2022/23"

#set document(title: title, author: author)

#let fit(content) = {
  style(styles => {
    let sizes = measure(content, styles)
    set page(width: sizes.width + 2in, height: sizes.height + 2in)
    content
  })
}

#fit[
  #[ #align(center, text(size: 20pt, title)) ]
  #[ #align(center, text(size: 14pt, author)) ]
  #[ #align(center, text(size: 14pt, date)) ]
  #v(1em)
]
