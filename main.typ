#import "template.typ": template

// #set text(font: "New Computer Modern", size: 12pt)
// #set enum(indent: 1em)
// #set list(indent: 1em)
// #set page(margin: 1in)

// #let title = "Type Theory exercises"
// #let author = "Stevanato Giacomo"
// #let date = "2nd Semester 2022/23"

// #set document(title: title, author: author)

#show: template(
  title: "Type Theory exercises",
  author: "Stevanato Giacomo",
  date: "2nd Semester 2022/23",
)

= Chosen exercises

+ Exercise 10 from chapter 3.6 "Martin-Löf's Intensional Propositional Equality"
+ Exercise 11 from chapter 3.6 "Martin-Löf's Intensional Propositional Equality"
+ TODO

The solutions will follow one in each page.

#let fit(content) = {
  style(styles => {
    let sizes = measure(content, styles)
    page(width: sizes.width + 2in, height: sizes.height + 2in, content)
  })
}

#fit[
  #include "exercises/ex1.typ"
]
