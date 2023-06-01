#import "template.typ": template

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

#let fit(content) = style(styles => {
  let sizes = measure(content, styles)
  page(width: sizes.width + 2in, height: sizes.height + 2in, content)
})

#let exercise(path) = {
  import "exercises/" + path: title, exercise
  fit[
    = #title
    #v(1cm)
    #exercise(false)
    #v(1cm)
    #exercise(true)
  ]
}

#exercise("ex1.typ")
