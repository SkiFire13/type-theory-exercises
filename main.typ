#import "template.typ": template

#show: template(
  title: "Type Theory exercises",
  author: "Stevanato Giacomo",
  date: "2nd Semester 2022/23",
)

#outline()

#let fit(content) = style(styles => {
  let sizes = measure(content, styles)
  page(width: sizes.width + 2in, height: sizes.height + 2in, content)
})

#fit(include "exercises/ex1.typ")
