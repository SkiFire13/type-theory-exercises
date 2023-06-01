#import "template.typ": template

#set page(
  paper: "a3",
  flipped: true
)

#show: template(
  title: "Type Theory Exercises for the Exam",
  author: "Stevanato Giacomo",
  date: "2nd Semester 2022/23",
)

#include "exercises/ex1.typ"
#include "exercises/ex2.typ"
#include "exercises/ex3.typ"
