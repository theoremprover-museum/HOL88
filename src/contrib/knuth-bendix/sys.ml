% sys.ml  - just load this one into HOL88, then run the tests
  at the bottom of the file group.ml
%
loadf `lib`;;
loadf `rewrite`;;
loadf `kb`;;
loadf `order`;;
unlink `group.th` ? ();;
loadt `group`;;
