######## 8T8 microcode compiler demo
#  cargo run -- -i demo/test.8t8.mc -f binary -o tmp/rom \
#   && ls tmp/rom_*.binary | xargs -n 1 xxd -b

@ a /b c ex/3 x y 
@ wide/4 z /not

~ ex  zero one two three four five six seven

> 2
= ex=three a b c
= ex=seven  wide=2

= a z
= b
= c
=
= a b ex=five
= a c
= b c
= a b c z

> h19
= a
