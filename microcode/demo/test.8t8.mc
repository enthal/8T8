######## 8T8 microcode compiler demo
#  cargo run -- -i demo/test.8t8.mc -f binary -o tmp/rom \
#   && ls tmp/rom_*.binary | xargs -n 1 xxd -b

@ a /b c ex/3 x y 
@ wide/4 z /not

~ ex  zero one two three four five six seven
~ wide  this that the-other three w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15

> b10
= ex=three a b c 
= ex=seven  wide=the-other  # into second partition
= wide=three

= a z
= b
= c
=
= a b ex=five
= a c
= b c
= a b c z

> h16
= a
