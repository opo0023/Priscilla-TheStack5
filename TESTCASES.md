# Test Cases for Parser (Milestone 2)

Each test lists: **Input**, **Purpose**, and expected **Outcome**.

1) `2+3` — addition → 5
2) `4*5` — multiplication → 20
3) `20/4` — division → 5
4) `2**3**2` — right-assoc power → 512
5) `57*2-(3+4)` — grouping/precedence → 107
6) `2*3+5` — precedence → 11
7) `A=2*(3+5)` — assignment → 16
8) `A` — identifier readback (after 7) → 16
9) `++A` — prefix inc (after 8) → 17
10) `A++` — postfix inc → yields prior A
11) `++A + A++` — side effects
12) `A++++` — postfix chain (two increments)
13) `++(A)` — runtime lvalue error
14) `Sum=Sum*+count` — syntax error at '+'
15) `(2+3` — missing right paren
16) `10/(5-5)` — division by zero
17) `2*3**2` — power binds above multiply → 18
