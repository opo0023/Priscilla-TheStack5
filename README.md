# Milestone 2 – Recursive-Descent Parser with AST & Evaluation

## Build
```bash
gcc -std=c11 -O2 -Wall -Wextra -o parser parser.c
```

## Run (single input)
Type an expression/statement then Enter:
```bash
./parser
57*2-(3+4)
```

## Run (batch file)
Each non-empty line is parsed independently:
```bash
./parser -f tests.txt
```

## Grammar Implemented
```
statement  -> IDENT '=' expr | expr
expr       -> term {('+'|'-') term}*
term       -> power {('*'|'/') power}*
power      -> unary ['**' power]           // right-associative
unary      -> '++' unary | '--' unary | postfix
postfix    -> primary { '++' | '--' }*
primary    -> INT | IDENT | '(' expr ')'
```

- Precedence (high→low): `()` > `++/--` (prefix & postfix) > `**` (right-assoc) > `* /` > `+ -`.
- Identifiers evaluate from a simple symbol table (A..Z, a..z). Uninitialized vars default to `0`.
- `++`/`--` require an identifier lvalue. Prefix modifies then yields; postfix yields then modifies.

## Output Format
- **Token listing** as `lexeme,category` for each token consumed; error cases print up to the error token.
- **AST** labeled like the samples.
- **Final Value** (for successful parses).

## Notes
- Division is integer division.
- Negative exponents aren’t supported in integer arithmetic (clear runtime error).
- `++`/`--` on non-identifiers is a runtime error.
