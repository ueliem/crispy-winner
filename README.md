# A Language

## Introduction

This is a functional systems language

- Region based memory management
- Values are unboxed by default
- Built-in integer and boolean types
- Tuples

## Compiler Passes

- Parsing to abstract syntax tree
- Transform to core language
- Typechecking
- Conversion to A-normal form
- Conversion to SSA
- Conversion to Typed ASM
- Conversion to NASM

## Syntax

```
<binop> ::= "+" | "-" | "*" | "/"
<ident> ::= [a-zA-Z]+[a-zA-Z0-9]*
<integer> ::= [0-9]+

<regionvar> ::= <ident>
<regionset> ::= 
  "{" "}"
| "{" <regionvar> [ "," <regionvar> ]* "}"
<effect> ::= 
  "{" "}"
| "{" <regionvar> [ "," <regionvar> ]* "}"
```

### Type Syntax

```
<ty> ::= 
  "int"
| "bool"
| "unit"
| <tuplety>
| <funty>
| <regfunty>
| <boxty>

<tuplety> ::= <ty> [ "*" <ty> ]+
<funty> ::= "(" <ty> [ "," <ty> ]+ ")" "->" <effect> <ty>
<regfunty> ::= "forall" <regionset> <ty>
<boxty> ::= <ty> "at" <regionvar>
```

### Top Level Syntax
```
<program> ::= [ <declaration> ]+

<declaration> ::= 
  <valuedeclaration>
| <fundeclaration>
| <tydeclaration>

<valuedeclaration> ::= "val" <ident> ":" <ty> "=" <term>
<fundeclaration> ::= 
  "fun" <regionset> <ident> [ "(" <ident> ":" <ty> ")" ]+ ":" <ty> "=" <term>
<tydeclaration> ::= "type" <regionset> <ident> "=" <ty>
```

### Term Syntax

```
<term> ::= 
  <value>
| <var>
| <select>
| <box>
| <unbox>
| <let>
| <letregion>
| <elim>
| <ifelse>
| <app>
| <primapp>

<value> ::= 
  <intlit>
| <boollit>
| <unitlit>
| <tuple>
| <lambda>
<var> ::= <ident>
<select> ::= "sel" <integer> <term>
<box> ::= <term> "at" <regionvar>
<unbox> ::= "unbox" <term>
<let> ::= "let" <ident> "=" <term> "in" <term> "end"
<letregion> ::= "letregion" <ident> "in" <term> "end"
<elim> ::= "elim" <regionset> <term>
<ifelse> ::= "if" <term> "then" <term> "else" <term>
<app> ::= <term> [ <term> ]+
<primapp> ::= <term> <binop> <term>
```

### Value Syntax

```
<intlit> ::= <integer>
<boollit> ::= "true" | "false"
<unitlit> ::= "()"
<tuple> ::= "(" <term> [ "," <term> ]+ ")"
<lambda> ::= "fn" <regionset> [ "(" <ident> ":" <ty> ")" ]+ "=>" <term>
```

# Old Version

## Introduction

This is a functional systems language. 

- Pure Type System
	- Functional, semi-full
- Built-in integer and boolean types
- Pairs, First, and Second
- Sigma types
- Delta rules (WIP)
- Syntactic sugar (WIP)
- Core language with de Bruijn indices
- Type preserving compiler (WIP)

## TODO

- Good error messages
- Integer operations
- Delta rules
- Type check syntax phase
- ANF transform
- ANF type checking
- DTAL transform
- DTAL type checking
- Some final output

## Compiler Passes

- Parsing to abstract syntax tree
- Desugaring to core PTS
- Transforming to A-Normal form
- Closure conversion
- Transforming to DTAL

