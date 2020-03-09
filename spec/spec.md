---
fontsize: 12pt
header-includes:
- \usepackage{syntax}
- \usepackage{ebproof}
- \setlength{\grammarparsep}{20pt plus 1pt minus 1pt}
- \setlength{\grammarindent}{12em}
---

## Syntax

\begin{grammar}

<binop> ::= `+' | `-' | `*' | `/'

<ident> ::= [a-zA-Z]+[a-zA-Z0-9]*

<integer> ::= [0-9]+

<regionvar> ::= <ident>

<regionset> ::= 
  `{' `}'
\alt `{' <regionvar> [ `,' <regionvar> ]* `}'

<effect> ::= 
  `{' `}'
\alt `{' <regionvar> [ `,' <regionvar> ]* `}'

\end{grammar}

### Type Syntax

\begin{grammar}

<ty> ::= 
  `int'
\alt `bool'
\alt `unit'
\alt <tuplety>
\alt <funty>
\alt <regfunty>
\alt <boxty>

<tuplety> ::= <ty> [ `*' <ty> ]+

<funty> ::= `(' <ty> [ `,' <ty> ]+ `)' `->' <effect> <ty>

<regfunty> ::= `forall' <regionset> <ty>

<boxty> ::= <ty> `at' <regionvar>

\end{grammar}

### Top Level Syntax

\begin{grammar}

<program> ::= [ <declaration> ]+

<declaration> ::= 
  <valuedeclaration>
\alt <fundeclaration>
\alt <tydeclaration>

<valuedeclaration> ::= `val' <ident> `:' <ty> `=' <term>

<fundeclaration> ::= `fun' <regionset> <ident> [ `(' <ident> `:' <ty> `)' ]+ `:' <ty> `=' <term>

<tydeclaration> ::= `type' <regionset> <ident> `=' <ty>

\end{grammar}

### Term Syntax

\begin{grammar}

<term> ::= 
  <value>
\alt <var>
\alt <select>
\alt <box>
\alt <unbox>
\alt <let>
\alt <letregion>
\alt <elim>
\alt <ifelse>
\alt <app>
\alt <primapp>

<value> ::= 
  <intlit>
\alt <boollit>
\alt <unitlit>
\alt <tuple>
\alt <lambda>

<var> ::= <ident>

<select> ::= `sel' <integer> <term>

<box> ::= <term> `at' <regionvar>

<unbox> ::= `unbox' <term>

<let> ::= `let' <ident> `=' <term> `in' <term> `end'

<letregion> ::= `letregion' <ident> `in' <term> `end'

<elim> ::= `elim' <regionset> <term>

<ifelse> ::= `if' <term> `then' <term> `else' <term>

<app> ::= <term> [ <term> ]+

<primapp> ::= <term> <binop> <term>

\end{grammar}

### Value Syntax

\begin{grammar}

<intlit> ::= <integer>

<boollit> ::= `true' \alt `false'

<unitlit> ::= `()'

<tuple> ::= `(' <term> [ `,' <term> ]+ `)'

<lambda> ::= `fn' <regionset> [ `(' <ident> `:' <ty> `)' ]+ `=>' <term>

\end{grammar}

## Type System

\begin{prooftree}
\hypo{ \Gamma, A &\vdash B }
\infer1[abs]{ \Gamma &\vdash A\to B }
\end{prooftree}

