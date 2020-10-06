---
title: Preliminary Thoughts On Injective Monadic Pure Type Systems
author: WJL
fontsize: 12pt
header-includes:
- \usepackage{syntax}
- \usepackage{ebproof}
- \setlength{\grammarparsep}{20pt plus 1pt minus 1pt}
- \setlength{\grammarindent}{12em}
---

\newcommand{\kwlet}{\mathbf{let}}
\newcommand{\kwin}{\mathbf{in}}
\newcommand{\kwunit}{\mathbf{unit}}
\newcommand{\kwm}{\mathbf{M}}
\newcommand{\kwmt}{\mathbf{MT}}

# Introduction

I'm trying to extend a type checking algorithm for injective pure type systems to monadic type systems. 
The star and box types of both computations and values can be used to construct an injective type system. 
The axioms can reflect those of the lambda cube, but with one for values and one for computations. 
If the rules, accepting at any position a computation or value sort, have the second and third sort equal, then the type system is injective. 
The monadic operations are checkable in the typing rules, but the classification algorithm has issues. 
The operations are only shown typed while applied to an argument. 
I attempted to use the classification rules for application, lambdas, and dependent products to inform rules for the monadic operations. 
I didn't get anywhere with this. 
I was especially bother by the thought that I might need two PTS rules to type a constructor by itself, and not really need it in the applied form. 
I decided to proceed with monadic operations that are not already applied and see how that goes. 
My gut feeling is that they will be easier to work with. 
I suppose that each monad rule could just have the base sort of computations, but it feels weird. 
The other thing is that haskell does this in a similar way. 
The unsafe monads, namely ST and IO, are implemented like regular types and stuff. 
Then, it uses unsafe functions or the ffi or the interpreter idk to do special priviledged things. 


# Monad typing rules according to Barthe 1998

\begin{center}
\begin{prooftree}
  \hypo{\Gamma \vdash A : \ast^x}
  \infer1{\Gamma \vdash \kwm A : \ast^c}
\end{prooftree}
\qquad
\begin{prooftree}
  \hypo{\Gamma \vdash M : A}
  \hypo{\Gamma \vdash \kwm A : s}
  \infer2{\Gamma \vdash \kwunit M : \kwm A}
\end{prooftree}

\begin{prooftree}
  \hypo{\Gamma \vdash M : \kwm A}
  \hypo{\Gamma, x : A \vdash N : \kwm B}
  \infer2{\Gamma \vdash \kwlet x : A ,= M \kwin N : \kwm B}
\end{prooftree}
\end{center}

Although the work describes these as type constructors they are only shown in typing rules applied to another term. 
So lets isolate them. 
The rule for the monad type constructor implies that:

\begin{center}
\begin{prooftree}
  \infer0{\Gamma \vdash \kwm : \Pi \alpha : \ast^x . \alpha \rightarrow \ast^c}
\end{prooftree}
\end{center}

I am not sure I can type this dependence on both sorts, computations and values. 
Split them up. 

\begin{center}
\begin{prooftree}
  \infer0{\Gamma \vdash \kwm : \Pi \alpha : \ast^v . \alpha \rightarrow \ast^c}
\end{prooftree}
\qquad
\begin{prooftree}
  \infer0{\Gamma \vdash \kwmt : \Pi \alpha : \ast^c . \alpha \rightarrow \ast^c}
\end{prooftree}
\end{center}

That looks like a regular monad, and a monad transformer. 
That's kinda neat. 
First class monad transformers. 
So, all chains of monad transformers could hypothetically be terminated in a value monad. 
Or not, which is fine but might be interesting. 
There is obviously an identity monad for both monad transformers and monads, but the one for monads might be more interesting. 
Whatever the last actions of a properly terminating program, they end with a pure function returning a value. 
Maybe this can be exploited as some "main function", maybe its loader, or whatever. 
I have no clue. 

Anyway, we can now make operations for both types. 

