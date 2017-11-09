\documentclass[review]{elsarticle}

%\modulolinenumbers[5]

%if False
\begin{code}
module regex where
\end{code}
%endif 
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{graphicx}
\usepackage{amsmath,amsthm}
\usepackage{amssymb}
\usepackage{url}
\usepackage{stmaryrd}
\usepackage{ifpdf, proof}
\ifpdf
  \usepackage{hyperref}
\fi
%\usepackage[x11names]{xcolor}
%\usepackage[all]{xy}
%\usepackage{xspace}
%\usepackage{pstricks}
%\usepackage{listings}
%\usepackage{wrapfig}
%\usepackage{mathpartir}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}
%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\V{" a "}"
%subst varid a = "\V{" a "}"
%subst numeral a = "\C{" a "}"

\newtheorem{Lemma}{Lemma}
\newtheorem{Theorem}{Theorem}
\theoremstyle{definition}
\newtheorem{Example}{Example}

\usepackage{color}
\newcommand{\redFG}[1]{\textcolor[rgb]{0.6,0,0}{#1}}
\newcommand{\greenFG}[1]{\textcolor[rgb]{0,0.4,0}{#1}}
\newcommand{\blueFG}[1]{\textcolor[rgb]{0,0,0.8}{#1}}
\newcommand{\orangeFG}[1]{\textcolor[rgb]{0.8,0.4,0}{#1}}
\newcommand{\purpleFG}[1]{\textcolor[rgb]{0.4,0,0.4}{#1}}
\newcommand{\yellowFG}[1]{\textcolor{yellow}{#1}}
\newcommand{\brownFG}[1]{\textcolor[rgb]{0.5,0.2,0.2}{#1}}
\newcommand{\blackFG}[1]{\textcolor[rgb]{0,0,0}{#1}}
\newcommand{\whiteFG}[1]{\textcolor[rgb]{1,1,1}{#1}}
\newcommand{\yellowBG}[1]{\colorbox[rgb]{1,1,0.2}{#1}}
\newcommand{\brownBG}[1]{\colorbox[rgb]{1.0,0.7,0.4}{#1}}

\newcommand{\ColourStuff}{
  \newcommand{\red}{\redFG}
  \newcommand{\green}{\greenFG}
  \newcommand{\blue}{\blueFG}
  \newcommand{\orange}{\orangeFG}
  \newcommand{\purple}{\purpleFG}
  \newcommand{\yellow}{\yellowFG}
  \newcommand{\brown}{\brownFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\whiteFG}
}

\newcommand{\MonochromeStuff}{
  \newcommand{\red}{\blackFG}
  \newcommand{\green}{\blackFG}
  \newcommand{\blue}{\blackFG}
  \newcommand{\orange}{\blackFG}
  \newcommand{\purple}{\blackFG}
  \newcommand{\yellow}{\blackFG}
  \newcommand{\brown}{\blackFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\blackFG}
}

\ColourStuff

\newcommand{\D}[1]{\blue{\mathsf{#1}}}
\newcommand{\C}[1]{\red{\mathsf{#1}}}
\newcommand{\F}[1]{\green{\mathsf{#1}}}
\newcommand{\V}[1]{\purple{\mathit{#1}}}


\journal{Science of Computer Programming}

\bibliographystyle{elsarticle-num}

\begin{document}

\begin{frontmatter}

\title{Certified Derivative-Based Parsing of\\ Regular Expressions}

%% Group authors per affiliation:

\author[rgr]{Rodrigo Ribeiro}
\cortext[rgr]{Corresponding author}
\address{Dep. de Computa\c{c}\~ao, Universidade
Federal de Ouro Preto, ICEB, \newline Campus Universit\'ario Morro do
Cruzeiro, Ouro Preto, Minas Gerais, Brasil}
\ead{rodrigo@@decsi.ufop.br}

\author{Raul Lopes}
\address{Dep. de Computa\c{c}\~ao, Universidade
  Federal de Ouro Preto, ICEB, \newline Campus Universit\'ario Morro do
  Cruzeiro, Ouro Preto, Minas Gerais, Brasil}
\ead{raulfpl@@gmail.com}

\author{Carlos Camar\~ao}
\address{Dep. de Ci\^encia da Computa\c{c}\~ao, Universidade Federal
  de Minas Gerais, \newline Av. Ant\^onio Carlos 6627, Belo Horizonte, Minas Gerais, Brasil}
\ead{camarao@@dcc.ufmg.br}

\begin{abstract}

We describe the formalization of Brzozowski and Antimirov derivative
based algorithms for regular expression parsing, in the dependently
typed language Agda. The formalization produces a proof that either an
input string matches a given regular expression or that no matching
exists. A tool for regular expression based search in the style of the
well known GNU grep has been developed with the certified algorithms.
Practical experiments conducted with this tool are reported.

\end{abstract}

\begin{keyword}
Certified algorithms, regular expressions; dependent types
\end{keyword}

\end{frontmatter}

%format . = "."
%format Set = "\D{Set}"
%format Set0 = Set "_{\D{0}}"
%format Set1 = Set "_{\D{1}}"
%format List = "\D{List}"
%format [] = "\C{\lbrack\:\rbrack}"
%format , = "\red{,}\,"
%format Nat = "\D{\mathbb{N}}"
%format zero = "\C{zero}"
%format succ = "\C{suc}"
%format id = "\F{id}"
%format o = "\F{\circ}"
%format Vec = "\D{Vec}"

\section{Introduction}\label{sec:intro}

Parsing is the process of analysing if a string of symbols conforms to
a given set of rules. It involves in computer science the formal
specification of the rules in a grammar and, also, either the
construction of data that makes evident which rules have been used to
conclude that the string of symbols can be obtained from the grammar
rules or, otherwise, an indication of an error that represents the
fact that the string of symbols cannot be generated from the grammar
rules.

In this work we are interested in the parsing problem for regular
languages (RLs)~\cite{Hopcroft2000}, i.e.~languages that can be
recognized by (non-)deterministic finite automata and equivalent
formalisms. Regular expressions (REs) are an algebraic and compact way
of specifying RLs that are extensively used in lexical analyser
generators~\cite{Lesk1990} and string search utilities~\cite{Grep}.
Since such tools are widely used and parsing is pervasive in
computing, there is a growing interest on certified parsing
algorithms~\cite{FirsovU13,Firsov14,Danielsson2010}.  This interest
is motivated by the recent development of dependently typed
languages. Such languages are powerful enough to express algorithmic
properties as types, that are automatically checked by a compiler.

The use of derivatives for regular expressions were introduced by
Brzozowski~\cite{Brzozowski1964} as an alternative method to compute a
finite state machine that is equivalent to a given RE and to perform
RE-based parsing. According to Owens et. al~\cite{Owens2009},
``derivatives have been lost in the sands of time'' until their work on
functional encoding of RE derivatives have renewed interest on their use
for parsing~\cite{Might2011,Fischer2010}.  In this work, we provide a
complete formalization of an algorithm for RE parsing using
derivatives \cite{Owens2009}, and describe a RE based search tool we developed by 
using the dependently typed language
Agda~\cite{Norell2009}. We want to emphasize that what we call ``RE parsing''
is the problem of finding all prefixes and substrings of an input that matches
a given RE, as in RE based text search tools as GNU-grep~\cite{Grep}.

More specifically, our contributions are:
\begin{itemize}
  \item A formalization of Brzozowski derivatives based RE parsing in
    Agda. The certified algorithm presented produces as a result
    either a proof term (parse tree) that is evidence that the input
    string is in the language of the input RE or a witness that such
    parse tree does not exist.

  \item A detailed explanation of the technique used to simplify
    derivatives using ``smart-constructors''~\cite{Owens2009}.
    We give formal proofs that smart constructors indeed preserve
    the language recognized by REs.

  \item A formalization of Antimirov's partial derivatives and their use to
    construct a RE parsing algorithm. The main difference between
    partial derivatives and Brzozowski's is that the former computes a
    set of REs using set operators instead of ``smart-constructors''.
    Producing a set of REs avoids the need of simplification using
    smart constructors.
\end{itemize}

This paper extends our SBLP 2016 paper~\cite{Lopes2016} by formalizing
a RE parsing algorithm using Antimirov's partial
derivatives~\cite{Antimirov1996}.  Also our original paper uses
Idris~\cite{Brady2013} instead of Agda. This change was motivated by a
modification in Idris totality checker that refuses some (correct and
total) proofs that are both accepted by Agda's and Coq totality
checkers. All source code produced in Idris, Agda and Coq, including
the \LaTeX~ source of this article, are avaliable
on-line~\cite{regex-rep}.

The rest of this paper is organized as follows. Section~\ref{sec:agda}
presents a brief introduction to Agda. Section~\ref{sec:regexp}
describes the encoding of REs and its parse trees. In
Section~\ref{sec:deriv} we define Brzozowski and Antimirov derivatives
and smart constructors, some of their properties and describe how to
build a correct parsing algorithm from them. Section~\ref{sec:exp}
comments on the use of the certified algorithm to build a tool for
RE-based search and present some experiments with this tool. Related
work is discussed on
Section~\ref{sec:related}. Section~\ref{sec:conclusion} concludes.

All the source code in this article has been formalized in Agda
version 2.5.2 using Standard Library 0.13, but
we do not present every detail. Proofs of some properties result in
functions with a long pattern matching structure, that would distract
the reader from understanding the high-level structure of the
formalization. In such situations we give just proof sketches and point
out where all details can be found in the source code.

\section{An Overview of Agda}\label{sec:agda}

%format String = "\D{String}"
%format Bool = "\D{Bool}"

Agda is a dependently-typed functional programming language based on
Martin-L\"of intuitionistic type theory~\cite{Lof98}.  Function types
and an infinite hierarchy of types, |Set l|, where |l| is a
natural number, are built-in. Everything else is a user-defined
type. The type |Set|, also known as |Set0|, is the type of all
``small'' types, such as |Bool|, |String| and |List Bool|.  The type
|Set1| is the type of |Set| and ``others like it'', such as |Set ->
Bool|, |String -> Set|, and |Set -> Set|. We have that |Set l| is an
element of the type |Set (l+1)|, for every $l≥0$. This
stratification of types is used to keep Agda consistent as a logical
theory~\cite{Sorensen2006}.

An ordinary (non-dependent) function type is written |A -> B| and a
dependent one is written |(x : A) -> B|, where type |B| depends on
|x|, or |∀ (x : A) -> B|. Agda allows the definition of \emph{implicit
parameters}, i.e.  parameters whose value can be infered from the
context, by surrounding them in curly braces: |∀ {x : A} -> B|. To
avoid clutter, we'll omit implicit arguments from the source code
presentation. The reader can safely assume that every free variable in
a type is an implicity parameter.

As an example of Agda code, consider the the following data type of
length-indexed lists, also known as vectors.

\begin{code}
  data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

  data Vec (A : Set) : Nat -> Set where
    []  : Vec A zero
    _::_ : ∀ {n} -> A -> Vec A n -> Vec A (succ n)
\end{code}
The |Vec| type uses some interesting concepts. 
First, |Vec| is \emph{parameterized} by a type |A : Set|, which means that 
in every occurrence of |Vec| its parameter |A| should not change. Second, 
the type of |Vec A| is |Nat -> Set|, i.e.
|Vec A| is a family of types indexed by natural numbers. 
For each natural number |n|, |Vec A n| is a type. 

%format head = "\F{head}"
In |Vec|'s definition, constructor |[]| builds empty vectors. The cons-operator (|_::_|)
inserts a new element in front of a vector of $n$ elements (of type
|Vec A n|) and returns a value of type |Vec A (succ n)|. The
|Vec| datatype is an example of a dependent type, i.e. a type
that uses a value (that denotes its length). The usefulness of
dependent types can be illustrated with the definition of a safe list
head function: |head| can be defined to accept only non-empty
vectors, i.e.~values of type |Vec A (succ n)|.
\begin{spec}
  head : Vec A (succ n) -> A
  head (x :: xs) = x
\end{spec}
In |head|'s definition, constructor |[]| is not used. The
Agda type-checker can figure out, from |head|'s parameter type,
that argument |[]| to |head| is not type-correct.

%format _==_ = "\D{" == "}"
%format == = "\D{\equiv}"
%format refl = "\C{refl}"

Thanks to the propositions-as-types principle\footnote{Also known as
  Curry-Howard ``isomorphism''~\cite{Sorensen2006}.} we can interpret
types as logical formulas and terms as proofs. We can encode logical
disjunction as the following Agda type:
%format inj₁ = "\C{inj_1}"
%format inj₂ = "\C{inj_2}"
%format _⊎_    = "\D{\_\lor\_}"
%format ⊎ = "\D{\lor}"

\begin{code}
   data _⊎_ (A B : Set) : Set where
     inj₁ : A -> A ⊎ B
     inj₂ : B -> A ⊎ B
\end{code}    
Note that each constructor of the previous data type represents how
we can build evidence for the proposition |A ⊎ B|: using constructor
|inj₁| together with an evidence for |A| or using constructor |inj₂| and 
evidence for |B|. Intuitively, type |_⊎_| encodes the intuitionistic intepretation
of disjunction. Another important example is the
representation of equality as the following Agda type:

\begin{code}
  data _==_ {l}{A : Set l}(x : A) : A -> Set where
    refl : x == x
\end{code}

%format not = "\F{\neg}"
%format Dec = "\D{Dec}"
%format yes = "\C{yes}"
%format no  = "\C{no}"
%format Even = "\C{Even}"
%format Odd = "\C{Odd}"
%format Parity = "\D{Parity}"
%format parity = "\F{parity}"
%format natToBin = "\F{natToBin}"
%format false = "\C{false}"
%format true = "\C{true}"
%format + = "\F{+}"
%format Bot = "\D{\bot}" 
This type is called propositional equality. It defines that there is
a unique evidence for equality, constructor |refl| (for reflexivity),
that asserts that the only value equal to |x| is itself. Given a type |P|,
type |Dec P| is used to build proofs that |P| is a
decidable proposition, i.e.~that either |P| or not |P|
holds. The decidable proposition type is defined as:
\begin{spec}
  data Dec (P : Set) : Set where
     yes : P -> Dec P
     no  : not P -> Dec P
\end{spec}
Constructor |yes| stores a proof that property |P| holds
and constructor |no| an evidence that such proof is impossible. Some functions
used in our formalization use this type. The type |¬ P| is an
abbreviation for |P -> Bot|, where
|Bot| is a data type with no constructors (i.e.~a data
type for which it is not possible to construct a value, which corresponds to
a false proposition).

Dependently typed pattern matching is built by using the so-called
|with| construct, that allows for matching intermediate
values~\cite{McBride2004}. If the matched value has a dependent type,
then its result can affect the form of other values. For example,
consider the following code that defines a type for natural number
parity. If the natural number is even, it can be represented as the
sum of two equal natural numbers; if it is odd, it is equal to one
plus the sum of two equal values. Pattern matching on a value of
|Parity n| allows to discover if $n = j + j$ or $n = S (k + k)$,
for some $j$ and $k$ in each branch of |with|.  Note that the
value of $n$ is specialized accordingly, using information ``learned''
by the type-checker.
\begin{spec}
data Parity : Nat -> Set where
   Even : ∀ {n : Nat} -> Parity (n + n)
   Odd  : ∀ {n : Nat} -> Parity (succ (n + n))

parity : (n : Nat) -> Parity n
parity = -- definition omitted

natToBin : Nat -> List Bool
natToBin zero = []
natToBin k with (parity k)
   natToBin (j + j)     | Even = false :: natToBin j
   natToBin (succ (j + j)) | Odd  = true  :: natToBin j
\end{spec}

For further information about Agda, see~\cite{Norell2009,Stump16}.


\section{Regular Expressions}\label{sec:regexp}


%format Char = "\D{Char}"

Regular expressions are defined with respect to a given
alphabet. Formally, RE syntax follows the following context-free
grammar
\[
e ::= \emptyset\,\mid\,\epsilon\,\mid\,a\,\mid\,e\,e\,\mid\,e+e\,\mid\,e^{\star}
\]
where $a$ is any symbol from the underlying alphabet.
In our original Idris formalization, we described symbols of an alphabet as a natural number
in Peano notation (type |Nat|), i.e.~the symbol's numeric
code. The reason for this design choice is due to the way that Idris
deals with propositional equality for primitive types, like
|Char|. Equalities of values of these types only reduce on
concrete primitive values; this causes computation of proofs to stop
under variables whose type is a primitive one. Thus, we decided to use
the inductive type |Nat| to represent the codes of alphabet
symbols. In our Agda formalization, in contrast, we represent alphabet symbols using type |Char|.

%format Regex = "\D{Regex}"
%format Eps = "\C{\lambda}"
%format ∅ = "\C{\emptyset}"
%format # = "\C{\$}"
%format ∙ = "\C{∙}"
%format + = "\C{+}"
%format ⋆ = "\C{\star}"
%format #_ = "\C{\$\_}"
%format _∙_ = "\C{\_∙\_}"
%format _+_ = "\C{\_+\_}"
%format _⋆ = "\C{\_\star}"


Datatype |Regex| encodes RE syntax.

\begin{spec}
  data Regex : Set where
    ∅  : Regex
    Eps : Regex
    #_  : Char -> Regex
    _∙_ : Regex -> Regex -> Regex
    _+_ : Regex -> Regex -> Regex
    _⋆  : Regex -> Regex
\end{spec}
Constructors |∅| and |Eps| denote respectively the
empty language ($\emptyset$) and the empty string ($\lambda$). Alphabet
symbols are constructed by using the |#| constructor. Composite REs are
built using concatenation (|∙|), union (|+|) and
Kleene star (|⋆|).

%format _<<-[[_]] = "\D{\_\in\llbracket\_\rrbracket}"
%format <<-[[ = "\D{\in\llbracket}"
%format ]] = "\D{\rrbracket}"
%format ++ = "\F{++}"
%format _∙_=>_ = "\C{\_∙\_\Rightarrow\_}"
%format => = "\C{\Rightarrow}"
%format _+L_ = "\C{\_+L\_}"
%format _+R_ = "\C{\_+R\_}"
%format +L = "\C{+L}"
%format +R = "\C{+R}"

We define RE semantics as the inductively defined judgment $s \in e$, 
which means that string $s$ is in the language denoted by RE $e$.
\[
    \begin{array}{ccc}
        \infer[_{Eps}]{\epsilon \in \epsilon}{}
        & 
        \infer[_{Chr}]{a \in a}{}
        &
        \infer[_{Cat}]{ss' \in ee'}
                      {s \in e & s' \in e'} \\ \\
        \infer[_{Left}]{s \in e + e'}
                       {s \in e} & 
        \infer[_{Right}]{s \in e + e'}
                        {s \in e'} &
        \infer[_{StarBase}]{\epsilon \in e^\star}{} \\ \\ 
        \multicolumn{3}{c}{
            \infer[_{StarRec}]
                  {ss' \in e^\star}
                  {s \in e & s' \in e^\star}
        }
    \end{array}
\]
Rule $Eps$ specifies that only the empty string is accepted by RE $\epsilon$, while 
rule $Chr$ says that a single character string is accepted by the RE formed by this
character. The rules for concatenation and choice are straightforward. For Kleene star, 
we need two rules: the first specifies that the empty string is in the language of RE $e^\star$ and 
rule $StarRec$ says that the string $ss'$ is in the language denoted by $e^\star$ if 
$s \in e$ and $s' \in e^\star$.

\begin{Example}
    The string $aab$ is in the language of RE $(aa + b)^\star$, as the following derivation shows:
    \[
        \infer[_{StarRec}]{aab \in (aa + b)^\star}
              {
                  \infer[_{Left}]{aa \in aa + b}
                        {
                            \infer[_{Cat}]{aa \in aa}
                                  {
                                      \infer[_{Chr}]{a \in a}{} &
                                      \infer[_{Chr}]{a \in a}{}
                                  }
                        }
                  & 
                  \infer[_{StarRec}]{b \in (aa + b)^\star}
                        {
                            \infer[_{Right}]{b \in aa + b}
                                  {
                                      \infer[_{Chr}]{b \in b}{}
                                  }
                            & 
                            \infer[_{StarBase}]{\epsilon \in (aa + b)^\star}{}
                        }          
              }
    \]
\end{Example}
In our formalization, we represent strings as values of type |List Char| and we encode the RE semantics
as an inductive data type in which each constructor represents a rule for the previously defined semantics.
Agda allows the overloading of constructor names. In some cases we use the same symbol both 
in the RE syntax and in the definition of its semantics.

\begin{spec}
  data _<<-[[_]] : List Char -> Regex -> Set where
    Eps : [] <<-[[ Eps ]]
    #_  : (a : Char) -> [ a ] <<-[[ # a ]]
    _∙_=>_ : xs <<-[[ l ]]  -> ys <<-[[ r ]]  -> zs == xs ++ ys -> zs <<-[[ l ∙ r ]]
    _+L_ : (r : Regex) -> xs <<-[[ l ]] -> xs <<-[[ l + r ]]
    _+R_ : (l : Regex) -> xs <<-[[ r ]] -> xs <<-[[ l + r ]]
    _⋆ : xs <<-[[ Eps + (e ∙ e ⋆) ]] -> xs <<-[[ e ⋆ ]]
\end{spec}

Constructor |Eps| states that the empty string (denoted by the empty list |[]|)
is in the language of RE |Eps|.

For any single character |a|, the singleton
string |[ a ]| is in the RL
for |# a|. Given parse trees for REs
|l| and |r|, |xs <<-[[ l ]]| and |ys <<-[[ r ]]|, constructor
|_∙_=>_| can be used to build a parse tree
for the concatenation of these REs.  Constructor
|_+L_| (|_+R_|) creates a parse tree
for |l + r| from a parse tree for |l| (|r|). Parse trees for Kleene star
are built using the following well known equivalence of REs: $e^\star
= \epsilon + e\,e^\star$.

Several inversion lemmas about RE parsing relation are necessary for
derivative-based parsing formalization. They consist of
pattern-matching on proofs of
\ensuremath{\D{\_\in\llbracket\_\rrbracket}}. As an example, we present below the inversion 
lemma for choice operator.

%format ∈+-invert = "\F{+invert}"
%format inj₁ = "\C{inj_1}"
%format inj₂ = "\C{inj_2}"
%format ⊎    = "\D{\lor}"
\begin{spec}
  ∈+-invert : ∀ {xs l r} → xs <<-[[ l + r ]] → xs <<-[[ l ]] ⊎ xs <<-[[ r ]]
  ∈+-invert (r +L pr) = inj₁ pr
  ∈+-invert (l +R pr) = inj₂ pr    
\end{spec}    

%format []∈∙-invert = "\F{∙-invert}"
%format ** = "\D{\times}"
%format :: = "\C{::}"
%format #-invert = "\F{charInvert}"

Intuitively, function |∈+-invert| specifies that, in the case that |xs <<-[[ l + r ]]|,
the string |xs| matches RE |l| or it matches the RE |r|. Another inversion lemma 
(function |#-invert|) specifies that 
if a string |x :: xs| matches RE |# y| then the input string must be a single character string, 
i.e. |xs == []| and |x == y|.

\begin{spec}
  #-invert : ∀ {x y xs} → x :: xs <<-[[ # y ]] → x == y ** xs == []
  #-invert (# c) = refl , refl
\end{spec}    

In our formalization of RE semantics we have defined other inversions lemmas. They follow the same
structure of the previously defined lemmas --- they produce, as result, the necessary conditions for a RE semantics 
proof to hold --- and are omitted for brevity.

\section{Derivatives, Smart Constructors and Parsing}\label{sec:deriv}

Formally, the derivative of a formal language $L\subseteq
\Sigma^\star$ with respect to a symbol $a\in\Sigma$ is the language
formed by suffixes of $L$ words without the prefix $a$.

An algorithm for computing the derivative of a language represented by
a RE as another RE is due to Brzozowski~\cite{Brzozowski1964}. It
relies on a function (called $\nu$) that determines if some RE accepts
or not the empty string (by returning |Eps| or |∅|, respectively):
\[
    \begin{array}{lcl}
         \nu(\emptyset) & = & \emptyset \\
         \nu(\epsilon)    & = & \epsilon \\
         \nu(a)                & = & \emptyset \\
         \nu(e\,e')           & = & \left\{
                                                 \begin{array}{ll}
                                                      \epsilon &
                                                                 \text{if
                                                                 }\nu(e)
                                                                 =
                                                                 \nu(e')
                                                                 =
                                                                 \epsilon
                                                   \\
                                                   \emptyset &
                                                               \text{otherwise}
                                                 \end{array}
                                             \right. \\
         \nu(e + e')  & = & \left\{
                                         \begin{array}{ll}
                                              \epsilon & \text{if
                                                         }\nu(e) =
                                                         \epsilon
                                                         \text{ or
                                                         }\nu(e') =
                                                         \epsilon \\
                                              \emptyset & \text{otherwise}
                                         \end{array}
                                      \right. \\
         \nu(e^\star) & = & \epsilon
    \end{array}
\]
%format nuu[_] = "\F{\nu[\_]}"
%format nuu[ = "\F{\nu[ }"
%format ]> = "\F{]}"
%format proj₁ = "\F{\pi_1}"
%format proj₂ = "\F{\pi_2}"
%format +invert = "\F{+invert}"
%format ∙invert = "\F{∙invert}"
Decidability of $\nu(e)$ is proved by function |nuu[_]|,
which is defined by induction over the structure of the input RE
|e| and returns a proof that the empty string is accepted or
not, using Agda type of decidable propositions, |Dec P|.
\begin{spec}
  nuu[_] : ∀ (e : Regex) → Dec ( [] <<-[[ e ]])
  nuu[ ∅ ]> = no (\ ())
  nuu[ Eps ]> = yes Eps
  nuu[ # x ]> = no (\ ())
  nuu[ e ∙ e' ]> with nuu[ e ]> | nuu[ e' ]>
  nuu[ e ∙ e' ]> | yes pr | (yes pr1) = yes (pr ∙ pr1 ⇒ refl)
  nuu[ e ∙ e' ]> | yes pr | (no ¬pr1) = no (¬pr1 ∘ proj₂ ∘ ∙invert)
  nuu[ e ∙ e' ]> | no ¬pr | pr1 = no (¬pr ∘ proj₁ ∘ ∙invert)
  nuu[ e + e' ]> with nuu[ e ]> | nuu[ e' ]>
  nuu[ e + e' ]> | yes pr | pr1 = yes (e' +L pr)
  nuu[ e + e' ]> | no ¬pr | (yes pr1) = yes (e +R pr1)
  nuu[ e + e' ]> | no ¬pr | (no ¬pr1) = no ( [ ¬pr , ¬pr1 ] ∘ +invert)
  nuu[ e ⋆ ]> = yes ((e ∙ e ⋆ +L Eps) ⋆) 
\end{spec}
The definition of |nuu[_]| uses some of the inversion lemmas about
RE semantics. Lemma |∙invert| states that if the empty string
is in the language of |l ∙ r| (where |l| and |r| are arbitrary REs)
then the empty string belongs to |l| and |r|'s languages.
Lemma |∈+-invert| is defined similarly for union.

\subsection{Smart Constructors}\label{sec:smart}

In order to define Brzozowski derivatives, we follow Owens et. al.~\cite{Owens2009}. We use
smart constructors to identify equivalent REs modulo identity and nullable
elements, $\epsilon$ and $\emptyset$, respectively. RE equivalence is
denoted by $e \approx e'$ and it's defined as usual~\cite{Hopcroft2000}.
The equivalence axioms maintained by smart constructors are:
\begin{itemize}
    \item For union:
      \[
          \begin{array}{ccc}
              1)\: e + \emptyset \approx e &\hspace{1cm} & 2)\: \emptyset + e \approx e
          \end{array}
      \]
      \item For concatenation:
      \[
          \begin{array}{ccc}
              1)\: e\:\emptyset \approx \emptyset & \hspace{1cm} & 2)\: e\:\epsilon \approx e\\
              3)\: \emptyset\:e\approx \emptyset & & 4)\: \epsilon\: e \approx e\\
          \end{array}
      \]
      \item For Kleene star:
      \[
           \begin{array}{ccc}
               1)\: \emptyset^\star \approx \epsilon & \hspace{1cm} & 2)\: \epsilon^\star
                                                  \approx \epsilon
           \end{array}
      \]
\end{itemize}
%format _`+_ = "\F{\_`+\_}"
%format `+ = "\F{`+}"
%format _`∙_ = "\F{\_`∙\_}"
%format `∙ = "\F{`∙}"
%format _`⋆ = "\F{\_`⋆}"
%format `⋆ = "\F{`⋆}"

These axioms are kept as invariants using functions that preserve them
while building REs. As a convention, a smart constructor is named by 
prefixing the constructor name with a back quote. In the case of union, 
the definition of the smart constructor differs only when one the 
parameters denotes the empty language:
\begin{spec}
  _`+_ : (e e' : Regex) → Regex
  ∅ `+ e' = e'
  e `+ ∅  = e
  e `+ e' = e + e'
\end{spec}
In the case of concatenation, we need to deal with the possibilities of each 
parameter being empty (denoting the empty language) or the empty string. If one
of them is empty (|∅|) the result is also empty, and the empty string is the 
identity for concatenation.

\begin{spec}
  _`∙_ : (e e' : Regex) -> Regex
  ∅ `∙ e' = ∅
  Eps `∙ e' = e'
  e `∙ ∅ = ∅
  e `∙ Eps = e
  e `∙ e' = e ∙ e'
\end{spec}
For Kleene star both |∅| and |Eps| are replaced by |Eps|.
\begin{spec}
  _`⋆ : Regex → Regex
  ∅ `⋆ = Eps
  Eps `⋆ = Eps
  e `⋆ = e ⋆
\end{spec}
Since all smart constructors produce equivalent REs, they preserve the
parsing relation. This property is stated below as a soundness and
completeness lemma of each smart constructor with respect to RE
membership proofs.
\begin{Lemma}[Soundness and completeness of union]
For all REs |e|, |e'| and all strings |xs|,
|xs <<-[[ e `+ e' ]] | holds if and only if, |xs <<-[[ e + e' ]] | also holds.
\end{Lemma}
\begin{proof}
  \begin{itemize}
      \item[]
      \item[($\to$)]: By case analysis on the structure of |e| and |e'|. The
  only interesting cases are when one of the expressions is
  |∅|. If |e = ∅|, then |∅ `+ e' = e'| and
  the desired result follows. The same reasoning applies for |e'
  = ∅|.
      \item[($\leftarrow$)]: By case analysis on the structure of |e|, |e'|. The
   only interesting cases are when one of the REs is |∅|.  If
   |e = ∅|, we need to analyse the structure of
   |xs <<-[[ e + e' ]] |. The result follows directly or by
   contradiction using |xs <<-[[ ∅ ]] |. The same reasoning
   applies when |e' = ∅|.
  \end{itemize}          
\end{proof}
\begin{Lemma}[Soundness and completeness of concatenation]
For all REs |e|, |e'| and all strings |xs|,
|xs <<-[[ e `∙ e' ]]| holds if and only if, | xs <<-[[ e ∙ e' ]] |
also holds.
\end{Lemma}
\begin{proof}
    \item[]
    \item[($\to$)]:
  By case analysis on the structure of |e|, |e'|. The
  interesting cases are when |e| or |e'| are equal to
  |Eps| or |∅|. When some of the REs are equal to
  |∅|, the result follows by contradiction. If one of the REs
  are equal to |Eps| the desired result is immediate, from the
  proof term |xs <<-[[ e `∙ e' ]]|, using list concatenation
  properties.
  \item[($\leftarrow$)]:
  By case analysis on the structure of |e|, |e'|. The
  interesting cases are when |e| or |e'| are equal to
  |Eps| or |∅|. When some of the REs are equal to
  |∅|, the result follows by contradiction. If one of the REs
  are equal to |Eps| the desired result is immediate.
\end{proof}  
\begin{Lemma}[Soundness and completeness of Kleene star]
For all REs |e| and string |xs|,
|xs <<-[[  e `⋆ ]]| holds if and only if, |xs <<-[[ e ⋆ ]]| also holds.
\end{Lemma}
\begin{proof}
  Both directions follows by straightforward case analysis on |e|'s structure.
\end{proof}

All definitions of smart constructors and their properties are
contained in \texttt{Smart.agda}, in the project's on-line
repository~\cite{regex-rep}.

\subsection{Brzozowski Derivatives and their Properties}

Intuitively, the derivative $L_a$ of a language $L$ w.r.t. a symbol $a$ is the 
set of strings generated by stripping the leading $a$ from the strings in $L$
that start with $a$. Formally:  
\[
   L_a = \{ w \,\mid\, aw \in L \}
\]
Regular languages are closed under the derivative operation and Janusz Brzozowski defined a
elegant method for computing derivatives for RE in~\cite{Brzozowski1964}. 
Formally, the derivative of a RE $e$ with respect to a symbol $a$, denoted by
$\partial_a(e)$, is defined by recursion on $e$'s structure as
follows:

\[
\begin{array}{lclr}
  \partial_a(\emptyset) & = & \emptyset\\
  \partial_a(\epsilon) & = & \emptyset \\
  \partial_a(b) & = & \left\{
                      \begin{array}{lr}
                        \epsilon & \text{if } b = a\\
                        \emptyset & \text{otherwise}
                      \end{array}
                                \right. \\
  \partial_a(e\:e') & = & \partial_a(e)\,e' + \nu(e)\,\partial_a(e')\\
  \partial_a(e + e') & = & \partial_a(e) + \partial_a(e') \\
  \partial_a(e^\star) & = & \partial_a(e)\,e^\star\\
\end{array}
\]

\begin{Example}
    Consider the RE $e = (aa + b)^\star$. The derivative of $e$ w.r.t. $a$ is $a(aa + b)^\star$, as demonstrated below:
    \begin{align*}
        \partial_a((aa + b)^\star) &= \partial_a(aa + b)\,(aa + b)^\star\\ 
                                   &= \left\lbrack \partial_a (aa) + \partial_a(b)\right\rbrack\,(aa + b)^\star\\
                                   &= \left\lbrack a + \emptyset \right\rbrack\, (aa + b)^\star \\
                                   &= a(aa + b)^\star
    \end{align*}
\end{Example}    


%format ∂[_,_] = "\F{∂[\_,\_]}"
%format ∂[ = "\F{∂[}"
%format =?= = "\F{\overset{?}{=}}"
This function has an immediate translation to Agda. Notice that the
derivative function uses smart constructors to quotient result REs
with respect to the equivalence axioms presented in
Section~\ref{sec:smart} and RE emptiness test. In the symbol case
(constructor |#_|), function |=?=| is used, which
produces an evidence for equality of two |Char| values.
\begin{spec}
  ∂[_,_] : Regex → Char → Regex
  ∂[ ∅ , c ]> = ∅
  ∂[ Eps , c ]> = ∅
  ∂[ # c , c' ]> with c =?= c'
  ...| yes refl = Eps
  ...| no prf = ∅
  ∂[ e ∙ e' , c ]> with nuu[ e ]>
  ∂[ e ∙ e' , c ]> | yes pr = (∂[ e , c ]> `∙ e') `+ ∂[ e' , c ]> 
  ∂[ e ∙ e' , c ]> | no ¬pr = ∂[ e , c ]> `∙ e'
  ∂[ e + e' , c ]> = ∂[ e , c ]> `+ ∂[ e' , c ]>
  ∂[ e ⋆ , c ]> = ∂[ e , c ]> `∙ (e `⋆)
\end{spec}
From this definition we prove the following important properties of
the derivative operation. Soundness of |∂[_,_]| ensures that if a
string |xs| is in the language of |∂[ e , x ]> |, then
|(x :: xs) <<-[[ e ]]| holds. Completeness ensures that the
other direction of implication holds.

\begin{Theorem}[Derivative operation soundness]\label{derivsound}
For all REs |e|, all strings |xs| and all symbols |x|, if
| xs <<-[[ ∂[ e , x ]> ]] | holds then |(x :: xs) <<-[[ e ]] | holds.
\end{Theorem}
\begin{proof}
  By induction on the structure of |e|, using the soundness
  lemmas for smart constructors and decidability of the emptiness
  test.
\end{proof}

\begin{Theorem}[Derivative operation completeness]\label{derivcomplete}
For all REs |e|, all strings |xs| and all symbols |x|, if
|(x :: xs) <<-[[ e ]] | holds then | xs <<-[[ ∂[ e , x ]> ]] | holds.
\end{Theorem}
\begin{proof}
  By induction on the structure of |e| using the completeness
  lemmas for smart constructors and decidability of the emptiness
  test.
\end{proof}

Definitions and properties of Brzozowski derivatives are given in
\texttt{Brzozowski.agda}, in the project's on-line
repository~\cite{regex-rep}.

\subsection{Antimirov's Partial Derivatives and its Properties}

RE derivatives were introduced by Brzozowski to construct a DFA (deterministic
finite automata) from a given RE. Partial derivatives were introduced by
Antimirov as a method to construct a NFA (non-deterministic finite automata).
The main insight of partial derivatives for building NFAs is building a set
of REs which collectively accept the same strings as Brzozowski derivatives.
Algebraic properties of set operations ensures that ACUI equations hold.
Below, we present function $\nabla_a(e)$ which computes the set of partial
derivatives from a given RE |e| and a symbol |a|.

\[
\begin{array}{lclr}
  \nabla_a(\emptyset) & = & \emptyset\\
  \nabla_a(\epsilon) & = & \emptyset \\
  \nabla_a(b) & = & \left\{
                      \begin{array}{lr}
                        \{\epsilon\} & \text{if } b = a\\
                        \emptyset & \text{otherwise}
                      \end{array}
                                \right.\\
  \nabla_a(e\:e') & = & \left \{
                           \begin{array}{lr}
                              \nabla_a(e) \odot e' \cup \nabla_a(e') & \text{if }\nu(e) = \epsilon \\
                              \nabla_a(e) \odot e' & \text{otherwise} \\
                           \end{array} \right . \\
  \nabla_a(e + e') & = & \nabla_a(e) \cup \nabla_a(e') \\
  \nabla_a(e^\star) & = & \nabla_a(e) \odot e^\star\\
\end{array}
\]
Function $\nabla_a(e)$ uses the operator $S \odot e'$ which concatenates RE |e'| at the right of every $e \in S$:

\[
  S \odot e' = \{e ∙ e'\,\mid\, e \in S\}
\]

\begin{Example}
    Consider RE $e = (aa + b)^\star$. The set of partial derivatives of $e$ w.r.t. $a$ is 
    $\{a(aa + b)^\star\}$ as demonstrated below:
    \begin{align*}
        \nabla_a((aa + b)^\star) &= \nabla_a(aa + b) \odot (aa + b)^\star \\
                                 &= \left\lbrack \nabla_a(aa) \cup \nabla_a(b)\right\rbrack \odot (aa + b)^\star \\
                                 &= \left\{\left\lbrack \nabla_a(a) \odot a \cup \emptyset\right\rbrack \right\}\odot (aa + b)^\star \\
                                 &= \left\{\left\lbrack \{\epsilon\} \odot a \cup \emptyset\right\rbrack \right\}\odot (aa + b)^\star \\
                                 &= \{a\} \odot (aa + b)^\star \\
                                 &= \{a(aa + b)^\star\}
    \end{align*}
\end{Example}    

%format _**_ = "\F{\_\odot\_}"
%format ** = "\F{\odot}"
%format naa[ = "\F{\nabla[}"
%format naa[_,_] = "\F{\nabla[\_,\_]}"
%format Regexes = "\D{Regexes}"
Our Agda implementation models sets as lists of regular expressions.
\begin{spec}
  Regexes = List Regex
\end{spec}
The operator that concatenates a RE at the right of every $e \in S$ is defined by induction on $S$:
\begin{spec}
  _**_ : Regexes → Regex → Regexes
  [] ** e = []
  (e' :: es') ** e = (e' ∙ e) :: (es' ** e)
\end{spec}
The definition of a function to compute partial derivatives for a given RE is a direct
translation of mathematical notation to Agda code:
\begin{spec}
  naa[_,_] : Regex → Char → Regexes
  naa[ ∅ , c ]> = []
  naa[ Eps , c ]> = []
  naa[ # x , c ]> with x =?= c
  naa[ # x , .x ]> | yes refl = [ Eps ]
  naa[ # x , c ]> | no p = []
  naa[ e ∙ e' , c ]> with nuu[ e ]>
  naa[ e ∙ e' , c ]> | yes p = (e' ** naa[ e , c ]>) ++ naa[ e' , c ]>
  naa[ e ∙ e' , c ]> | no ¬p = e' ** naa[ e , c ]>
  naa[ e + e' , c ]> = naa[ e , c ]> ++ naa[ e' , c ]>
  naa[ e ⋆ , c ]> = (e ⋆) ** naa[ e , c ]>
\end{spec}

In order to prove relevant properties about partial derivatives, we define a relation that specifies
when a string is accepted by some set of REs.
%format _<<-<[_]]> = "\D{\_\in\langle\langle\_\rangle\rangle}"
%format <<-<[ = "\D{\in\langle\langle}"
%format ]]> = "\D{\rangle\rangle}"
%format Here = "\C{here}"
%format There = "\C{there}"
\begin{spec}
  data _<<-<[_]]> : List Char -> Regexes -> Set where
    Here  : s <<-[[ e ]] -> s <<-<[ e :: es ]]>
    There : s <<-<[ es ]]> -> s <<-<[ e :: es ]]>
\end{spec}
Essentially, a value of type |s <<-<[ S ]]> | indicates that |s| is accepted by some RE
in |S|. The next lemmas on the membership relation |s <<-<[ S ]]> | and list concatenation
are used to prove soundness and completeness of partial derivatives.

\begin{Lemma}[Weakening left]\label{wl}
  For all sets of REs |S|, |S'| and all strings |s|, if |s <<-<[ S ]]> | holds then |s <<-<[ S ++ S' ]]> | holds.
\end{Lemma}
\begin{proof}
  Straightforward induction on the derivation of |s <<-<[ S ]]> |.
\end{proof}

\begin{Lemma}[Weakening right]\label{wr}
  For all sets of REs |S|, |S'| and all strings |s|, if |s <<-<[ S' ]]> | holds then |s <<-<[ S ++ S' ]]> | holds.
\end{Lemma}
\begin{proof}
  Straightforward induction on the derivation of |s <<-<[ S' ]]> |.
\end{proof}

\begin{Lemma}\label{wapp}
For all sets of REs |S|, |S'| and all strings |s|, if |s <<-<[ S ++ S' ]]> | holds then |s <<-<[ S ]]> | or
|s <<-<[ S' ]]> | holds.
\end{Lemma}
\begin{proof}
  Induction on the derivation of |s <<-<[ S ++ S' ]]> | and case analysis on the
  structure of |S| and |S'|.
\end{proof}

\begin{Lemma}\label{wop}
  For all sets of REs |S|, all REs |e| and all strings |s|, |s'|, if |s <<-<[ S ]]>| and |s' <<-[[ e ]] | holds then
  |s ++ s' <<-<[ e ** S ]]> | holds.
\end{Lemma}
\begin{proof}
  Induction on the derivation of |s <<-<[ S ]]>|.
\end{proof}

\begin{Lemma}\label{wopeq}
  For all sets of REs |S|, all REs |e| and all strings |s|, if |s <<-<[ e ** S ]]> | holds then there exist |s₁| and |s₂| such that
  |s == s₁ ++ s₂|, |s₁ <<-<[ S ]]> | and |s₂ <<-[[ e ]]| holds.
\end{Lemma}
\begin{proof}
  Induction on the derivation of |s <<-<[ e ** S ]]> |.
\end{proof}

Using these previous results about |_<<-<[_]]>|, we can enunciate soundness and completeness theorems
of partial derivatives. Let |e| be an arbitrary RE and |a| an arbitrary symbol. Soundness means that if a
string |s| is accepted by some RE in |naa[ e , a ]| then |(a :: s) <<-[[ e ]]|. The completeness theorem shows
that the other direction of the soundness implication also holds.

\begin{Theorem}[Partial derivative operation soundness]
For all symbols |a|, all strings |s| and all REs |e|, if |s <<-<[ naa[ e , a ] ]]> | holds then |(a :: s) <<-[[ e ]]| holds.
\end{Theorem}
\begin{proof}
  Induction on the structure of |e|, using Lemmas \ref{wapp} and \ref{wopeq}.
\end{proof}

\begin{Theorem}[Partial derivative operation completeness]
For all symbols |a|, all strings |s| and all REs |e|, if |(a :: s) <<-[[ e ]]| holds then |s <<-<[ naa[ e , a ] ]]> | holds.
\end{Theorem}
\begin{proof}
  Induction on the structure  of |e|, using Lemmas \ref{wl}, \ref{wr} and \ref{wop}.
\end{proof}

Definitions and properties of Antimirov's partial derivatives are given in
\texttt{Antimirov.agda}, in the project's on-line
repository~\cite{regex-rep}.

\subsection{Parsing}

Assume that we are given an RE $e$ and a string $s$ and we want to 
determine if $s \in e$. We can use RE derivatives for building such a 
test by extending the definition of derivatives to strings as follows~\cite{Owens2009}:
\[
    \begin{array}{lcl}
        \widehat{\partial}_\epsilon(e) & = & e\\
        \widehat{\partial}_{as}(e)     & = & \widehat{\partial}_s(\partial_a(e))
    \end{array}
\]
Note that $s \in e$ if and only if $\epsilon \in \widehat{\partial}_s(e)$, which is true whenever 
$\nu(\widehat{\partial}_s(e)) = \epsilon$. Owens et. al. define a relation between strings and RE, called
the \emph{matching} relation, defined as:
\[
    \begin{array}{lcl}
        e \sim \epsilon & \Leftrightarrow & \nu(e) \\
        e \sim as       & \Leftrightarrow & \partial_a(e) \sim s
    \end{array}
\] 
A simple inductive proof shows that $s \in e$ if and only if $e \sim s$. 

\begin{Example}
    Suppose $e = (aa + b)^\star$ and the string $aab$. We can show that 
    $aab \in e$ using the previously defined matching relation as follows:
    \begin{align*}
        (aa + b)^\star \sim aab & \Leftrightarrow \partial_a (aa + b) (aa + b)^\star \sim ab \\
                                & \Leftrightarrow a(aa + b)^\star \sim ab \\
                                & \Leftrightarrow \partial_a(a(aa + b)^\star) \sim b \\
                                & \Leftrightarrow (aa + b)^\star \sim b \\
                                & \Leftrightarrow \partial_b(aa + b)(aa + b)^\star \sim \epsilon\\
                                & \Leftrightarrow (aa + b)^\star \sim \epsilon \\
                                & \Leftrightarrow \nu((aa + b)^\star) = \epsilon \text{ which is true.}\\ 
    \end{align*}
    
    The same idea can be used to show that a string isn't in the language of some RE. Now consider again
    RE $e = (aa + b)^\star$ and the string $abb$:
    \begin{align*}
        (aa + b)^\star \sim abb & \Leftrightarrow \partial_a (aa + b) (aa + b)^\star \sim bb \\
                                & \Leftrightarrow a(aa + b)^\star \sim bb \\
                                & \Leftrightarrow \partial_b (a(aa+ b)^\star) \sim b \\
                                & \Leftrightarrow \partial_b(a)(aa + b)^\star \sim b \\
                                & \Leftrightarrow \emptyset\,(aa + b)^\star \sim b   \\
                                & \Leftrightarrow \emptyset \sim b                   \\
                                & \Leftrightarrow \partial_b(\emptyset) \sim \epsilon \\
                                & \Leftrightarrow \nu(\emptyset) = \epsilon \text{ which is false.}\\
    \end{align*}    
\end{Example}    

For our purposes, understanding
RE parsing as a matching relation isn't adequate because RE-based text search tools, like GNU-grep, shows
every matching prefix and substring of a RE for a given input.
Since our interest is in determining which prefixes and substrings of the
input string match a given RE, we define datatypes that
represent the fact that a given RE matches a prefix or a substring of
some string.

%format IsPrefix = "\D{IsPrefix}"
%format Prefix = "\C{Prefix}"
%format IsSubstring = "\D{IsSubstring}"
%format Substring = "\C{Substring}"
%format ¬IsPrefix = "\F{¬IsPrefix}"
%format ¬IsPrefix-:: = "\F{¬IsPrefix-::}"
%format ¬IsSubstring = "\F{¬IsSubstring}"
%format ¬IsSubstring-:: = "\F{¬IsSubstring-::}"

We say that RE |e| matches a prefix of string |xs| if there exist
strings |ys| and |zs| such that |xs == ys ++ zs| and |ys <<-[[ e ]]
|. Definition of |IsPrefix| datatype encodes this concept. Datatype
|IsSubstring| specifies when a RE |e| matches a substring in |xs|:
there must exist strings |ys|, |zs| and |ws| such that |xs == ys ++ zs
++ ws| and |zs <<-[[ e ]] | hold. We could represent prefix and substring 
predicates using dependent products, but for code clarity we choose to 
define the types |IsPrefix| and |IsSubstring|.

\begin{spec}
  data IsPrefix (xs : List Char)(e : Regex) : Set where
    Prefix : ∀ (ys zs) -> xs == ys ++ zs -> ys <<-[[ e ]] -> IsPrefix xs e
    
  data IsSubstring (xs : List Char)(e : Regex) : Set where
    Substring :  xs == ys ++ zs ++ ws -> zs <<-[[ e ]] -> IsSubstring xs e
\end{spec}
Using these datatypes we can state and prove the following relevant properties of 
prefixes and substrings. 

\begin{Lemma}[Lemma |¬IsPrefix|]\label{pref1}
  For all REs |e|, if |[] <<-[[ e ]]| does not hold then neither does |IsPrefix [] e|. 
\end{Lemma}
\begin{proof}
  Immediate from the definition of |IsPrefix| and properties of list concatenation.
\end{proof}

\begin{Lemma}[Lemma |¬IsPrefix-::|]\label{pref2}
  For all REs |e| and all strings |xs|, if |[] <<-[[ e ]]| and |IsPrefix xs ∂[ e , x ]> | do not hold then
  neither does |IsPrefix (x :: xs) e|.
\end{Lemma}
\begin{proof}
  Immediate from the definition of |IsPrefix| and Theorem \ref{derivcomplete}.
\end{proof}

\begin{Lemma}[Lemma |¬IsSubstring|]\label{sub1}
  For all REs |e|, if |IsPrefix [] e| does not hold then neither does |IsSubstring [] e|.
\end{Lemma}
\begin{proof}
  Immediate from the definitions of |IsPrefix| and |IsSubstring|.
\end{proof}

\begin{Lemma}[Lemma |¬IsSubstring-::|]
  For all strings |xs|, all symbols |x| and all REs |e|, if |IsPrefix (x :: xs) e| 
  and |IsSubstring xs e| do not hold
  then neither does |IsSubstring (x :: xs) e|.
\end{Lemma}
\begin{proof}
  Immediate from the definitions of |IsPrefix| and |IsSubstring|.
\end{proof}

%format IsPrefixDec = "\F{IsPrefixDec}"
%format ∂-sound = "\F{∂-sound}"
%format cong = "\F{cong}"

Function |IsPrefixDec| decides if a given RE |e| matches a prefix in
|xs| by induction on the structure of |xs|, using Lemmas \ref{pref1},
\ref{pref2}, decidable emptyness test |nuu[_]| and Theorem
\ref{derivsound}. Intuitively, |IsPrefixDec| first checks if current
RE |e| accepts the empty string. In this case, |[]| is returned as a
prefix. Otherwise, it verifies, for each symbol |x|, whether RE |∂[ e , x ]>|
matches a prefix of the input string. If this is the case, a prefix
including |x| is built from a recursive call to |IsPrefixDec| or if no
prefix is matched a proof of such impossibility is constructed using
lemma \ref{pref2}.

\begin{spec}
  IsPrefixDec : ∀ (xs : List Char)(e : Regex) → Dec (IsPrefix xs e)
  IsPrefixDec [] e with nuu[ e ]>
  IsPrefixDec [] e | yes p = yes (Prefix [] [] refl p)
  IsPrefixDec [] e | no ¬p = no (¬IsPrefix ¬p)
  IsPrefixDec (x :: xs) e with nuu[ e ]>
  IsPrefixDec (x :: xs) e | yes p = yes (Prefix [] (x :: xs) refl p)
  IsPrefixDec (x :: xs) e | no ¬p with IsPrefixDec xs (∂[ e , x ])
  IsPrefixDec (x :: xs) e | no ¬p | (yes (Prefix ys zs eq wit))
    = yes (Prefix (x :: ys) zs (cong (_::_ x) eq) (∂-sound _ _ _ wit))
  IsPrefixDec (x :: xs) e | no ¬pn | (no ¬p) = no (¬IsPrefix-:: ¬pn ¬p)
\end{spec}

%format IsSubstringDec = "\F{IsSubstringDec}"

Function |IsSubstringDec| is also defined by induction on the
structure of the input string |xs|, using |IsPrefixDec| to check
whether it is possible to match a prefix of |e|. In this case, a
substring is built from this prefix. If there's no such prefix, a
recursive call is made to check if there is a substring match,
returning such substring or a proof that it does not exist.

\begin{spec}
  IsSubstringDec : ∀ (xs : List Char)(e : Regex) → Dec (IsSubstring xs e)
  IsSubstringDec [] e with nuu[ e ]>
  IsSubstringDec [] e | yes p = yes (Substring [] [] [] refl p)
  IsSubstringDec [] e | no ¬p = no (¬IsSubstring (¬IsPrefix ¬p))
  IsSubstringDec (x :: xs) e with IsPrefixDec (x :: xs) e
  IsSubstringDec (x :: xs) e | yes (Prefix ys zs eq wit)
    = yes (Substring [] ys zs eq wit)
  IsSubstringDec (x :: xs) e | no ¬p with IsSubstringDec xs e
  IsSubstringDec (x :: xs) e | no ¬p | (yes (Substring ys zs ws eq wit))
    = yes (Substring (x :: ys) zs ws (cong (_::_ x) eq) wit)
  IsSubstringDec (x :: xs) e | no ¬p₁ | (no ¬p)
    = no (¬IsSubstring-:: ¬p₁ ¬p)
\end{spec}

Previously defined functions for computing prefixes and substrings use Brzozowski
derivatives. Functions for building prefixes and substrings using Antimirov's
partial derivatives are similar to Brzozowski derivative based ones.
The main differences between them are in the necessary lemmas used to prove
decidability of the prefix and substring relations. Such lemmas are slightly modified
versions of Lemmas \ref{pref1} and \ref{pref2} that consider the relation
|_<<-<[_]]>|  and are omitted for brevity.

Definitions and properties of functions for prefix and substring computation
are given in folders \texttt{Prefix} and \texttt{Substring}, in the project's on-line
repository~\cite{regex-rep}.

\section{Implementation Details and Experiments}\label{sec:exp}

From the formalized algorithm we built a tool for RE parsing in the
style of GNU Grep~\cite{Grep}. We have built a simple parser
combinator library for parsing RE syntax, using the Agda Standard
Library and its support for calling Haskell functions through its
foreign function interface.

Experimentation with our tool, named verigrep, involved a comparison
of its performance with GNU Grep~\cite{Grep} (grep), Google regular
expression library re2~\cite{re2} and Haskell RE parsing algorithms
haskell-regexp, described in~\cite{Fischer2010}. We run RE parsing
experiments on a machine with a Intel Core I7 1.7 GHz, 8GB RAM running
Mac OS X 10.12.3; the results were collected and the median of several
test runs was computed.

We used the same experiments as those used in ~\cite{SulzmannL14};
these consist of parsing files containing thousands of occurrences of
symbol \texttt{a}, using the RE $(a + b + ab)^\star$, and parsing
files containing thousands of occurrences of \texttt{ab}, using the
same RE. Results are presented in Figures~\ref{fig:graph1}
and~\ref{fig:graph2}, respectively.

\begin{figure}[!ht]
    \includegraphics[width=0.7\textwidth]{as.png}
   \centering
   \caption{Results of experiment 1.}
   \label{fig:graph1}
\end{figure}

\begin{figure}[!ht]
    \includegraphics[width=0.7\textwidth]{abs.png}
   \centering
   \caption{Results of experiment 2.}
   \label{fig:graph2}
\end{figure}

Our tool behaves poorly when compared with all other options
considered. The cause of this inefficiency needs further
investigation, but we envisaged that it can be due to the
following: 1) Our algorithm relies on the Brzozowski's definition for RE
parsing, which needs to quotient resulting REs. 2) We use lists to
represent sets of Antimirov's partial derivatives. We believe that
usage of better data structures to represent sets and using
appropriate disambiguation strategies like greedy
parsing~\cite{FrischC04} and POSIX~\cite{SulzmannL14} would be able to
improve the efficiency of our algorithm without sacrificing
correctness. We leave the formalization of disambiguation strategies
and the use of more efficient data structures for future work.

\section{Related Work}\label{sec:related}

\paragraph{Parsing with derivatives} Recently, derivative-based
parsing has received a lot of attention. Owens et al. were the first
to present a functional encoding of RE derivatives and use it to
parsing and DFA building. They use derivatives to build scanner
generators for ML and Scheme~\cite{Owens2009}; no formal proof of
correctness was presented.

Might et al.~\cite{Might2011} report on
the use of derivatives for parsing not only RLs but also context-free
ones. He uses derivatives to handle context-free grammars (CFG) and
develops an equational theory for compaction that allows for efficient
CFG parsing using derivatives. Implementation of derivatives for CFGs
are described by using the Racket programming
language~\cite{Felleisen2013}. However, Might et al. do not present
formal proofs related to the use of derivatives for CFGs.

Fischer et al.~describe an algorithm for RE-based parsing based on
weighted automata in Haskell~\cite{Fischer2010}.  The paper describes
the design evolution of such algorithm as a dialog between three
persons. Their implementation has a competitive performance when
compared with Google's RE library~\cite{re2}. This work also does not
consider formal proofs of RE parsing.

An algorithm for POSIX RE parsing is described
in~\cite{SulzmannL14}. The main idea of the article is to adapt
derivative parsing to construct parse trees incrementally to solve
both matching and submatching for REs. In order to improve the
efficiency of the proposed algorithm, Sulzmann et al. use a bit
encoded representation of RE parse trees. Textual proofs of
correctness of the proposed algorithm are presented in an appendix.

\paragraph{Certified parsing algorithms} Certified algorithms for
parsing also received attention recently. Firsov et al.~describe a
certified algorithm for RE parsing by converting an input RE to an
equivalent NFA represented as a boolean matrix~\cite{FirsovU13}. A
matrix library based on some ``block'' operations~\cite{MacedoO13} is
developed and used Agda formalization of NFA-based parsing
~\cite{Norell2009}. Compared to our work, a NFA-based formalization requires
much more infrastructure (such as a Matrix library). No experiments
with the certified algorithm were reported.

Firsov describes an Agda formalization of a parsing algorithm that
deals with any CFG (CYK algorithm)~\cite{Firsov2014}. Bernardy
et al.~describe a formalization of another CFG parsing algorithm in
Agda~\cite{BernardyJ16}: Valiant's algorithm~\cite{Valiant1975}, which
reduces a CFG parsing problem to boolean matrix multiplication. In both works,
no experiment with formalized parsing algorithms were reported.

A certified LR(1) CFG validator is described
in~\cite{Jourdan2012}. The formalized checking procedure verifies if
a CFG and an automaton match. They proved soundness and completeness of
the validator in the Coq proof
assistant~\cite{Bertot2010}. Termination of the LR(1) automaton
interpreter is ensured by imposing a natural number bound on
allowed recursive calls.

Formalization of a parser combinator library was the subject of
Danielsson's work~\cite{Danielsson2010}. He built a library of parser
combinators using coinduction and provide correctness proofs of such
combinators.

Almeida et al.~\cite{AlmeidaMPS10} describe a Coq formalization of
partial derivatives and its equivalence with automata. Partial
derivatives were introduced by Antimirov~\cite{Antimirov91} as an
alternative to Brzozowski derivatives, since it avoids quotient
resulting REs with respect to ACUI axioms. Almeida et al. motivation
is to use such formalization as a basis for a decision procedure for
RE equivalence.

Ridge~\cite{Ridge2011} describes a formalization, in the HOL4 theorem
prover, of a combinator parsing library. A parser generator for such
combinators is described and a proof that generated parsers are sound
and complete is presented.  According to Ridge, preliminary results
show that parsers built using his generator are faster than those
created by the Happy parser generator~\cite{Happy}.

Ausaf et. al.~\cite{AusafDU16} describe a formalization, in
Isabelle/HOL~\cite{Nipkow02}, of the POSIX matching algorithm proposed
by Sulzmann et.al.~\cite{SulzmannL14}. They give a constructive
characterization of what a POSIX matching is and prove that such
matching is unique for a given RE and string. No experiments with the
verified algorithm are reported.


\section{Conclusion}\label{sec:conclusion}

We gave a complete formalization of a derivative-based parsing
for REs in Agda. To the best of our knowledge, this is the first work
that presents a complete certification and that uses the certified
program to build a tool for RE-based search.

The developed formalization has 1145 lines of code, organized in 20
modules. We have proven 39 theorems and lemmas to complete the
development. Most of them are immediate pattern matching functions
over inductive datatypes and were omitted from this text for brevity.

As future work, we intend to work on the development of a certified
program of greedy and POSIX RE parsing using Brzozowski
derivatives~\cite{SulzmannL14,FrischC04} and investigate ways to
obtain a formalized but simple and efficient RE parsing tool.

\paragraph{Acknowledgements:} We would like to thank the reviewers 
for their insightful comments on the paper, as these comments led us 
to an improvement of the work. The first author thanks CAPES for financial
support. Second author thanks Fundação de Amparo a
Pesquisa de Minas Gerais (FAPEMIG) for financial support.

\section*{References}

\bibliography{main}

\end{document}
