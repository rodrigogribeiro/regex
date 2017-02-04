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
\usepackage{ifpdf}
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
\address[rgr]{Dep. de Computa\c{c}\~ao e Sistemas, Universidade
  Federal de Ouro Preto, ICEA, Jo\~ao Monlevade, Minas Gerais, Brasil}
\ead[rgr]{rodrigo@@decsi.ufop.br}  

\author{Raul Lopes}
\address{Dep. de Computa\c{c}\~ao, Universidade
  Federal de Ouro Preto, ICEB, Campus Universit\'ario Morro do
  Cruzeiro, Ouro Preto, Minas Gerais, Brasil}
\ead{raulfpl@@gmail.com}


\author{Carlos Camar\~ao}
\address{Dep. de Ci\^encia da Computa\c{c}\~ao, Universidade Federal
  de Minas Gerais, Av. Ant\^onio Carlos 6627, Belo Horizonte, Minas Gerais, Brasil}
\ead{camarao@@dcc.ufmg.br}


\begin{abstract}

We describe the formalization of a certified algorithms for regular
expression parsing based on Brzozowski and Antimirov derivatives,
in the dependently typed language Agda. The formalized algorithms
produces proofs that an input string matches a given regular expression
or a proof that no matching exists. A tool for regular expression based
search in the style of the well known GNU grep has been developed with
the certified algorithms, and practical experiments were conducted
with it.

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
given rules, involving also, in computer science, formally specifying
the rules in a grammar and also, either the construction of data that
makes evident the rules that have been used to conclude that the
string of symbols can be obtained from the grammar rules, or else
indication of an error, representative of the fact that the string of
symbols cannot be generated from the grammar rules.

In this work, we are interested in the parsing problem for regular
languages (RLs)~\cite{Hopcroft2000}, i.e. languages recognized by
(non-)deterministic finite automata and equivalent formalisms. Regular
expressions (REs) are an algebraic and compact way of specifying RLs
that are extensively used in lexical analyser
generators~\cite{Lesk1990} and string search utilities~\cite{Grep}.
Since such tools are widely used and parsing is pervasive in
computing, there is a growing interest on correct parsing
algorithms~\cite{FirsovU13,FirsovU14,Danielsson2010}.  This interest
is motivated by the recent development of dependently typed
languages. Such languages are powerful enough to express algorithmic
properties as types, that are automatically checked by a compiler.

The use of derivatives for regular expressions were introduced by
Brzozowski~\cite{Brzozowski1964} as an alternative method to compute a
finite state machine that is equivalent to a given RE and to perform
RE-based parsing. According to Owens et. al~\cite{Owens2009},
``derivatives have been lost in the sands of time'' until his work on
functional encoding of RE derivatives have renewed interest on its use
for parsing~\cite{Might2011,Fischer2010}.
In this work, we provide a complete formalization of an algorithm for
RE parsing using derivatives, as presented by~\cite{Owens2009}, and
describe a RE based search tool that has been developed by us, using
the dependently typed language Agda~\cite{Norell2009}.

More specifically, our contributions are:
\begin{itemize}
  \item A formalization of Brzozowski derivatives based RE
    parsing in Agda. The certified algorithm presented produces as
    a result either a proof term (parse tree) that is evidence that
    the input string is in the language of the input RE, or a witness
    that such parse tree does not exist.

  \item A detailed explanation of the technique used to quotient
    derivatives with respect to ACUI axioms\footnote{Associativity,
      Commutativity and Idempotence with Unit elements axioms for
      REs~\cite{Brzozowski1964}.} in an implementation by Owens et
    al.~\cite{Owens2009}, called ``smart-constructors'', and its proof
    of correctness. We give formal proofs that smart constructors
    indeed preserve the language recognized by REs.

  \item A formalization of Antimirov's derivatives and its use to
      construct a RE parsing algorithm. The main difference between
      partial derivatives and Brzozowski's is that the former computes
      a set of RE's using set operators instead of ``smart-constructors''.
      Producing a set of RE's avoids the need of quotienting the resulting
      REs w.r.t. ACUI axioms.  
\end{itemize}

This paper extends our SBLP 2016 paper~\cite{Lopes2016} by formalizing
a RE parsing algorithm using Antimirov's partial derivatives~\cite{Antimirov1996}.
Also our original paper uses Idris~\cite{Brady2013} instead of Agda. This change
was motivated by a modification in Idris totality checker that refuses some
(correct and total) proofs that are both accepted by Agda's and Coq totality
checkers. All source code produced in Idris, Agda and Coq, including the \LaTeX~
source of this article, instructions on how to build and use it are avaliable
on-line~\cite{regex-rep}.

The rest of this paper is organized as
follows. Section~\ref{sec:agda} presents a brief introduction to
Agda. Section~\ref{sec:regexp} describes the encoding of REs and its
parse trees. In Section~\ref{sec:deriv} we define Brzozowski and Antimirov
derivatives and smart constructors, some of their properties and describe
how to build a correct parsing algorithm from them. Section~\ref{sec:exp}
comments on the usage of the certified algorithm to build a tool for RE-based
search and present some experiments with it. Related work is discussed
on Section~\ref{sec:related}. Section~\ref{sec:conclusion} concludes.

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

Agda is dependently-typed functional programming language based on Martin-L\"oef
intuitionistic type theory~\cite{Lof98}. This means, in particular, that it has
very few built-in types. In fact, only function types and the type of all types
are built-in. Everything else is a user-defined type. The type |Set|, also known
as |Set0|, is the type of all ``small'' types, such as |Bool|, |String| and |List Bool|.
The type |Set1| is the type of |Set| and ``others like it'', such as |Set -> Bool|,
|String -> Set|, and |Set -> Set|. There is in fact an infinite hierarchy of types of the
form |Set l|, where |l| is a level, roughly, a natural integer. This stratification
of types is need to keep Agda consistent as a logical theory~\cite{Sorensen2006}.

An ordinary (non-dependent) function type is written |A -> B| and a dependent one is written
|(x : A) -> B| or |∀ (x : A) -> B|. Agda allows the definition of \emph{implicit parameters}, i.e.
parameters whose value can be infered from the context, by surrounding them in curly
braces: |∀ {x : A} -> B|. To avoid clutter, we'll omit implicit arguments from the source code
presentation. The reader can safely assume that every free variable in a type is an implicity
parameter.

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
%format head = "\F{head}"
Constructor |[]| builds empty vectors. The cons-operator (|_::_|)
inserts a new element in front of a vector of $n$ elements (of type
|Vec A n| and returns a value of type |Vec A (succ n)|. The
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
types as logical formulas and terms as proofs. An example is the
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

This type is called propositional equality. It defines that there is
a unique evidence for equality, constructor |refl| (for reflexivity),
that asserts that the only value equal to |x| is itself. Given a type |P|,
type |Dec P| is used to build proofs that |P| is a
decidable proposition, i.e.~that either |P| or not |P|
holds. The decidable proposition type is defined as:
\begin{spec}
  data Dec (P : Set) : Set where
     yes : P -> Dec P
     no  : not P -> Dec p
\end{spec}
Constructor |yes| stores a proof that property |P| holds
and |no| an evidence that such proof is impossible. Some functions
used in our formalization use this type.

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
   Even : Parity (n + n)
   Odd  : Parity (S (n + n))

parity : (n : Nat) -> Parity n
parity = -- definition omitted

natToBin : Nat -> List Bool
natToBin zero = []
natToBin k with (parity k)
   natToBin (j + j)     | Even = false :: natToBin j
   natToBin (succ (j + j)) | Odd  = true  :: natToBin j
\end{spec}

A detailed discussion about the Agda language is out of the scope of
this paper. A tutorial on Agda is avaliable~\cite{Norell2009}.


\section{Regular Expressions}\label{sec:regexp}


%format Char = "\D{Char}"

Regular expressions are defined with respect to a given
alphabet. Formally, RE syntax follows the following context-free
grammar
\[
e ::= \emptyset\,\mid\,\epsilon\,\mid\,a\,\mid\,e\,e\,\mid\,e+e\,\mid\,e^{\star}
\]
where $a$ is a symbol from the underlying alphabet.
In our original Idris formalization, we describe symbols of an alphabet as a natural number
in Peano notation (type |Nat|), i.e.~the symbol's numeric
code. The reason for this design choice is due to the way that Idris
deals with propositional equality for primitive types, like
|Char|. Equalities of values of these types only reduce on
concrete primitive values; this causes computation of proofs to stop
under variables whose type is a primitive one. Thus, we decide to use
the inductive type |Nat| to represent the codes of alphabet
symbols. In our Agda formalization, we represent alphabet symbols using |Char| type.

%format Regex = "\D{Regex}"
%format Eps = "\C{\epsilon}"
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
empty language ($\emptyset$) and empty string ($\epsilon$). Alphabet
symbols are constructed using |#| constructor. Bigger REs are
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


Using the datatype for RE syntax, we can define a relation for RL
membership. Such relation can be understood as a parse tree (or a
proof term) that a string, represented by a list of |Char|
values, belongs to the language of a given
RE.

The following datatype defines RE semantics inductively, i.e.,
each of its constructor specifies how to build a parse tree
for some string and RE.

\begin{spec}
  data _<<-[[_]] : List Char -> Regex -> Set where
    Eps : [] <<-[[ Eps ]]
    #_  : (c : Char) -> # c <<-[[ # c ]]
    _∙_=>_ : xs <<-[[ l ]]  -> ys <<-[[ r ]]  -> zs == xs ++ ys -> zs <<-[[ l ∙ r ]]
    _+L_ : (r : Regex) -> xs <<-[[ l ]] -> xs <<-[[ l + r ]]
    _+R_ : (l : Regex) -> xs <<-[[ r ]] -> xs <<-[[ l + r ]]
    _⋆ : xs <<-[[ Eps + (e ∙ e ⋆) ]] -> xs <<-[[ e ⋆ ]]
\end{spec}

Constructor |Eps| states that the empty string (denoted by the empty list |[]|)
is in the language of RE |Eps|. Parse tree for single characters are built
with |# a|, which says that the singleton string
|[ a ]| is in RL for |# a|. Given parse trees for REs
|l| and |r|; | xs <<-[[ l ]] | and | ys <<-[[ r ]] |, we can use constructor
| _∙_=>_ | to build a parse tree for the concatenation of these REs. 
Constructor |_+L_| 
(|_+R_|) creates a parse tree for |l + r| from a parse
tree from |l|(|r|). Parse trees for Kleene star are built
using the following well known equivalence of REs: $e^\star = \epsilon
+ e\,e^\star$.

Several inversion lemmas about RE parsing relation are necessary to
formalize derivative based parsing. They consist of pattern-matching
on proofs of |_<<-[[_]]| and are omitted for brevity.


\section{Derivatives, Smart Constructors and Parsing}\label{sec:deriv}

Formally, the derivative of a formal language $L\subseteq
\Sigma^\star$ with respect to a symbol $a\in\Sigma$ is the language
formed by suffixes of $L$ words without the prefix $a$.

An algorithm for computing the derivative of a language represented as
a RE as another RE is due to Brzozowski~\cite{Brzozowski1964} and it
relies on a function (called $\nu$) that determines if some RE accepts
or not the empty string:
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
%format ∈+-invert = "\F{∈+-invert}"
%format []∈∙-invert = "\F{[]∈∙-invert}"
Decidability of $\nu(e)$ is proved by function |nuu[ e ]|,
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
  nuu[ e ∙ e' ]> | yes pr | (no ¬pr1) = no (¬pr1 ∘ proj₂ ∘ []∈∙-invert)
  nuu[ e ∙ e' ]> | no ¬pr | pr1 = no (¬pr ∘ proj₁ ∘ []∈∙-invert)
  nuu[ e + e' ]> with nuu[ e ]> | nuu[ e' ]>
  nuu[ e + e' ]> | yes pr | pr1 = yes (e' +L pr)
  nuu[ e + e' ]> | no ¬pr | (yes pr1) = yes (e +R pr1)
  nuu[ e + e' ]> | no ¬pr | (no ¬pr1) = no ( [ ¬pr , ¬pr1 ] ∘ ∈+-invert)
  nuu[ e ⋆ ]> = yes ((e ∙ e ⋆ +L Eps) ⋆) 
\end{spec}
The |nuu[_]| definition uses several inversion lemmas about
RE semantics. Lemma |[]∈∙-invert| states that if the empty string
is in the language of |l ∙ r| (where |l| and |r| are arbitrary RE's)
then the empty string belongs to |l| and |r|'s languages.
Lemma |∈+-invert| is defined similarly for union.

\subsection{Smart Constructors}\label{sec:smart}

In order to define Brzozowski derivatives, we follow Owens et. al.~\cite{Owens2009}, we use
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
while building REs. For union, we just need to worry when one
parameter denotes the empty language RE (|∅|):
\begin{spec}
  _`+_ : (e e' : Regex) → Regex
  ∅ `+ e' = e'
  e `+ ∅  = e
  e `+ e' = e + e'
\end{spec}
In concatenation, we need to deal with the possibility of
parameters being the empty RE or the empty string RE. If one is the
empty language (∅) the result is also the empty
language. Since empty string RE is identity for concatenation, we
return, as a result, the other parameter.
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
parsing relation. This property is stated as a soundness and
completeness lemma, stated below, of each smart constructor with
respect to RE membership proofs.

\begin{Lemma}[Soundness of union]
For all REs |e|, |e'| and all strings |xs|, if
|xs <<-[[ e `+ e' ]] | holds then |xs <<-[[ e + e' ]] | also holds.
\end{Lemma}
\begin{proof}
  By case analysis on the structure of |e| and |e'|. The
  only interesting cases are when one of the expressions is
  |∅|. If |e = ∅|, then |∅ `+ e' = e'| and
  the desired result follows. The same reasoning applies for |e'
  = ∅|.
\end{proof}
\begin{Lemma}[Completeness of union]
For all REs |e|, |e'| and all strings |xs|, if
|xs <<-[[ e + e' ]] | holds then |xs <<-[[ e `+ e' ]] | also holds.
\end{Lemma}
\begin{proof}
   By case analysis on the structure of |e|, |e'|. The
   only interesting cases are when one of the REs is |∅|.  If
   |e = ∅|, we need to analyse the structure of
   |xs <<-[[ e + e' ]] |. The result follows directly or by
   contradiction using |xs <<-[[ ∅ ]] |. The same reasoning
   applies when |e' = ∅|.
\end{proof}
\begin{Lemma}[Soundness of concatenation]
For all REs |e|, |e'| and all strings |xs|, if
|xs <<-[[ e `∙ e' ]] | holds then | xs <<-[[ e ∙ e' ]] |
also holds.
\end{Lemma}
\begin{proof}
  By case analysis on the structure of |e|, |e'|. The
  interesting cases are when |e| or |e'| are equal to
  |Eps| or |∅|. When some of the REs are equal to
  |∅|, the result follows by contradiction. If one of the REs
  are equal to |Eps| the desired result is immediate, from the
  proof term |xs <<-[[ e `∙ e' ]] |, using list concatenation
  properties.
\end{proof}
\begin{Lemma}[Completeness of concatenation]
For all REs |e|, |e'| and all strings |xs|, if
| xs <<-[[ e ∙ e' ]] | holds then | xs <<-[[ e `∙ e' ]] | also holds.
\end{Lemma}
\begin{proof}
  By case analysis on the structure of |e|, |e'|. The
  interesting cases are when |e| or |e'| are equal to
  |Eps| or |∅|. When some of the REs are equal to
  |∅|, the result follows by contradiction. If one of the REs
  are equal to |Eps| the desired result is immediate.
\end{proof}  
\begin{Lemma}[Soundness of Kleene star]
For all REs |e| and string |xs|, if
|xs <<-[[  e `⋆ ]] | then |xs <<-[[ e ⋆ ]] |.
\end{Lemma}
\begin{proof}
  Straightforward case analysis on |e|'s structure.
\end{proof}
\begin{Lemma}[Completeness of Klenne star]
For all REs |e| and all strings |xs|, if |xs <<-[[ e ⋆ ]] |
holds then |xs <<-[[  e `⋆ ]] | also holds.
\end{Lemma}
\begin{proof}
  Straightforward case analysis on |e|'s structure.
\end{proof}

All definitions of smart constructors and their properties are
contained in \texttt{Smart.agda}, in the project's on-line
repository~\cite{regex-rep}.

\subsection{Brzozowski Derivatives and its Properties}

The derivative of a RE with respect to a symbol $a$, denoted by
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
derivative operation. Soundness of |∂[_,_]| ensures that if a
string |xs| is in |∂[ e , x ]> |'s language, then
|(x :: xs) <<-[[ e ]]| holds. Completeness ensures that the
other direction of implication holds.

\begin{Theorem}[Soundness of derivative operation]\label{derivsound}
For all RE |e|, string |xs| and symbol |x|, if
| xs <<-[[ ∂[ e , x ]> ]] | then |(x :: xs) <<-[[ e ]] | holds.
\end{Theorem}
\begin{proof}
  By induction on the structure of |e|, using the soundness
  lemmas for smart constructors and decidability of the emptiness
  test.
\end{proof}

\begin{Theorem}[Completeness of derivative operation]\label{derivcomplete}
For all RE |e|, string |xs| and symbol |x|, if
|(x :: xs) <<-[[ e ]] | then | xs <<-[[ ∂[ e , x ]> ]] |.
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
The main insight of partial derivatives for building NFA's is building a set
of RE's which, collectively accepts the same strings as Brzozowski derivatives.
Algebraic properties of set operations ensures that ACUI equations holds.
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
                              \partial_a(e) \odot e' \cup \partial_a(e') & \text{if }\nu(e) = \epsilon \\
                              \partial_a(e) \odot e' & \text{otherwise} \\
                           \end{array} \right . \\
  \nabla_a(e + e') & = & \nabla_a(e) \cup \nabla_a(e') \\
  \nabla_a(e^\star) & = & \nabla_a(e) \odot e^\star\\
\end{array}
\]

Function $\nabla_a(e)$ uses the operator $S \odot e'$ which concatenates RE |e'| at right of every $e \in S$:

\[
  S \odot e' = \{e ∙ e'\,\mid\, e \in S\}
\]
%format _**_ = "\F{\_\odot\_}"
%format ** = "\F{\odot}"
%format naa[ = "\F{\nabla[}"
%format naa[_,_] = "\F{\nabla[\_,\_]}"
%format Regexes = "\D{Regexes}"
Our agda implementation models sets as lists of regular expressions.
\begin{spec}
  Regexes = List Regex
\end{spec}
The operator that concatenates a RE at right of every $e \in S$ is defined by induction on $S$:
\begin{spec}
  _**_ : Regex → Regexes → Regexes
  e ** [] = []
  e ** (e' :: es) = (e' ∙ e) :: (e ** es)
\end{spec}
Definition of a function to compute partial derivatives for a given RE is defined as a direct
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

In order to prove relevant properties about partial derivatives, we define a relation that stablish
when a string is accepted by some set of RE's.
%format _<<-<[_]]> = "\D{\_\in\{\_\}}"
%format <<-<[ = "\D{\in\{}"
%format ]]> = "\D{\}}"
%format Here = "\C{here}"
%format There = "\C{there}"
\begin{spec}
  data _<<-<[_]]> : List Char -> Regexes -> Set where
    Here  : s <<-[[ e ]] -> s <<-<[ e :: es ]]>
    There : s <<-<[ es ]]> -> s <<-<[ e :: es ]]>
\end{spec}
Essentially, a value of type |s <<-<[ S ]]> | represents that |s| is accepted by some RE
in |S|. The next lemmas present the relation of |s <<-<[ S ]]> | and list concatenation.

\begin{Lemma}[Weakening left]\label{wl}
  For all sets of RE's |S|, |S'| and string |s|, if |s <<-<[ S ]]> | then |s <<-<[ S ++ S' ]]> |.
\end{Lemma}
\begin{proof}
  Straightforward induction on the derivation of |s <<-<[ S ]]> |.
\end{proof}

\begin{Lemma}[Weakening right]\label{wr}
  For all sets of RE's |S|, |S'| and string |s|, if |s <<-<[ S' ]]> | then |s <<-<[ S ++ S' ]]> |.
\end{Lemma}
\begin{proof}
  Straightforward induction on the derivation of |s <<-<[ S' ]]> |.
\end{proof}

\begin{Lemma}\label{wapp}
For all sets of RE's |S|, |S'| and string |s|, if |s <<-<[ S ++ S' ]]> | then |s <<-<[ S ]]> | or
|s <<-<[ S' ]]> |.
\end{Lemma}
\begin{proof}
  Induction on the derivation of |s <<-<[ S ++ S' ]]> | and case analysis on the
  structure of |S| and |S'|.
\end{proof}

\begin{Lemma}\label{wop}
  For all set of RE's |S|, RE |e| and strings |s|, |s'|; if |s <<-<[ S ]]>| and |s' <<-[[ e ]] | then
  |s ++ s' <<-<[ e ** S ]]> |.
\end{Lemma}
\begin{proof}
  Induction on the derivation of |s <<-<[ S ]]>|.
\end{proof}

\begin{Lemma}\label{wopeq}
  For all set of RE's |S|, RE |e| and string |s|, if |s <<-<[ e ** S ]]> | then exists |s₁| and |s₂| s.t.
  |s == s₁ ++ s₂|, |s₁ <<-<[ S ]]> | and |s₂ <<-[[ e ]]|.
\end{Lemma}
\begin{proof}
  Induction on the derivation of |s <<-<[ e ** S ]]> |.
\end{proof}

Using these previous results about |_<<-<[_]]>|, we can enunciate the soundness and completeness theorems
of partial derivatives. Let |e| be an arbitrary RE and |a| an arbitrary symbol. Soundness means that if a
string |s| is accepted by some RE in |naa[ e , a ]| then |(a :: s) <<-[[ e ]]|. Completeness theorems shows
that the other direction of the soundness implication also holds.

\begin{Theorem}[Soundness of partial derivative operation]
For all symbol |a|, string |s| and RE |e|, if |s <<-<[ naa[ e , a ] ]]> | then |(a :: s) <<-[[ e ]]|.
\end{Theorem}
\begin{proof}
  Induction on |e|'s structure using Lemmas \ref{wapp} and \ref{wopeq}.
\end{proof}

\begin{Theorem}[Completeness of partial derivative operation]
For all symbol |a|, string |s| and RE |e|, if |(a :: s) <<-[[ e ]]| then |s <<-<[ naa[ e , a ] ]]> |.
\end{Theorem}
\begin{proof}
  Induction on |e|'s structure using Lemmas \ref{wl}, \ref{wr} and \ref{wop}.
\end{proof}

Definitions and properties of Antimirov's partial derivatives are given in
\texttt{Antimirov.agda}, in the project's on-line
repository~\cite{regex-rep}.

\subsection{Parsing}

When parsing a string using a given RE we are interested in discover what parts of
input string are matched. Basically, RE parsing involves determine what prefixes and
substring's of input match a given RE. For this, we define datatypes for representing
when a RE |e| matches a prefix or a substring of |xs|.

%format IsPrefix = "\D{IsPrefix}"
%format Prefix = "\C{Prefix}"
%format IsSubstring = "\D{IsSubstring}"
%format Substring = "\C{Substring}"
%format ¬IsPrefix = "\F{¬IsPrefix}"
%format ¬IsPrefix-:: = "\F{¬IsPrefix-::}"
%format ¬IsSubstring = "\F{¬IsSubstring}"
%format ¬IsSubstring-:: = "\F{¬IsSubstring-::}"

We say that RE |e| matches a prefix of string |xs| if there's exists strings |ys| and
|zs| s.t. |xs == ys ++ zs| and |ys <<-[[ e ]] |. Definition of |IsPrefix| datatype encode
this concept. Datatype |IsSubstring| specifies when a RE |e| matches a substring in |xs|,
i.e. there's must exists strings |ys|, |zs| and |ws| s.t. |xs == ys ++ zs ++ ws| and
|zs <<-[[ e ]] |.

\begin{spec}
  data IsPrefix (xs : List Char)(e : Regex) : Set where
    Prefix : ∀ (ys zs) -> xs == ys ++ zs -> ys <<-[[ e ]] -> IsPrefix xs e
    
  data IsSubstring (xs : List Char)(e : Regex) : Set where
    Substring :  xs == ys ++ zs ++ ws -> zs <<-[[ e ]] -> IsSubstring xs e
\end{spec}
Using these datatypes we can define some relevant properties of prefixes and substrings that
are used in certified functions to compute them.

\begin{Lemma}[Lemma |¬IsPrefix|]\label{pref1}
  For all RE |e|, if |[] <<-[[ e ]]| is false then |IsPrefix [] e| is false. 
\end{Lemma}
\begin{proof}
  Immediate from |IsPrefix| definition and properties of list concatenation.
\end{proof}

\begin{Lemma}[Lemma |¬IsPrefix-::|]\label{pref2}
  For all RE |e| and string |xs|, if |[] <<-[[ e ]]| is false and |IsPrefix xs ∂[ e , x ]> | is false then
  |IsPrefix (x :: xs) e| is false.
\end{Lemma}
\begin{proof}
  Immediate from |IsPrefix| definition and Theorem \ref{derivcomplete}.
\end{proof}

\begin{Lemma}[Lemma |¬IsSubstring|]\label{sub1}
  For all RE |e|, if |IsPrefix [] e| is false then |IsSubstring [] e| is false.
\end{Lemma}
\begin{proof}
  Immediate from |IsPrefix| and |IsSubstring| definitions.
\end{proof}

\begin{Lemma}[Lemma |¬IsSubstring-::|]
  For all strings |xs|, symbol |x| and RE |e|, if |IsPrefix (x :: xs) e| is false
  and |IsSubstring xs e| is false
  then |IsSubstring (x :: xs) e| is false.
\end{Lemma}
\begin{proof}
  Immediate from |IsPrefix| and |IsSubstring| definitions.
\end{proof}

%format IsPrefixDec = "\F{IsPrefixDec}"
%format ∂-sound = "\F{∂-sound}"
%format cong = "\F{cong}"

Function |IsPrefixDec| decides if a given RE |e| matches a prefix in |xs| by
induction on |xs| structure using Lemmas \ref{pref1}, \ref{pref2}, decidable emptyness test |nuu[_]|
and Theorem \ref{derivsound}. Intuitively, |IsPrefixDec| first checks if current RE |e| accepts the
empty string. In this case, |[]| is returned as a prefix. Otherwise, it verifies for each symbol |x|
if RE |∂[ e , x ]>| matches a prefix of the input string. If it is the case, a prefix including |x| is
built from a recursive call to |IsPrefixDec| or if no prefix is matched a proof of such impossibility
is constructed using lemma |¬IsPrefix-::|. 

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

Function |IsSubstringDec| is also defined by induction on input strings structure using
|IsPrefixDec| to check if it is possible to match a prefix of input using |e|. In this case,
a substring is built from this prefix. If there's no such prefix, a recursive call is made to
check if there's a substring match, returning such substring or a proof that it does not exist.

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
decidability of prefix and substring relation. Such lemmas are slighly modified
versions of Lemmas \ref{pref1} and \ref{pref2} that consider the relation
|_<<-<[_]]>|  and are omitted for brevity.

Definitions and properties of functions for prefix and substring computation
are given in folders \texttt{Prefix} and \texttt{Substring}, in the project's on-line
repository~\cite{regex-rep}.

\section{Implementation Details and Experiments}\label{sec:exp}

From the algorithm formalized we built a tool for RE parsing in the
style of GNU Grep~\cite{Grep}. We have built a simple parser combinator
library, for parsing RE syntax and use Agda Standard Library and its
support for calling Haskell functions throught foreign function interface.

In order to validade our tool (named verigrep --- for verified Grep), we
compare its performance with GNU Grep~\cite{Grep} (grep), Google
regular expression library~\cite{re2} (re2) and with Haskell RE
parsing algorithms described in~\cite{Fischer2010} (haskell-regexp).
We run RE parsing experiments on a machine with a Intel Core I7 1.7
GHz, 8GB RAM running Mac OS X 10.12.3; the results were collected and
the median of several test runs was computed.

We use the same experiments as~\cite{SulzmannL14} using files formed
by thousands of occurrences of
symbol \texttt{a} were parsed, using the RE $(a + b + ab)^\star$; in
the second, files with thousands of occurrences of \texttt{ab} were
parsed using the same RE. Results are presented in
Figures~\ref{fig:graph1} and~\ref{fig:graph2}, respectively.

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
considered. This inefficiency could be explained: 1) Our algorithm
relies on the Brzozowski definition of RE parsing, which needs to
quotient resulting REs. 2) We use lists to represent sets of Antimirov's
partial derivatives. We believe that usage of better data structures
to represent sets and using appropriate disambiguation strategies
like greedy parsing~\cite{FrischC04} and POSIX~\cite{SulzmannL14}
would be able to improve the efficiency of our algorithm without
sacrificing its correctness. We leave the formalization of
disambiguation strategies and the use of more efficient
data structures for future work.

\section{Related Work}\label{sec:related}

\paragraph{Parsing with derivatives}: recently, derivative-based parsing has
received a lot of attention. Owens et al. were the first to present a
functional encoding of RE derivatives and use it to parsing and DFA
building. They use derivatives to build scanner generators for ML and
Scheme~\cite{Owens2009} and no formal proof of correctness were
presented.

Might et al.~\cite{Might2011} report on
the use of derivatives for parsing not only RLs but also context-free
ones. He uses derivatives to handle context-free grammars (CFG) and
develops an equational theory for compaction that allows for efficient
CFG parsing using derivatives. Implementation of derivatives for CFGs
are described by using the Racket programming
language~\cite{Felleisen2013}. However, Might et al. do not present
formal proofs related to the use of derivatives for CFGs.

Fischer et al. describes an algorithm for RE-based parsing based on
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

\paragraph{Certified parsing algorithms}: certified algorithms for
parsing also received attention recently. Firsov et al.~describe a
certified algorithm for RE parsing by converting an input RE to an
equivalent non-deterministic finite automata (NFA) represented as a
boolean matrix~\cite{FirsovU13}. A matrix library based on some
``block'' operations~\cite{MacedoO13} is developed and used Agda
formalization of NFA-based parsing in Agda~\cite{Norell2009}. Compared
to our work, a NFA-based formalization requires a lot more
infrastructure (such as a Matrix library). No experiments with the
certified algorithm were reported.

Firsov describes an Agda formalization of a parsing algorithm that
deals with any CFG (CYK algorithm)~\cite{Firsov2014}. Bernardy
et al.~describe a formalization of another CFG parsing algorithm in
Agda~\cite{BernardyJ16}: Valiant's algorithm~\cite{Valiant1975}, which
reduces CFG parsing to boolean matrix multiplication. In both works,
no experiment with formalized parsing algorithms were reported.

A certified LR(1) CFG validator is described
in~\cite{Jourdan2012}. The formalized checking procedure
verifies if CFG and a automaton match. They proved soundness and
completeness of the validator in Coq proof
assistant~\cite{Bertot2010}. Termination of LR(1) automaton
interpreter is ensured by imposing a natural number bound.

Formalization of a parser combinator library was the subject of
Danielsson's work~\cite{Danielsson2010}. He built a library of parser
combinators using coinduction and provide correctness proofs of such
combinators.

Almeida et al.~\cite{AlmeidaMPS10} describes a Coq formalization of
partial derivatives and its equivalence with automata. Partial
derivatives were introduced by Antimirov~\cite{Antimirov91} as
an alternative to Brzozowski derivatives, since it avoids quotient
resulting REs with respect to ACUI axioms. Almeida et al. motivation
is to use such formalization as a basis for a decision procedure for
RE equivalence.

Ridge~\cite{Ridge2011} describes a formalization, in HOL4 theorem prover, of
combinator parsing library. A parser generator for such combinators is described
and a proof that generated parsers are sound and complete is presented.
According to Ridge, preliminary results shows that parsers built using his
generator are faster than those created by Happy parser generator~\cite{Happy}.

Ausaf et.al.~\cite{AusafDU16} describes a formalization, in Isabelle/HOL~\cite{Nipkow02},
of POSIX matching algorithm proposed by Sulzmann et.al.~\cite{SulzmannL14}. They
give a constructive characterization of what a POSIX matching is and prove that
such matching is unique for a given RE and string. No experiments with the
veried algorithm are reported.


\section{Conclusion}\label{sec:conclusion}

We have given a complete formalization of a derivative-based parsing
for REs in Agda. To the best of our knowledge, this is the first work
that presents a complete certification and that uses the certified
program to build a tool for RE-based search.

The developed formalization has 1145 lines of code, organized in 20
modules. We have proven 39 theorems and lemmas to complete the
development. Most of them are immediate pattern matching functions
over inductive datatypes and were omitted from this text for brevity.

As future work, we intend to work on the development of a certified
program of greedy and POSIX RE parsing using Brzozowski
derivatives~\cite{SulzmannL14,FrischC04} and investigate on
ways to obtain a formalized but simple and efficient RE parsing tool.

\paragraph{Acknowledgements:} The first author thanks CNPq for financial
support. Second author thanks Fundação de Amparo a
Pesquisa de Minas Gerais (FAPEMIG) for financial support.

\section*{References}

\bibliography{main}

\end{document}

