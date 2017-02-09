Certified Derivative-based Parsing of Regular Expressions
=====================================

This repository contains verified implemenations of regular expression search algorithms
based on Brzozowski derivatives and Antivirov partial derivatives.

A certified tool for regular expression search, using both types of derivatives
(Brzozowski and Antimirov) are developed in Agda.

Proofs of soundness and completeness for Brzozowski derivatives are developed in Coq.

A first prototype of this tool was developed in Idris version 0.9.11.

Building
=====

The parsing tool was built using Agda 2.5.2 using Standard Library 0.13 and the GHC
backend (MAlonzo). We use GHC version 8.0.1.

