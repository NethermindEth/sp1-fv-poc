# Proof-of-concept infrastructure for verification of SP1 zk chips

This repository contains a proof-of-concept Lean infrastructure for verification of SP1 zk chips. It is organised as follows:
- [`Sp1Poc/Wheels.lean`](Sp1Poc/Wheels.lean) contains auxiliary functions on Lean standard types;
- [`Sp1Poc/Basic.lean`](Sp1Poc/Basic.lean) contains basic definitions, functions, and facts about the BabyBear field and conformance theorem templating, noting that the fact that 2013265921 is prime is axiomatised as there are issues with its automated proof on Mac M1-M4 machines;
- [`Sp1Poc/Specs.lean`](Sp1Poc/Specs.lean) contains manually written specifications of chip behaviours---currently, it contains only the specification of wrap-around 32-bit addition;
- [`Sp1Poc/Templater.lean`](Sp1Poc/Templater.lean) generates the conformance theorem templates;
- [`Sp1Poc/Cli.lean`](Sp1Poc/Cli.lean) defines the command-line arguments for template generation;
- [`Sp1Poc.lean`](Sp1Poc.lean) brings the previous modules together to define the main `Sp1Poc` module;
- [`Main.lean`](Main.lean) defines the main user-facing function; and
- [`Examples/AddSub.main.lean`](Examples/AddSub.main.lean) contains the proof that the constraints extracted from the \texttt{AddSub} chip conform to the specification of wrap-around 32-bit addition, and is elaborated on in detail in \S\ref{sec:proof}.

Assuming that an installation of a version of Lean is present on the system, the infrastructure can be built using the following commands:
```
lake clean
lake update
lake exe cache get!
lake build
```
Once the installation has completed, the infrastructure can be used to generate a conformance theorem template by running:
```
lake exe genTemplate path-to-constraints-file template-folder-name [-f]
```
where:
- `path-to-constraints-file` is the path to a file that contains constraints extracted from an SP1 zk chip using the [extraction mechanism](https://github.com/NethermindEth/sp1-constraint-extractor);
- the generated template will be stored in the `Generated/template-folder-name/main.lean` file;
- `-f` is an optional argument to denote that generated files should be overwritten if they already exist.
