# Miscellaneous formalisations in Lean

[![.github/workflows/push.yml](https://github.com/YaelDillies/MiscYD/actions/workflows/push.yml/badge.svg)](https://github.com/YaelDillies/MiscYD/actions/workflows/push.yml)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/YaelDillies/MiscYD)

This repository is a collection of ideas and (partially implemented) projects in Lean.

## Content

The Lean code is located within the `MiscYD` folder. Within it, one can find:
* A `Mathlib` subfolder for the **prerequisites** to be upstreamed to mathlib. Lemmas that belong in an existing mathlib file `Mathlib.X` will be located in `MiscYD.Mathlib.X`. We aim to preserve the property that `MiscYD.Mathlib.X` only imports `Mathlib.X` and files of the form `MiscYD.Mathlib.Y` where `Mathlib.X` (transitively) imports `Mathlib.Y`. Prerequisites that do not belong in any existing mathlib file are placed in subtheory folders. See below.
* One folder for each **theory development**. The formal lecture transcripts only contain what was stated in the lectures, but sometimes it makes sense for a theory to be developed as a whole before being incorporated by the prerequisites or imported in the formal lecture transcripts.

### Content under development

The following topics are under active development in MiscYD.

* The impact function of a set
* The Birkhoff representation theorem, categorical version
* The Minkowski-Carathéodory theorem

See the [upstreaming dashboard](https://yaeldillies.github.io/MiscYD/upstreaming) for more information.

### Current content

The following topics are covered in MiscYD and could be upstreamed to Mathlib.

* Kneser's addition theorem
* The Sylvester-Chvatal theorem
* Containment of graphs

See the [upstreaming dashboard](https://yaeldillies.github.io/MiscYD/upstreaming) for more information.

The following topics are archived because they are already covered by mathlib, but nevertheless display interesting proofs:
* The Cauchy-Davenport theorem for `ℤ/pℤ` as a corollary of Kneser's theorem.

### Past content

The following topics have been upstreamed to mathlib and no longer live in MiscYD.

* The Birkhoff representation theorem, non-categorical version
* Shatterings of sets, the Sauer-Shelah lemma and the Vapnik-Chervonenkis dimension
* Sublattices
* Incidence algebras
* Strongly convex functions
* Visibility of a point through a set
* The upper bound on the Ruzsa-Szemerédi problem
* Cauchy's functional equation
* Marked groups

## Interacting with the project

### Getting the project

To build the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://leanprover-community.github.io/get_started.html) (under Regular install).
Alternatively, click on the button below to open a Gitpod workspace containing the project.

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/YaelDillies/LeanAPAP)

In either case, run `lake exe cache get` and then `lake build` to build the project.

### Browsing the project

With the project opened in VScode, you are all set to start exploring the code. There are two pieces of functionality that help a lot when browsing through Lean code:

* "Go to definition": If you right-click on a name of a definition or lemma (such as `Finset.sups`), then you can choose "Go to definition" from the menu, and you will be taken to the relevant location in the source files. This also works by `Ctrl`-clicking on the name.
* "Goal view": in the event that you would like to read a *proof*, you can step through the proof line-by-line, and see the internals of Lean's "brain" in the Goal window. If the Goal window is not open, you can open it by clicking on the forall icon in the top right hand corner.
