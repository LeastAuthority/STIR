# Lean Blueprint for STIR Verification

This repository implements a Lean Blueprint to formally verify the cryptographic protocol **STIR: Reed–Solomon Proximity Testing with Fewer Queries**. For more details, please refer to the [STIR paper](https://eprint.iacr.org/2024/390).

The generated blueprint can be found [here](https://leastauthority.github.io/STIR/).

This project utilizes the [Lean Blueprint](https://github.com/PatrickMassot/leanblueprint) tool to structure and organize proofs in Lean using LaTeX.

---

## How to Participate

To contribute and work effectively with this repository using VSCode, please ensure you have the following extensions installed:

- **Lean4** – for Lean language support.
- **LaTeX Workshop** – for LaTeX editing and compilation.

---

## Project Structure

This repository leverages the Lean Blueprint tool for writing blueprints in Lean using LaTeX to organize proofs, with the specific goal of formally verifying the STIR cryptographic protocol.

The repository contains two primary TeX files:

- **`web.tex`**  
  Intended for use with plasTeX.

- **`print.tex`**  
  Meant to be compiled with traditional TeX engines such as *xelatex* or *lualatex*.

Both files import `macros/common.tex`, which contains macros common to both output formats. Macros that need to behave differently depending on the target output should be placed in:

- **`macros/web.tex`** for web-specific macros.
- **`macros/print.tex`** for print-specific macros.

*Note:* Each of these files includes inline comments that explain the structure and purpose.

The primary content of your blueprint should reside in `content.tex`. If you prefer to divide your content into multiple files, you can import them into `content.tex`.

---

## Key TeX Macros for Lean Integration

The following macros connect your Lean code with your TeX documents:

- **`\lean`**  
  Lists the Lean declaration names corresponding to the surrounding definition or statement (including namespaces).

- **`\leanok`**  
  Indicates that the surrounding environment (whether a definition, statement, or proof) has been fully formalized.

- **`\uses`**  
  Specifies LaTeX labels used in the current environment. This information is crucial for generating a dependency graph, with the context being either a definition, theorem, or proof depending on whether the labels are essential for the statement or only appear in the proof.

---

## Example Usage

Below is an example illustrating the usage of these macros. This example assumes the existence of a LaTeX label `def:prime` and a Lean declaration `euclid_inf_primes`.

```latex
\begin{theorem}[Euclid]
  \label{thm:euclid_inf_primes}
  \lean{euclid_inf_primes}
  \leanok
  \uses{def:prime}
  There exist infinitely many prime numbers.
\end{theorem}

\begin{proof}
  \leanok
  \uses{lem:divisibility, thm:prime_factorization}
  Suppose there are finitely many primes and let them be \(p_1, p_2, \dots, p_n\). Consider the number
  \[
  N = p_1 \cdot p_2 \cdots p_n + 1.
  \]
  None of the primes \(p_i\) divides \(N\) (as each leaves a remainder of 1), which leads to a contradiction. Thus, there must be infinitely many primes.
\end{proof}

## License

This project is released under the **Apache License.  The full text of the license is available in the [`LICENSE`](./LICENSE) file.
