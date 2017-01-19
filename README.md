# Indifferentiability

## Installation

*1*. Install [Opam](https://opam.ocaml.org/).

 * In Ubuntu,

~~~~~
apt-get install -y ocaml ocaml-native-compilers opam m4 camlp4-extra
~~~~~

 * In OS X, use homebrew,

~~~~~
brew install opam
~~~~~

*2*. Install the right compiler and the right libraries.

~~~~~
opam pin add indiff CLONED_DIR -n
opam install indiff --deps-only
~~~~~

*3*. To compile and test the tool, execute the following commands:

~~~~~
make
./main.native examples/5-rounds-feistel-attack.ind
~~~~~