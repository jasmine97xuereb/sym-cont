# Symbolic Controllability

A tool using OCaml to check whether a monitor is symbolically controllable.

## Getting Started

These instructions will get you a copy of the project up and running on your local machine for development and testing purposes. 

### Installing

What things you need to install the software and how to install them.

#### Installs curl
```
sudo apt install curl
```

#### Installs opam 
Opam is the package manager for OCaml.
```
sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
```
#### Sets up environment
```
opam init
```
#### Sets up necessary environment variables
```
eval $(opam env)
```
#### Installs the OCaml compiler version 4.08.0
```
opam switch create 4.08.0
eval $(opam env)
```
#### Installs opam-depext 
Opam-depext is a tool to query and install external dependencies of opam packages.
```
opam install depext
eval $(opam env)
```
#### Install Z3 dependencies gmp and m4 outside of opam
```
opam depext conf-gmp.1
opam depext conf-m4.1
```
#### Installs Z3 
Z3 is an SMT Solver by Microsoft.
```
opam install z3
```
#### Sets the environment variable LD_LIBRARY_PATH 
```
export LD_LIBRARY_PATH=~/.opam/4.08.0/lib/z3
eval $(opam env)
```
#### Installs Zarith 
Zarith is a library used to implement arithmetic and logical operations over arbitrary-precision integers.
```
opam install zarith
eval $(opam env)
```
#### Installs Menhir 
Menhir is a parser generator for OCaml.
```
opam install menhir
eval $(opam env)
```
#### Install Oasis 
Oasis is a tool used to integrate a configure, build and install system in for OCaml projects.
```
opam install oasis
eval $(opam env)
```
#### To generates a build system, produce the files setup.ml, configure and Makefile, along with some others which can be safely ignored
```
oasis setup -setup-update dynamic
```
#### To build the project
```
make
```

## Running the tests

To run the automated tests for this system, run the file [run.py](https://github.com/jasmine97xuereb/sym-cont/blob/master/run.py). 
```
python run.py
```
<!-- This will automatically run the system set-up with three different pathological monitor descriptions, generated by [generate.py](https://github.com/jasmine97xuereb/sym-cont/blob/master/generate.py).
The mean running time over 3 repeated runs is calculated for each.  -->
This will automatically run the system set-up with generated monitor descriptions and calculate the mean running time (over 3 repeated runs). 

The experiment is repeated for incremental size and complexity for each of the three templates in [generate.py](https://github.com/jasmine97xuereb/sym-cont/blob/master/generate.py), starting at n=1 up to n=15.
Each run has a predefined time threshold of 10 hours, which if overcame, the run is terminated. 

This will produce a CSV file with 3 columns (one for each monitor template) and 15 rows (for incremental size and complexity). 
Each reading represents the corresponding mean running time. 

<!-- ## Authors

* **Jasmine Xuereb** - *Initial work* - [SymbolicControllability](https://github.com/jasmine97xuereb/sym-cont)

See also the list of [collaborator](https://github.com/your/project/contributors) who participated in this project. -->
