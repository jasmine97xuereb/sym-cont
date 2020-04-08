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
#### Installs the ocaml compiler version 4.08.0
```
opam switch create 4.08.0
eval $(opam env)
```
#### Installs depext
```
opam install depext
eval $(opam env)
```
#### Install Z3 dependencies gmp and m4 outside of opam
```
opam depext conf-gmp.1
opam depext conf-m4.1
```
#### Installs the Z3 SAT solver
```
opam install z3
```
#### Sets the environment variable LD_LIBRARY_PATH 
```
export LD_LIBRARY_PATH=~/.opam/4.08.0/lib/z3
eval $(opam env)
```
#### Installs Zarith
```
opam install zarith
eval $(opam env)
```
#### Installs Menhir
```
opam install menhir
eval $(opam env)
```
#### Install oasis
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

How to run the automated tests for this system
To run the automated test, run the file [run.py](https://github.com/jasmine97xuereb/sym-cont/blob/master/run.py). 
```
python run.py
```

### Break down into end to end tests

Explain what these tests test and why

```
Give an example
```

### And coding style tests

Explain what these tests test and why

```
Give an example
```

## Authors

* **Jasmine Xuereb** - *Initial work* - [PurpleBooth](https://github.com/PurpleBooth)

See also the list of [contributors](https://github.com/your/project/contributors) who participated in this project.
