<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# GeometricAlgebra

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/GeometricAlgebra/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/GeometricAlgebra/actions/workflows/docker-action.yml




This is an update of the original project 
  [GeometricAlgebra](http://www-sop.inria.fr/marelle/GeometricAlgebra/).
The project should now be compatible with Rocq 9.0

Simply run `make` to compile the relevant files.

This is the content of the old Readme:

>This archive contains all the material of the formalisation of our Grassman
>Cayley and Clifford formalisation. It has been developped with Coq 8.3
>To compile it, a simple make should be enough
>
>Laurent.Fuchs@sic.univ-poitiers.fr
>Laurent.Thery@inria.fr

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Compatible Rocq/Coq versions: 9.0 or later
- Additional dependencies: none
- Rocq/Coq namespace: `GeometricAlgebra`
- Related publication(s): none

## Building and installation instructions

To build and install manually, do:

``` shell
git clone https://github.com/thery/GeometricAlgebra.git
cd GeometricAlgebra
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



