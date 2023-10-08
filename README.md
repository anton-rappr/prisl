
# prisl
Slicing tool for the PRISM Language written with the help of the storm parser in cpp

## About this project
This project is the source code of the prisl tool, which is capable
of slicing the PRISM-language.
It uses the [C++ API](https://www.stormchecker.org/api/) of the [storm model checker](https://www.stormchecker.org/). 
It uses the storm API to parse PRISM model files. The parsed model 
is then used to construct a dependency graph which is ultimately used 
to slice the model and write it to the ```slice.prism``` file

## Installation

### Dependencies 

- Since prisl is written in the C++ language, you need to be able to
compile `.cpp` written in the C++17 standard.

- Additionally since this tool is using the storm API, you first need 
to build storm from source. Therefore you first need to install the
dependencies of storm from
    1. Install the [dependencies of storm](https://www.stormchecker.org/documentation/obtain-storm/dependencies.html)

    1. and then [build storm from source](https://www.stormchecker.org/documentation/obtain-storm/build.html) 
    (Note: building `storm-main` suffices)

### Running prisl 

After you installed all the dependencies and cloned this repository,
open a terminal in the root directory of the repository. Now all you need to do is run the following commands.
```
mkdir build 
cd build 
cmake .. 
make 
cd ..
```

To check if everything installed correctly, run 
```
./build/prisl ./benchmarks/eajs_5.prism b
```

This will run a benchmark of the slicing of the ```eajs_5.prism``` model
file and if everything works correctly you should get an output
containing the benchmark results containing (along others) the following results
```
...
Results:
      nodes: 423
      edges: 12465
      slices: 34
      avg_size unweighted: 181.3823547
      avg_size weighted: 365.2907715
...
```
for the COMPONENTS benchmark and 
```
...
Results: 
      modules: 8
      edges: 55
      slices: 1
      avg_size_uw = 8.000000000/1.000000000 = 8.000000000
      avg_size_w = 64.000000000/8.000000000 = 8.000000000
...
```
for the MODULE benchmark.

## How to use

To run the executable 
you will need to first specify the prism model file, next the type of slicingcriterion that you
wish to use and then atleast one slicing criterion.

In general the tool can be used from the root directory of this repo as follows:
```
./build/prisl PRISM_FILE TYPE CRIT [CRIT]...
```

### PRISM_FILE
`PRISM_FILE` is the path to the PRISM model you want to slice.
The PRISM model files can be of type `.prism`, `.pm` or `.nm`.

### TYPE and CRIT
The `TYPE` parameter refers to the type of the given slicing criteria.
The `TYPE` parameter also determines what critera are allowed and how to select them correctly.
The following criterion types are supported.

- `module` or just `m`: Slices the given model for modules 
    - input: names of the modules in the model. Additionally accepts `global` for the global module.
    - example:
    ```
    ./build/prisl ./benchmarks/indep_mods.prism m m1 m2 m3
    ```
- `variable` or just `v`: Slices the given model with the given variables, formulas or constants as criterion.
    - input: names of the variables or formulas or constants inside the model
    - example:
    ```
    ./build/prisl ./benchmarks/eajs_5.prism v process_1_finishes
    ```
- `component` or just `c`: Takes components of type `Variablendeklaration` ,`Konstantendefinition`, `Formeldefinition`, `guard`, `rate`, `assignment`, or `init`.
    - input: the code segments of the components surrounded by `"`, f.e. `"a & b"`. If there are multiple components with this code segment, then the first one (starting from the first line going to the last) will be used
    - example:
    ```
    ./build/prisl ./benchmarks/resource-gathering.pm c "(y'=(y + 1))" "pAttack"
    ```
    - note: since criteria will be searched in the parsed version of the model file, you might need to choose the components based on how they are formatted in the 
    parsed model file.

### MISCELLANEOUS
There is two more functionalities of prisl aside from slicing.
- benchmarking: as seen in the installation section
    ```
    ./build/prisl PRISM_FILE b
    ```
    Slices the given file by all possible single components and modules and prints benchmarking results.

- just parsing: since the storm parser does some formatting, this might be useful to get the correct string of a component. usage via 
    ```
    ./build/prisl PRISM_FILE parse
    ```