# Changelog

<<<<<<< HEAD
### 0.0.6 (2021-07-07)
* A new option `--environment` for checking external tools and configurations that are required
* Clarify errors caused by external tools/configurations that are not installed properly
* Better error messages
* Improve incrementalization algorithms
* Support transactions at the Serializable isolation level

=======
>>>>>>> d96beeb (introduce files)
### 0.0.5 (2021-06-04)
* Send transaction IDs when detecting updates on Dejima views
* No Greek alphabet characters in generated SQL code
* Switch to a new ast in Expr2.ml

### 2020-12-02
* Fix bugs in the Datalog evaluator
* Accept `'` in the end of a variable name
* SQL functions to force BXs to propagate updates between views and sources in a transaction
* Fix bugs in the SQl generation

### 0.0.4 (2020-04-01)
* CLI: Update some options and add new options
* New counterexample & explanation generator
* New in-memory Datalog evaluator
* New features for WebUI

### 2019-12-11
<<<<<<< HEAD
* Incrementally calculate Dejima view updates
=======
* Incrementally calculate Dejima view updates.
>>>>>>> d96beeb (introduce files)

### 0.0.3 (2019-11-15)
* Fix bugs
* Benchmarks
* Modify the syntax of schema declaration

### 2019-09-07
* New WebUI
* Add a new option timeout for the verification
* Fix bugs of the data type real 
* Add a new option for speed-up by parallel verification
* Remove the option -m mode, it will be automatically detected 

### 2019-03-17:
* Add option install in Makefile
* Fix bugs in Makefile
* Add option -m in commandline-line interface
* Grammar for arithmetic expressions
* FOL transformations for verification and view derivation
* Integrating with Lean and Z3 for verification
* Optimization for Datalog
* New syntax for schema declaration

### 0.0.2 (2018-10-15):

* New trigger architecture: using three triggers, each trigger for each step in update process from view to source relations
* Fix bug of row type of a single column
* Change the name of Compile_error to SemErr
* Using rowtype instead of record
* Allow predicate names to start with an underscore