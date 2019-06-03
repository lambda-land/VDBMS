# VDBMS

A **variational database management system** that accounts for variability in the context of relational databases by assigning propositional formulas of features to attributes, tuples, and relations. It also provides a variational query language for the user to interact with the variational database. It sits on top of a DBMS, currently Sqlite but the extensible design of the system allows one to change it easily.

VDBMS is most useful when the structure of data changes but the user wants to access all the variants at the same time. It is also desirable for the user to just run one query to achieve an information need instead of re-writing a query according to each database. The variational query language provides user with such a functionality.

## Installation
Most of the installation is handled by [Haskell Stack][Stack], which will
automatically install the Haskell compiler (GHC), build system (Cabal), and
other Haskell dependencies.

### Step-by-step installation guide
1. **Install Stack.** Also available via standard package managers, or from the
   [Stack home page][Stack].

2. **Use Stack to complete installation.** Run the following commands in order:

   ```bash
   > stack setup     # downloads the package index and installs GHC
   > stack build     # installs dependencies and builds the project
   ```


## How to Use

Unfortunately, the implementation of VDBMS is not complete yet. However, you can still run some examples and see some output to
see how our translation is working. 

In order to run examples, simply fire up GHCi in the project directory by running the following command:

	```bash
	> stack ghci
	```

Now you can see the final SQL query of a variational query over the Employee database by running the following:

	```bash
	> printSql q  employeeVSchema
	```

You can choose any of the sample queries written in src/Examples/EmployeeUseCase/EmployeeQs.hs and src/Examples/EmployeeUseCase/EmployeeQuery.hs.

For example:
	```bash
	> printSql empVQ1naive  employeeVSchema
	```

Results in:
```TO BE COMPLETED!
```


## Papers

TODO

[Stack]: http://docs.haskellstack.org/en/stable/README/
