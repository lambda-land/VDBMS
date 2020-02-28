CREATE TABLE v_engineerpersonnel (
  empno integer NOT NULL,
  name varchar(31) DEFAULT NULL,
  hiredate date NOT NULL,
  title varchar(50) NOT NULL,
  deptname varchar(40) NOT NULL,
  presCond varchar(31) DEFAULT NULL
);

CREATE TABLE v_otherpersonnel (
  empno integer NOT NULL,
  name varchar(31) DEFAULT NULL,
  hiredate date NOT NULL,
  title varchar(50) NOT NULL,
  deptname varchar(40) NOT NULL,
  presCond varchar(31) DEFAULT NULL
);

CREATE TABLE v_empacct (
  empno integer NOT NULL,
  name varchar(31) DEFAULT NULL,
  hiredate date NOT NULL,
  title varchar(50) NOT NULL,
  deptname varchar(40) DEFAULT NULL,
  deptno varchar(4) DEFAULT NULL,
  salary integer DEFAULT NULL,
  presCond varchar(31) DEFAULT NULL
) ;

CREATE TABLE v_job (
  title varchar(50) NOT NULL,
  salary integer DEFAULT NULL,
  presCond varchar(31) NOT NULL
) ;

CREATE TABLE v_dept (
  deptname varchar(40) NOT NULL,
  deptno char(4) NOT NULL,
  managerno integer NOT NULL,
  presCond varchar(31) DEFAULT NULL
) ;

CREATE TYPE gender AS ENUM ('M', 'F');

CREATE TABLE v_empbio (
  empno integer NOT NULL,
  sex gender NOT NULL,
  birthdate date NOT NULL,
  name varchar(31) DEFAULT NULL,
  firstname varchar(31) DEFAULT NULL,
  lastname varchar(31) DEFAULT NULL,
  presCond varchar(31) DEFAULT NULL
);

