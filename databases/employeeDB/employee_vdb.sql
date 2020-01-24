### ###########################################
#Create Tables for employee database usecase. #
###############################################
DROP DATABASE IF EXISTS employee_vdb;
CREATE DATABASE IF NOT EXISTS employees_vdc;
USE employees_vdb;

# v_engineerpersonnel(empno, name, hiredate, title, deptname, presCond)
DROP TABLE IF EXISTS `v_engineerpersonnel`;
CREATE TABLE `v_engineerpersonnel` (
  `empno` int(11) NOT NULL,
  `name` varchar(31) DEFAULT NULL,
  `hiredate` date NOT NULL,
  `title` varchar(50) NOT NULL,
  `deptname` varchar(40) NOT NULL,
  `presCond` varchar(31) DEFAULT NULL
)

# v_otherpersonnel (empno, name, hiredate, title, deptname, presCond)
DROP TABLE IF EXISTS `v_otherpersonnel`;
CREATE TABLE `v_otherpersonnel` (
  `empno` int(11) NOT NULL,
  `name` varchar(31) DEFAULT NULL,
  `hiredate` date NOT NULL,
  `title` varchar(50) NOT NULL,
  `deptname` varchar(40) NOT NULL,
  `presCond` varchar(31) DEFAULT NULL
) 

# v_empacct(empno, name, hiredate, title, deptname, deptno, salary, presCond)
DROP TABLE IF EXISTS `v_empacct`;
CREATE TABLE `v_empacct` (
  `empno` int(11) NOT NULL,
  `name` varchar(31) DEFAULT NULL,
  `hiredate` date NOT NULL,
  `title` varchar(50) NOT NULL,
  `deptname` varchar(40) DEFAULT NULL,
  `deptno` varchar(4) DEFAULT NULL,
  `salary` int(11) DEFAULT NULL,
  `presCond` varchar(31) DEFAULT NULL
) 

# v_job(title, salary, presCond)
DROP TABLE IF EXISTS `v_job`;
CREATE TABLE `v_job` (
  `title` varchar(50) NOT NULL,
  `salary` int(11) DEFAULT NULL,
  `presCond` varchar(31) NOT NULL
) 

# v_dept(deptname, deptno, managerno,presCond)
DROP TABLE IF EXISTS `v_dept`;
CREATE TABLE `v_dept` (
  `deptname` varchar(40) NOT NULL,
  `deptno` char(4) NOT NULL,
  `managerno` int(11) NOT NULL,
  `presCond` varchar(31) DEFAULT NULL
) 

# v_empbio(empno, sex, birthdate, name, lastname,firstname, presCond)
DROP TABLE IF EXISTS `v_empbio`;
CREATE TABLE `v_empbio` (
  `empno` int(11) NOT NULL,
  `sex` enum('M','F') NOT NULL,
  `birthdate` date NOT NULL,
  `name` varchar(31) DEFAULT NULL,
  `lastname` varchar(31) DEFAULT NULL,
  `firstname` varchar(31) DEFAULT NULL,
  `presCond` varchar(31) DEFAULT NULL
)

### ###########################################
# Information about original employees DB     #
###############################################

-- mysql> select count(*) from employees where hire_date < '1988-01-01';
-- +----------+
-- |   104967 |
-- +----------+

-- mysql> select count(*) from employees where hire_date >= '1988-01-01' And hire_date < '1991-01-01';
-- +----------+
-- |    85440 |
-- +----------+

-- mysql> select count(*) from employees where hire_date >= '1991-01-01' and hire_date < '1994-01-01';
-- +----------+
-- |    60742 |
-- +----------+

-- mysql> select count(*) from employees where hire_date >= '1994-01-01' and hire_date < '1997-01-01';
-- +----------+
-- |    36524 |
-- +----------+

-- mysql> select count(*) from employees where hire_date >= '1997-01-01';
-- +----------+
-- |    12351 |
-- +----------+

### ###########################################
# Populating data into employee v-tables.     #
###############################################

-- ** Steps to populating v-tables

-- 1. Chop employees into 5 parts (A,B,C,D,E) based on hire_date
-- 2. For v-table `v_engineerpersonnel` and `v_otherpersonnel`:
--    1) populate employees in A whose title is Enginner into enginnerpersonnel
--    2) insert the rest of employees of A into otherpersonnel
--    3) The presCond value for these 2 tables shoule be `v1`
-- 3. For v-table ``v_empacct`:
--    1) Employees in B,C,D,E will be inserted into v_empacct
--   +-------+-------+----------+-------+----------+-------+-------+---------+
--   | empno | name  | hiredate | title | deptname | deptno| salary| presCond|
--   +-------+-------+----------+-------+----------+-------+-------+---------+
-- B |  xx   |   xx  |    xx    |   xx  |   xx     |  NULL |  NULL |    v2   |
--   +-------+-------+----------+-------+----------+-------+-------+---------+
-- C |  xx   |   xx  |    xx    |   xx  |   NULL   |  xx   |  NULL |    v3   |
--   +-------+-------+----------+-------+----------+-------+-------+---------+
-- D |  xx   |  NULL |    xx    |   xx  |   NULL   |  xx   |  NULL |    v4   |
--   +-------+-------+----------+-------+----------+-------+-------+---------+
-- E |  xx   |  NULL |    xx    |   xx  |   NULL   |  xx   |  xx   |    v5   |
--   +-------+-------+----------+-------+----------+-------+-------+---------+

-- 4. For v-table `v_job`, Employee in A,B,C,D,E will be inserted in it.
-- 5. For v-table `v_dept`, employes in C, D, E will be inserted in it as follows:
--   +----------+--------+-----------+---------+
--   | deptname | deptno | managerno | presCond|
--   +----------+--------+-----------+---------+
-- C |   xx     |   xx   |  xx       |    v3   |
--   +----------+--------+-----------+---------+
-- D |   xx     |   xx   |  xx       |    v4   |
--   +----------+--------+-----------+---------+
-- E |   xx     |   xx   |  xx       |    v5   |
--   +----------+--------+-----------+---------+
-- 6. For v-table `v_empbio`, employee in D, E will be inserted in it accordingly:
--   +----------+--------+-----------+---------+-----------+---------+-----------+
--   | empno    | sex    | birthdate | name    | firstname | lastname| presCond  |
--   +----------+--------+-----------+---------+-----------+---------+-----------+
-- D |   xx     |   xx   |  xx       |    xx   |  NULL     | NULL    |   v4      |
--   +----------+--------+-----------+---------+-----------+---------+-----------+
-- E |   xx     |   xx   |  xx       |   NULL  |  xx       |  xx     |   v5      |
--   +----------+--------+-----------+---------+-----------+---------+-----------+
