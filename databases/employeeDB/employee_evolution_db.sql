### ###########################################
#Create Tables for employee database usecase. #
###############################################
DROP DATABASE IF EXISTS employee_evolution_db;
CREATE DATABASE IF NOT EXISTS employee_evolution_db;
USE employee_evolution_db;

# v1_engineerpersonnel(empno, name, hiredate, title, deptname)
DROP TABLE IF EXISTS `v1_engineerpersonnel`;
CREATE TABLE `v1_engineerpersonnel` (
  `empno` int(11) NOT NULL,
  `name` varchar(31) DEFAULT NULL,
  `hiredate` date NOT NULL,
  `title` varchar(50) NOT NULL,
  `deptname` varchar(40) NOT NULL
);

# v1_otherpersonnel (empno, name, hiredate, title, deptname, presCond)
DROP TABLE IF EXISTS `v1_otherpersonnel`;
CREATE TABLE `v1_otherpersonnel` (
  `empno` int(11) NOT NULL,
  `name` varchar(31) DEFAULT NULL,
  `hiredate` date NOT NULL,
  `title` varchar(50) NOT NULL,
  `deptname` varchar(40) NOT NULL
); 

# v2_empacct(empno, name, hiredate, title, deptname)
DROP TABLE IF EXISTS `v2_empacct`;
CREATE TABLE `v2_empacct` (
  `empno` int(11) NOT NULL,
  `name` varchar(31) DEFAULT NULL,
  `hiredate` date NOT NULL,
  `title` varchar(50) NOT NULL,
  `deptname` varchar(40) DEFAULT NULL
);

# v3_empacct(empno, name, hiredate, title, deptno)
DROP TABLE IF EXISTS `v3_empacct`;
CREATE TABLE `v3_empacct` (
  `empno` int(11) NOT NULL,
  `name` varchar(31) DEFAULT NULL,
  `hiredate` date NOT NULL,
  `title` varchar(50) NOT NULL,
  `deptno` varchar(4) DEFAULT NULL
); 

# v4_empacct(empno, hiredate, title, deptno)
DROP TABLE IF EXISTS `v4_empacct`;
CREATE TABLE `v4_empacct` (
  `empno` int(11) NOT NULL,
  `hiredate` date NOT NULL,
  `title` varchar(50) NOT NULL,
  `deptno` varchar(4) DEFAULT NULL
); 

# v5_empacct(empno, hiredate, title, deptno, salary)
DROP TABLE IF EXISTS `v5_empacct`;
CREATE TABLE `v5_empacct` (
  `empno` int(11) NOT NULL,
  `hiredate` date NOT NULL,
  `title` varchar(50) NOT NULL,
  `deptno` varchar(4) DEFAULT NULL,
  `salary` int(11) DEFAULT NULL
); 

# v4_empbio(empno, sex, birthdate, name)
DROP TABLE IF EXISTS `v4_empbio`;
CREATE TABLE `v4_empbio` (
  `empno` int(11) NOT NULL,
  `sex` enum('M','F') NOT NULL,
  `birthdate` date NOT NULL,
  `name` varchar(31) DEFAULT NULL
);

# v5_empbio(empno, sex, birthdate, firstname, lastname)
DROP TABLE IF EXISTS `v5_empbio`;
CREATE TABLE `v5_empbio` (
  `empno` int(11) NOT NULL,
  `sex` enum('M','F') NOT NULL,
  `birthdate` date NOT NULL,
  `firstname` varchar(31) DEFAULT NULL,
  `lastname` varchar(31) DEFAULT NULL
);


# job(title, salary)
DROP TABLE IF EXISTS `job`;
CREATE TABLE `job` (
  `title` varchar(50) NOT NULL,
  `salary` int(11) DEFAULT NULL
); 

# dept(deptname, deptno, managerno)
DROP TABLE IF EXISTS `dept`;
CREATE TABLE `dept` (
  `deptname` varchar(40) NOT NULL,
  `deptno` char(4) NOT NULL,
  `managerno` int(11) NOT NULL
); 

