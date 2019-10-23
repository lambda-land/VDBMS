# v_engineerpersonnel(empno, name, hiredate, title, deptname, presCond)
-- DROP TABLE IF EXISTS `v_engineerpersonnel`;
-- CREATE TABLE `v_engineerpersonnel` (
--   `empno` int(11) NOT NULL,
--   `name` varchar(31) DEFAULT NULL,
--   `hiredate` date NOT NULL,
--   `title` varchar(50) NOT NULL,
--   `deptname` varchar(40) NOT NULL,
--   `presCond` varchar(31) DEFAULT NULL
-- );

-- INSERT INTO v_engineerpersonnel (empno, name, hiredate,title, deptname, presCond)
-- SELECT empno, name,hiredate,title, deptname, "v1" FROM v1_engineerpersonnel_view;

-- # v_otherpersonnel (empno, name, hiredate, title, deptname, presCond)
DROP TABLE IF EXISTS `v_otherpersonnel`;
CREATE TABLE `v_otherpersonnel` (
  `empno` int(11) NOT NULL,
  `name` varchar(31) DEFAULT NULL,
  `hiredate` date NOT NULL,
  `title` varchar(50) NOT NULL,
  `deptname` varchar(40) NOT NULL,
  `presCond` varchar(31) DEFAULT NULL
) ;

INSERT INTO v_otherpersonnel (empno, name, hiredate,title, deptname, presCond)
SELECT empno, name,hiredate,title, deptname, "v1" FROM v1_otherpersonnel_view;

-- # v_empacct(empno, name, hiredate, title, deptname, deptno, salary, presCond)
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
) ;

INSERT INTO v_empacct(empno, name, hiredate, title, deptname, deptno, salary, presCond)
SELECT empno, name, hiredate,title, deptname, NULL, NULL, "v2" 
FROM v2_empacct_view;

INSERT INTO v_empacct(empno, name, hiredate, title, deptname, deptno, salary, presCond)
SELECT empno, name, hiredate, title, NULL, deptno, NULL, "v3"
 FROM v3_empacct_view;

INSERT INTO v_empacct(empno, name, hiredate, title, deptname, deptno, salary, presCond)
SELECT empno, NULL, hiredate, title, NULL, deptno, NULL, "v4" 
FROM v4_empacct_view;

INSERT INTO v_empacct(empno, name, hiredate, title, deptname, deptno, salary, presCond)
SELECT empno, NULL, hiredate, title, NULL, deptno, salary, "v5" 
FROM v5_empacct_view;

-- # v_job(title, salary, presCond)
-- DROP TABLE IF EXISTS `v_job`;
-- CREATE TABLE `v_job` (
--   `title` varchar(50) NOT NULL,
--   `salary` int(11) DEFAULT NULL,
--   `presCond` varchar(31) NOT NULL
-- ) 


# v_dept(deptname, deptno, managerno,presCond)
DROP TABLE IF EXISTS `v_dept`;
CREATE TABLE `v_dept` (
  `deptname` varchar(40) NOT NULL,
  `deptno` char(4) NOT NULL,
  `managerno` int(11) NOT NULL,
  `presCond` varchar(31) DEFAULT NULL
) ;

INSERT INTO v_dept(deptname, deptno, managerno,presCond)
SELECT deptname, deptno, managerno,"v3" FROM v3_dept_view;

INSERT INTO v_dept(deptname, deptno, managerno,presCond)
SELECT deptname, deptno, managerno,"v4" FROM v4_dept_view;

INSERT INTO v_dept(deptname, deptno, managerno,presCond)
SELECT deptname, deptno, managerno,"v5" FROM v5_dept_view;

-- # v_empbio(empno, sex, birthdate, name, firstname, lastname presCond)
DROP TABLE IF EXISTS `v_empbio`;
CREATE TABLE `v_empbio` (
  `empno` int(11) NOT NULL,
  `sex` enum('M','F') NOT NULL,
  `birthdate` date NOT NULL,
  `name` varchar(31) DEFAULT NULL,
  `firstname` varchar(31) DEFAULT NULL,
  `lastname` varchar(31) DEFAULT NULL,
  `presCond` varchar(31) DEFAULT NULL
);

INSERT INTO v_empbio(empno, sex, birthdate, name, firstname, lastname, presCond)
SELECT empno, sex, birthdate, name, NULL, NULL, "v4" FROM v4_empbio_view;

INSERT INTO v_empbio(empno, sex, birthdate, name, lastname,firstname, presCond)
SELECT empno, sex, birthdate, NULL, lastname,firstname, "v5" FROM v5_empbio_view;

