# Partition employees 

-- v1
-- SELECT count(emp.emp_no) -- 83815
-- FROM employees emp 
-- JOIN dept_emp de on emp.emp_no = de.emp_no
-- JOIN salaries on emp.emp_no = salaries.emp_no
-- JOIN titles on titles.emp_no = emp.emp_no
-- WHERE hire_date < '1988-01-01'  and salaries.to_date = '9999-01-01' and de.to_date = '9999-01-01' and titles.to_date =  '9999-01-01' 
-- order by emp.emp_no

-- v2
-- SELECT count(emp.emp_no) -- 68401
-- FROM employees emp 
-- JOIN dept_emp de on emp.emp_no = de.emp_no
-- JOIN salaries on emp.emp_no = salaries.emp_no
-- JOIN titles on titles.emp_no = emp.emp_no
-- WHERE hire_date >= '1988-01-01'  and hire_date < '1991-01-01' and salaries.to_date = '9999-01-01' and de.to_date = '9999-01-01' and titles.to_date =  '9999-01-01' 
-- order by emp.emp_no

-- v3  
-- SELECT count(emp.emp_no) -- 48790
-- FROM employees emp 
-- JOIN dept_emp de on emp.emp_no = de.emp_no
-- JOIN salaries on emp.emp_no = salaries.emp_no
-- JOIN titles on titles.emp_no = emp.emp_no
-- WHERE hire_date >= '1991-01-01'  and hire_date < '1994-01-01' and salaries.to_date = '9999-01-01' and de.to_date = '9999-01-01' and titles.to_date =  '9999-01-01' 
-- order by emp.emp_no

-- v4
-- SELECT * 
-- SELECT count(emp.emp_no) -- 29291
-- FROM employees emp 
-- JOIN dept_emp de on emp.emp_no = de.emp_no
-- JOIN salaries on emp.emp_no = salaries.emp_no
-- JOIN titles on titles.emp_no = emp.emp_no
-- WHERE hire_date >= '1994-01-01' and hire_date < '1997-01-01' and salaries.to_date = '9999-01-01' and de.to_date = '9999-01-01' and titles.to_date =  '9999-01-01' 
-- order by emp.emp_no

-- v5
-- SELECT * 
-- SELECT count(emp.emp_no) -- 9827
-- FROM employees emp 
-- JOIN dept_emp de on emp.emp_no = de.emp_no
-- JOIN salaries on emp.emp_no = salaries.emp_no
-- JOIN titles on titles.emp_no = emp.emp_no
-- WHERE hire_date >= '1997-01-01'  and salaries.to_date = '9999-01-01' and de.to_date = '9999-01-01' and titles.to_date =  '9999-01-01' 
-- order by emp.emp_no

# Plain db for version 1 
## Create view v1_engineerpersonnel_view AS 
-- SELECT count(emp.emp_no) -- 42247 
-- -- SELECT emp.emp_no as empno, concat(first_name, " ", last_name) as name, hire_date as hiredate, title, dept_name as deptname
-- FROM employees emp 
-- JOIN dept_emp de on emp.emp_no = de.emp_no 
-- JOIN departments dept on dept.dept_no = de.dept_no
-- JOIN titles on titles.emp_no = emp.emp_no
-- WHERE hire_date < '1988-01-01' and title in ('Engineer', 'Senior Engineer', 'Assistant Engineer') and de.to_date = '9999-01-01' and titles.to_date =  '9999-01-01' ;

## CREATE view v1_otherpersonnel_view AS 
-- SELECT emp.emp_no as empno, concat(first_name, " ", last_name) as name, hire_date as hiredate, title, dept_name as deptname
-- SELECT count(emp.emp_no) -- 41568 
-- FROM employees emp 
-- JOIN dept_emp de on emp.emp_no = de.emp_no 
-- JOIN departments dept on dept.dept_no = de.dept_no
-- JOIN titles on titles.emp_no = emp.emp_no
-- WHERE hire_date < '1988-01-01' and title not in ('Engineer', 'Senior Engineer', 'Assistant Engineer') and de.to_date = '9999-01-01' and titles.to_date =  '9999-01-01' ;

-- SELECT count( empno) 
-- FROM v1_otherpersonnel_view 

-- SELECT *
-- FROM v1_otherpersonnel_view other
-- join v1_engineerpersonnel_view eng on other.empno = eng.empno 
-- order by other.empno

-- SELECT distinct title 
-- FROM titles

-- SELECT count( empno) 
-- FROM v1_engineerpersonnel_view

## vx_empacct/vx_empbio where x = 2,3,4,5
-- Create view v2_empacct AS 
-- SELECT emp.emp_no as empno, concat(first_name, " ", last_name) as name, hire_date as hiredate, title, dept_name as deptname
-- SELECT count(emp.emp_no) -- 68401
-- FROM employees emp 
-- JOIN dept_emp de on emp.emp_no = de.emp_no 
-- JOIN departments dept on dept.dept_no = de.dept_no
-- JOIN titles on titles.emp_no = emp.emp_no
-- WHERE hire_date >= '1988-01-01'  and hire_date < '1991-01-01' and de.to_date = '9999-01-01'  and titles.to_date = '9999-01-01'

-- Create view v3_empacct AS 
-- SELECT emp.emp_no as empno, concat(first_name, " ", last_name) as name, hire_date as hiredate, title, dept_no as deptno
-- SELECT count(emp.emp_no) -- 48790
-- FROM employees emp 
-- JOIN dept_emp de on emp.emp_no = de.emp_no 
-- JOIN departments dept on dept.dept_no = de.dept_no
-- JOIN titles on titles.emp_no = emp.emp_no
-- WHERE hire_date >= '1991-01-01'  and hire_date < '1994-01-01' and de.to_date = '9999-01-01'  and titles.to_date = '9999-01-01'

-- Create view v4_empacct AS 
-- SELECT emp.emp_no as empno, hire_date as hiredate, title, dept_no as deptno
-- SELECT count(emp.emp_no) -- 29291 
-- FROM employees emp 
-- JOIN dept_emp de on emp.emp_no = de.emp_no 
-- JOIN departments dept on dept.dept_no = de.dept_no
-- JOIN titles on titles.emp_no = emp.emp_no
-- WHERE hire_date >= '1994-01-01'  and hire_date < '1997-01-01' and de.to_date = '9999-01-01'  and titles.to_date = '9999-01-01'


-- Create view v4_empbio AS 
-- SELECT emp.emp_no as empno, gender as sex, birth_day as birth_date concat(first_name, " ", last_name) as name
-- SELECT count(emp.emp_no) -- 29291 -- 37286 without title.to_date = .... 
-- FROM employees emp 
-- JOIN dept_emp de on emp.emp_no = de.emp_no 
-- JOIN departments dept on dept.dept_no = de.dept_no
-- JOIN titles on titles.emp_no = emp.emp_no
-- WHERE hire_date >= '1994-01-01'  and hire_date < '1997-01-01' and de.to_date = '9999-01-01'  and titles.to_date = '9999-01-01'
-- order by emp.emp_no

-- Create view v5_empacct AS 
-- SELECT emp.emp_no as empno, hire_date as hiredate, title, dept_no as deptno, salaries as salary
-- SELECT count(emp.emp_no) -- 9827
-- FROM employees emp 
-- JOIN dept_emp de on emp.emp_no = de.emp_no 
-- JOIN departments dept on dept.dept_no = de.dept_no
-- JOIN salaries on emp.emp_no = salaries.emp_no
-- WHERE hire_date >= '1997-01-01' and de.to_date = '9999-01-01' and salaries.to_date = '9999-01-01'

-- Create view v5_empbio AS 
-- SELECT emp.emp_no as empno, gender as sex, birth_date as birthdate, first_name as  firstname, last_name as lastname
-- SELECT count(emp.emp_no)  -- 12351
-- FROM employees emp 
-- WHERE hire_date >= '1997-01-01' 
-- order by emp.emp_no

-- SELECT count(distinct emp.emp_no) -- 9827
-- FROM employees emp 
-- JOIN salaries on emp.emp_no = salaries.emp_no
-- WHERE hire_date >= '1997-01-01' and to_date = '9999-01-01'
-- order by emp.emp_no

-- Create view v5_empbio AS 
-- SELECT emp.emp_no as empno, gender as sex, birth_date as birthdate, first_name as  firstname, last_name as lastname
-- SELECT count( emp.emp_no) -- 9827
-- FROM employees emp 
-- JOIN dept_emp de on emp.emp_no = de.emp_no
-- JOIN salaries on emp.emp_no = salaries.emp_no
-- JOIN titles on titles.emp_no = emp.emp_no
-- WHERE hire_date >= '1997-01-01' and salaries.to_date = '9999-01-01' and de.to_date = '9999-01-01' and titles.to_date =  '9999-01-01' 
-- order by emp.emp_no

## vx_dept where x = 3,4,5
-- Create view v3_dept AS 
-- SELECT dept_name as deptname, dept.dept_no as deptno, dept_manager.emp_no as managerno
-- SELECT * 
-- FROM dept_manager  
-- JOIN departments dept on dept.dept_no = dept_manager.dept_no
-- JOIN employees emp on emp.emp_no = dept_manager.emp_no
-- WHERE hire_date >= '1991-01-01'  and hire_date < '1994-01-01'  and dept_manager.to_date = '9999-01-01'

-- Create view v4_dept AS 
-- SELECT dept_name as deptname, dept.dept_no as deptno, dept_manager.emp_no as managerno
-- SELECT count(distinct emp.emp_no)
-- FROM dept_manager  
-- JOIN departments dept on dept.dept_no = dept_manager.dept_no
-- JOIN employees emp on emp.emp_no = dept_manager.emp_no
-- WHERE hire_date >= '1994-01-01'  and hire_date < '1997-01-01'  and dept_manager.to_date = '9999-01-01'

-- Create view v5_dept AS 
-- SELECT dept_name as deptname, dept.dept_no as deptno, dept_manager.emp_no as managerno
-- SELECT count(distinct emp.emp_no)
-- FROM dept_manager  
-- JOIN departments dept on dept.dept_no = dept_manager.dept_no
-- JOIN employees emp on emp.emp_no = dept_manager.emp_no
-- WHERE hire_date >= '1997-01-01'  and dept_manager.to_date = '9999-01-01'

-- SELECT count(dept_no) -- 24
-- SELECT count(distinct dept_no) -- 9
-- FROM dept_manager

-- SELECT count(*) -- 9
-- FROM dept_manager 
-- WHERE to_date = '9999-01-01'

-- SELECT count(*)  -- 9
-- FROM departments 
-- order by dept_no


-- SELECT * 
-- FROM dept_manager  
-- JOIN departments dept on dept.dept_no = dept_manager.dept_no
-- JOIN employees emp on emp.emp_no = dept_manager.emp_no
-- WHERE dept_manager.to_date = '9999-01-01'
-- order by dept.dept_no 


