-- SELECT count(emp.emp_no) -- 152216
Create OR REPLACE view v2_empacct_view AS 
SELECT emp.emp_no as empno, concat(first_name, " ", last_name) as name, hire_date as hiredate, title, dept_name as deptname
FROM employees emp 
JOIN dept_emp de on emp.emp_no = de.emp_no 
JOIN departments dept on dept.dept_no = de.dept_no
JOIN titles on titles.emp_no = emp.emp_no
WHERE hire_date < '1991-01-01' and de.to_date = '9999-01-01'  and titles.to_date = '9999-01-01';

-- SELECT count(emp.emp_no) -- 201006
Create OR REPLACE view v3_empacct_view AS 
SELECT emp.emp_no as empno, concat(first_name, " ", last_name) as name, hire_date as hiredate, title, dept.dept_no as deptno
FROM employees emp 
JOIN dept_emp de on emp.emp_no = de.emp_no 
JOIN departments dept on dept.dept_no = de.dept_no
JOIN titles on titles.emp_no = emp.emp_no
WHERE  hire_date < '1994-01-01' and de.to_date = '9999-01-01'  and titles.to_date = '9999-01-01';

-- SELECT count(emp.emp_no) -- 230297 
Create OR REPLACE view v4_empacct_view AS 
SELECT emp.emp_no as empno, hire_date as hiredate, title, dept.dept_no as deptno
FROM employees emp 
JOIN dept_emp de on emp.emp_no = de.emp_no 
JOIN departments dept on dept.dept_no = de.dept_no
JOIN titles on titles.emp_no = emp.emp_no
WHERE hire_date < '1997-01-01' and de.to_date = '9999-01-01'  and titles.to_date = '9999-01-01';

-- SELECT count(emp.emp_no) -- 29291 -- 37286 without title.to_date = .... 
Create OR REPLACE view v4_empbio_view AS 
SELECT emp.emp_no as empno, gender as sex, birth_date as birthdate, concat(first_name, " ", last_name) as name
FROM employees emp 
JOIN dept_emp de on emp.emp_no = de.emp_no 
JOIN departments dept on dept.dept_no = de.dept_no
JOIN titles on titles.emp_no = emp.emp_no
WHERE hire_date < '1997-01-01' and de.to_date = '9999-01-01'  and titles.to_date = '9999-01-01'
order by emp.emp_no;

-- SELECT count(emp.emp_no) -- 240124
Create OR REPLACE view v5_empacct_view AS 
SELECT emp.emp_no as empno, hire_date as hiredate, title, dept.dept_no as deptno, salary
FROM employees emp 
JOIN dept_emp de on emp.emp_no = de.emp_no 
JOIN departments dept on dept.dept_no = de.dept_no
JOIN salaries on emp.emp_no = salaries.emp_no
JOIN titles on titles.emp_no = emp.emp_no
WHERE hire_date < '2000-01-28' and de.to_date = '9999-01-01' and salaries.to_date = '9999-01-01';

-- SELECT count( emp.emp_no) -- 240124
Create OR REPLACE view v5_empbio_view AS 
SELECT emp.emp_no as empno, gender as sex, birth_date as birthdate, first_name as  firstname, last_name as lastname
FROM employees emp 
JOIN dept_emp de on emp.emp_no = de.emp_no
JOIN salaries on emp.emp_no = salaries.emp_no
JOIN titles on titles.emp_no = emp.emp_no
WHERE hire_date < '2000-01-28'and salaries.to_date = '9999-01-01' and de.to_date = '9999-01-01' and titles.to_date =  '9999-01-01' 
order by emp.emp_no;

Create OR REPLACE view v3_dept_view AS 
SELECT dept_name as deptname, dept.dept_no as deptno, dept_manager.emp_no as managerno
FROM dept_manager  
JOIN departments dept on dept.dept_no = dept_manager.dept_no
JOIN employees emp on emp.emp_no = dept_manager.emp_no
WHERE hire_date < '1994-01-01'  and dept_manager.to_date = '9999-01-01';

Create OR REPLACE view v4_dept_view  AS 
SELECT dept_name as deptname, dept.dept_no as deptno, dept_manager.emp_no as managerno
FROM dept_manager  
JOIN departments dept on dept.dept_no = dept_manager.dept_no
JOIN employees emp on emp.emp_no = dept_manager.emp_no
WHERE hire_date < '1997-01-01'  and dept_manager.to_date = '9999-01-01';

Create OR REPLACE view v5_dept AS 
SELECT dept_name as deptname, dept.dept_no as deptno, dept_manager.emp_no as managerno
FROM dept_manager  
JOIN departments dept on dept.dept_no = dept_manager.dept_no
JOIN employees emp on emp.emp_no = dept_manager.emp_no
WHERE hire_date < '2000-01-28'  and dept_manager.to_date = '9999-01-01';

flush /*!50503 binary */ logs;