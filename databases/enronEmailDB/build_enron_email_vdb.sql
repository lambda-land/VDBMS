# create a view for p1_employee for prodcut focusing on daily usage. 
# SELECT count(eid) -- 30
-- CREATE OR REPLACE view p1_employee_view AS 
-- SELECT eid, firstname, lastname, email_id, folder, status
-- FROM employeelist emp 
-- WHERE eid <= 30;

# create a view for p2_employee for prodcut focusing on pivacy. 
# create signature and public_key
# SELECT count(eid) -- 30
-- CREATE OR REPLACE view p2_employee_view AS 
-- SELECT eid, firstname, lastname, email_id, folder, status, 
-- CASE    
-- WHEN  status is NULL THEN  concat(firstname, " ", lastname)
-- WHEN status = "N/A" THEN concat(firstname, " ", lastname)
-- WHEN  status is not NULL THEN concat(firstname, " ", lastname, '    |    ', status, "   ", email_id)
-- END AS sign, 
-- conv(floor(rand() * 99999999999999), 20, 36) as public_key
-- FROM employeelist emp 
-- WHERE eid > 30 AND eid <= 60;

# create a view for p3_employee for prodcut focusing on group usage. 
# SELECT count(eid) -- 30
-- CREATE OR REPLACE view p3_employee_view AS 
-- SELECT eid, firstname, lastname, email_id, folder, status
-- FROM employeelist emp 
-- WHERE  eid > 60 AND eid <= 90;

# create a view for p4_employee for prodcut focusing on pivacy. 
# create signature and public_key
# SELECT count(eid) -- 30
-- CREATE OR REPLACE view p4_employee_view AS 
-- SELECT eid, firstname, lastname, email_id, folder, status, 
-- CASE    
-- WHEN  status is NULL THEN  concat(firstname, " ", lastname)
-- WHEN status = "N/A" THEN concat(firstname, " ", lastname)
-- WHEN  status is not NULL THEN concat(firstname, " ", lastname, '    |    ', status, "   ", email_id)
-- END AS sign, 
-- conv(floor(rand() * 99999999999999), 20, 36) as public_key
-- FROM employeelist emp 
-- WHERE eid > 90 AND eid <= 120;

# create a view for p3_employee for prodcut focusing on group usage. 
-- SELECT count(eid) -- 29
-- CREATE OR REPLACE view p3_employee_view AS 
-- SELECT eid, firstname, lastname, email_id, folder, status
-- FROM employeelist emp 
-- WHERE  eid > 120 AND eid <= 1500;

