##########
# v_employee 
##########

-- # create a view for p1_employee for prodcut focusing on daily usage. 
-- # SELECT count(eid) -- 30
-- CREATE OR REPLACE view p1_employee_view AS 
-- SELECT eid, firstname, lastname, email_id, folder, status
-- FROM employeelist emp 
-- WHERE eid <= 30;

-- # create a view for p2_employee for prodcut focusing on pivacy. 
-- # create signature and public_key
-- # SELECT count(eid) -- 30
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

-- # create a view for p3_employee for prodcut focusing on group usage. 
-- # SELECT count(eid) -- 30
-- CREATE OR REPLACE view p3_employee_view AS 
-- SELECT eid, firstname, lastname, email_id, folder, status
-- FROM employeelist emp 
-- WHERE  eid > 60 AND eid <= 90;

-- # create a view for p4_employee for prodcut with all feature enabled. 
-- # create signature and public_key
-- # SELECT count(eid) -- 30
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

-- # create a view for p3_employee for prodcut with all feature disabled. 
-- -- SELECT count(eid) -- 29
-- CREATE OR REPLACE view p5_employee_view AS 
-- SELECT eid, firstname, lastname, email_id, folder, status
-- FROM employeelist emp 
-- WHERE  eid > 120 AND eid <= 1500;

##########
# v_forward_msg(eid, forwardaddr)
##########
-- CREATE OR REPLACE view forward_msg_view as
-- SELECT eid, email2 AS forwardaddr
-- FROM employeelist
-- WHERE eid <= 30 or (eid > 90 AND eid <= 120 )
-- order by eid 


##########
# v_remail_msg(eid, pseudonym, presCond)
##########
-- CREATE OR REPLACE view remail_msg_view as 
-- SELECT eid,  concat(substring('ABCDEFGHIJKLMNOPQRSTUVWXYZ', rand()*26+1, 1),
--               substring('abcdelhio', rand()*9+1, 1),
--               substring('abcdelhio', rand()*9+1, 1),
--               substring('abcdefghijklmnopqrstuvwxyz', rand()*26+1, 1),
--               substring('abcdefghijklmnopqrstuvwxyz', rand()*26+1, 1),
--               substring('abcdefghijklmnopqrstuvwxyz', rand()*26+1, 1),
--               substring('abcdefghijklmnopqrstuvwxyz', rand()*26+1, 1),
--               substring('abcdefghijklmnopqrstuvwxyz', rand()*26+1, 1)
--              ) as pseudonym
-- FROM employeelist
-- where (eid > 30 AND eid <= 60) OR (eid > 90 AND eid <= 120)
-- order by eid

##########
# v_filter_msg(eid, suffix, presCond)
##########

##########
# v_mailhost(eid, username, mailhost, presCond)
##########
-- CREATE OR REPLACE view mailhost_view as 
-- SELECT eid, 
-- SUBSTRING(email_id, 1, LOCATE('@', email_id) - 1) AS username,
-- CASE
-- WHEN  eid% 3 = 0 THEN "phoenix_host"
-- WHEN  eid% 3 = 1 THEN "corvallis_host"
-- WHEN  eid% 3 = 2 THEN "seattle_host"
-- END AS mailhost 
-- FROM employeelist
-- WHERE  eid > 60 AND eid <= 120;

##########
# v_auto_msg(eid, subject, body)
##########
# eid should be in p3 and p4
-- CREATE OR REPLACE view auto_msg_view as 
-- SELECT eid, 
-- CASE    
-- WHEN  eid% 3 = 0 THEN  "out of office"
-- WHEN  eid% 3 = 1 THEN "Thanks for getting in touch. We’re on it."
-- WHEN  eid% 3 = 2 THEN "out of office"
-- END AS subject,
-- CASE
-- WHEN  eid% 3 = 0 THEN  "Hi,
-- I'm enjoying a holiday at sea and will be off the grid until the 15th of January! I'll get back to you that week. You could also reach out to my colleagues via support@email.com.
-- Thanks for your patience and talk to you then!
-- Best regards,
-- "
-- WHEN  eid% 3 = 1 THEN "Thanks for getting in touch. We’ll get back to you within 6 business hours (Monday-Friday 9am-6pm EST)."
-- WHEN  eid% 3 = 2 THEN "Thank you for your message. I am currently out of the office, with no email access. If you need immediate assistance before then, you may reach me at my mobile"
-- END AS body 
-- FROM employeelist
-- WHERE  eid > 60 AND eid <= 120 ;

##########
# v_alias(eid, email, nickname, presCond)
##########
-- CREATE OR REPLACE view alias_view as 
-- select eid, email_id, SUBSTRING_INDEX( email_id,'.',1) as nickname
-- FROM employeelist
-- WHERE  eid > 60 AND eid <= 120
-- order by eid

##########
# v_message(mid, sender, date, message_id, subject, body, folder, 
#                    is_system_notification, is_signed, is_encrypted, is_from_remailer, is_autoresponse, is_forward_msg) 
# is_system_notification is true, if 
# is_signed is true, if  sender is in p2 and p4
# is_encrypted is true, if  sender is in p2 and p4
# is_from_remailer is true,  ??? the first line is recipient....
# is_autoresponse is true,  if  message is OOO, and sender is in P3 and P4
# is_forward_msg is true, if the message's subject is FWD and sender is in p1 and p4
##########
-- # create a view for p1_message for prodcut focusing on daily usage. 
-- CREATE OR REPLACE view p1_message_view AS 



