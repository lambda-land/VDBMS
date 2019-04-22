-- CREATE TABLE auto_msg (
--     eid int,
--     subject text ,
--     body text,
--     PRIMARY KEY (eid)
-- );

-- insert into auto_msg (eid, subject, body)
-- SELECT eid, "out of office", "Hi,
-- I'm enjoying a holiday at sea and will be off the grid until the 15th of January! I'll get back to you that week. You could also reach out to my colleagues via support@email.com.
-- Thanks for your patience and talk to you then!
-- Best regards,
-- "
-- FROM v_employee WHERE eid>=75;

-- create view auto_msg_view as 
-- select eid, 
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
-- from auto_msg 


create table v_auto_msg as 
select * 
from auto_msg_view