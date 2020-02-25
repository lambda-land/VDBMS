-- ##########
-- # v_employee 
-- ##########

-- # create a view for p1_employee for product focusing on daily usage. (enhanced email) 
-- # SELECT count(eid) -- 30
CREATE OR REPLACE view p1_employee_view AS 
SELECT eid, firstname, lastname, email_id, folder, status
FROM employeelist emp 
WHERE eid <= 30;

-- # create a view for p2_employee for prodcut focusing on pivacy. (privacy-focus email)
-- # create signature and public_key
-- # SELECT count(eid) -- 30
-- CASE    
-- WHEN  status is NULL THEN  concat(firstname, " ", lastname)
-- WHEN status = "N/A" THEN concat(firstname, " ", lastname)
-- WHEN  status is not NULL THEN concat(firstname, " ", lastname, '    |    ', status, "   ", email_id)
-- END AS sign, 
CREATE OR REPLACE view p2_employee_view AS 
SELECT eid, firstname, lastname, email_id, folder, status, 
conv(floor(rand() * 99999999999999), 20, 36) as sign,
conv(floor(rand() * 99999999999999), 20, 36) as public_key
FROM employeelist emp 
WHERE eid > 30 AND eid <= 60;

-- # create a view for p3_employee for prodcut focusing on group usage. (group email)
-- # SELECT count(eid) -- 30
CREATE OR REPLACE view p3_employee_view AS 
SELECT eid, firstname, lastname, email_id, folder, status,
conv(floor(rand() * 99999999999999), 20, 36) as sign,
conv(floor(rand() * 99999999999999), 20, 36) as public_key
FROM employeelist emp 
WHERE  eid > 60 AND eid <= 90;

-- # create a view for p4_employee for prodcut with all feature enabled. (premium email)
-- # create signature and public_key
-- # SELECT count(eid) -- 30
CREATE OR REPLACE view p4_employee_view AS 
SELECT eid, firstname, lastname, email_id, folder, status, 
conv(floor(rand() * 99999999999999), 20, 36) as sign,
conv(floor(rand() * 99999999999999), 20, 36) as public_key
FROM employeelist emp 
WHERE eid > 90 AND eid <= 120;

-- # create a view for p3_employee for prodcut with all feature disabled. (basic email)
-- SELECT count(eid) -- 29
CREATE OR REPLACE view p5_employee_view AS 
SELECT eid, firstname, lastname, email_id, folder, status
FROM employeelist emp 
WHERE  eid > 120 AND eid <= 1500;

-- ##########
-- # v_forward_msg(eid, forwardaddr)
-- ##########
CREATE OR REPLACE view forward_msg_view as
SELECT eid, email2 AS forwardaddr
FROM employeelist
WHERE eid <= 30 or (eid > 90 AND eid <= 120 )
order by eid;


-- ##########
-- # v_remail_msg(eid, pseudonym, presCond)
-- ##########
CREATE OR REPLACE view remail_msg_view as 
SELECT eid,  concat(substring('ABCDEFGHIJKLMNOPQRSTUVWXYZ', rand()*26+1, 1),
              substring('abcdelhio', rand()*9+1, 1),
              substring('abcdelhio', rand()*9+1, 1),
              substring('abcdefghijklmnopqrstuvwxyz', rand()*26+1, 1),
              substring('abcdefghijklmnopqrstuvwxyz', rand()*26+1, 1),
              substring('abcdefghijklmnopqrstuvwxyz', rand()*26+1, 1),
              substring('abcdefghijklmnopqrstuvwxyz', rand()*26+1, 1),
              substring('abcdefghijklmnopqrstuvwxyz', rand()*26+1, 1)
             ) as pseudonym
FROM employeelist
where (eid > 30 AND eid <= 60) OR (eid > 90 AND eid <= 120)
order by eid;

-- ##########
-- # filter_msg_view(eid, suffix)
-- ##########
CREATE OR REPLACE view filter_msg_view as
SELECT 1 as eid , "pgn.com" as suffix;

-- ##########
-- # v_mailhost(eid, username, mailhost, presCond)
-- ##########
CREATE OR REPLACE view mailhost_view as 
SELECT eid, 
SUBSTRING(email_id, 1, LOCATE('@', email_id) - 1) AS username,
CASE
WHEN  eid% 3 = 0 THEN "phoenix_host"
WHEN  eid% 3 = 1 THEN "corvallis_host"
WHEN  eid% 3 = 2 THEN "seattle_host"
END AS mailhost 
FROM employeelist
WHERE  eid > 60 AND eid <= 120;

-- ##########
-- # v_auto_msg(eid, subject, body)
-- ##########
-- # eid should be in p3 and p4
CREATE OR REPLACE view auto_msg_view as 
SELECT eid, 
CASE    
WHEN  eid% 3 = 0 THEN  "out of office"
WHEN  eid% 3 = 1 THEN "will follow up"
WHEN  eid% 3 = 2 THEN "out of office"
END AS subject,
CASE
WHEN  eid% 3 = 0 THEN  "will contact you after the holidays."
WHEN  eid% 3 = 1 THEN "Thanks for the info. will update you."
WHEN  eid% 3 = 2 THEN "reach me at my mobile."
END AS body 
FROM employeelist
WHERE  eid > 60 AND eid <= 120 ;

-- ##########
-- # v_alias(eid, email, nickname, presCond)
-- ##########
CREATE OR REPLACE view alias_view as 
select eid, email_id, SUBSTRING_INDEX( email_id,'.',1) as nickname
FROM employeelist
WHERE  eid > 60 AND eid <= 120
order by eid;

##########
# v_message(mid, sender, date, message_id, subject, body, folder, 
#                    is_system_notification, is_signed, is_encrypted, is_from_remailer, is_autoresponse, is_forward_msg) 
# is_system_notification is true, if 
# is_signed is true, if  sender is in p2 and p4 and has sign provisioned (not NULL)
# is_encrypted is true, if  sender is in p2 and p4 and has public_key provisioned (not NULL)
# is_from_remailer:, the message from enron data set  will be alwasy false 
# is_autoresponse:, the message from enron data set  will be alwasy false 
# is_forward_msg is true, if the message's the message from enron data set  will be alwasy false
##########
# ALTER TABLE employeelist
# DROP INDEX  idx_email_id;
# ALTER TABLE recipientinfo
# DROP INDEX idx_rvalue;
# ALTER TABLE message
# DROP INDEX idx_sender;

# CREATE INDEX idx_email_id ON employeelist(email_id); 
# CREATE INDEX idx_sender ON message(sender);
# CREATE INDEX idx_rec_mid ON recipientinfo(mid); 
# CREATE INDEX idx_msg_mid ON message(mid); 

-- # create a view for p1_message for prodcut focusing on daily usage(forward filter). alter
# SELECT count(mid) -- 19103
# p1_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_forward_msg) 
CREATE OR REPLACE view p1_message_view AS 
SELECT msg.*,  false as is_system_notification, false as is_forward_msg
FROM message msg 
inner join p1_employee_view emp on msg.sender = emp.email_id;

-- #create a view for p2_message for prodcut focusing on privacy. 
# SELECT count(mid) -- 25139
# p3_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_from_remailer) 
CREATE OR REPLACE view p2_message_view AS 
SELECT msg.*,  false as is_system_notification, 
CASE    
WHEN  emp.sign is NULL THEN false   
WHEN  emp.sign is not NULL THEN true
END AS is_signed,
CASE
WHEN  emp.public_key is not Null THEN true   
else  false
END AS is_encrypted, 
False as is_from_remailer
FROM message msg 
inner join p2_employee_view emp on msg.sender = emp.email_id;


-- #create a view for p3_message for prodcut focusing on group usage. 
# SELECT count(mid) -- 27952
-- # p3_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_autoresponse) 
CREATE OR REPLACE view p3_message_view AS 
SELECT msg.* , false as is_system_notification, false as is_autoresponse
FROM message msg 
inner join p3_employee_view emp on msg.sender = emp.email_id;

-- #create a view for p4_message for prodcut focusing on all feauture enabled. 
-- SELECT count(distinct msg.mid) -- 20138
# p3_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_from_remailer, is_autoresponse, is_forward_msg) 
CREATE OR REPLACE view p4_message_view AS 
SELECT msg.* , false as is_system_notification, 
CASE    
WHEN  emp.sign is NULL THEN false   
WHEN  emp.sign is not NULL THEN true
END AS is_signed,
CASE
WHEN  emp.public_key is not Null THEN true   
else  false
END AS is_encrypted, 
False as is_from_remailer,
false as is_autoresponse,
false as is_forward_msg
FROM message msg 
inner join p4_employee_view emp on msg.sender = emp.email_id;

# SELECT count(distinct msg.mid) -- 12434
CREATE OR REPLACE view p5_message_view AS 
SELECT msg.* , false as is_system_notification
FROM message msg 
inner join p5_employee_view emp on msg.sender = emp.email_id;



