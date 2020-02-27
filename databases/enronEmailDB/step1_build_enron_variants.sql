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
CASE
WHEN  eid% 5 = 0 THEN conv(floor(rand() * 99999999999999), 20, 36)
WHEN  eid% 5 = 1 THEN conv(floor(rand() * 99999999999999), 20, 36)
WHEN  eid% 5 = 2 THEN NULL
WHEN  eid% 5 = 3 THEN conv(floor(rand() * 99999999999999), 20, 36)
WHEN  eid% 5 = 4 THEN conv(floor(rand() * 99999999999999), 20, 36)
END as verification_key,
CASE
WHEN  eid% 5 = 0 THEN conv(floor(rand() * 99999999999999), 20, 36)
WHEN  eid% 5 = 1 THEN conv(floor(rand() * 99999999999999), 20, 36)
WHEN  eid% 5 = 2 THEN NULL
WHEN  eid% 5 = 3 THEN conv(floor(rand() * 99999999999999), 20, 36)
WHEN  eid% 5 = 4 THEN conv(floor(rand() * 99999999999999), 20, 36)
END as public_key
FROM employeelist emp 
WHERE eid > 30 AND eid <= 60;

-- # create a view for p3_employee for prodcut focusing on group usage. (group email)
-- # SELECT count(eid) -- 30
CREATE OR REPLACE view p3_employee_view AS 
SELECT eid, firstname, lastname, email_id, folder, status,
CASE
WHEN  eid% 5 = 0 THEN conv(floor(rand() * 99999999999999), 20, 36)
WHEN  eid% 5 = 1 THEN conv(floor(rand() * 99999999999999), 20, 36)
WHEN  eid% 5 = 2 THEN NULL
WHEN  eid% 5 = 3 THEN conv(floor(rand() * 99999999999999), 20, 36)
WHEN  eid% 5 = 4 THEN conv(floor(rand() * 99999999999999), 20, 36)
END as verification_key,
CASE
WHEN  eid% 5 = 0 THEN conv(floor(rand() * 99999999999999), 20, 36)
WHEN  eid% 5 = 1 THEN conv(floor(rand() * 99999999999999), 20, 36)
WHEN  eid% 5 = 2 THEN NULL
WHEN  eid% 5 = 3 THEN conv(floor(rand() * 99999999999999), 20, 36)
WHEN  eid% 5 = 4 THEN conv(floor(rand() * 99999999999999), 20, 36)
END as public_key
FROM employeelist emp 
WHERE  eid > 60 AND eid <= 90;

-- # create a view for p4_employee for prodcut with all feature enabled. (premium email)
-- # create signature and public_key
-- # SELECT count(eid) -- 30
CREATE OR REPLACE view p4_employee_view AS 
SELECT eid, firstname, lastname, email_id, folder, status, 
CASE
WHEN  eid% 5 = 0 THEN conv(floor(rand() * 99999999999999), 20, 36)
WHEN  eid% 5 = 1 THEN conv(floor(rand() * 99999999999999), 20, 36)
WHEN  eid% 5 = 2 THEN NULL
WHEN  eid% 5 = 3 THEN conv(floor(rand() * 99999999999999), 20, 36)
WHEN  eid% 5 = 4 THEN conv(floor(rand() * 99999999999999), 20, 36)
END as verification_key,
CASE
WHEN  eid% 5 = 0 THEN conv(floor(rand() * 99999999999999), 20, 36)
WHEN  eid% 5 = 1 THEN conv(floor(rand() * 99999999999999), 20, 36)
WHEN  eid% 5 = 2 THEN NULL
WHEN  eid% 5 = 3 THEN conv(floor(rand() * 99999999999999), 20, 36)
WHEN  eid% 5 = 4 THEN conv(floor(rand() * 99999999999999), 20, 36)
END as public_key
FROM employeelist emp 
WHERE eid > 90 AND eid <= 120;

-- # create a view for p3_employee for prodcut with all feature disabled. (basic email)
-- SELECT count(eid) -- 29
CREATE OR REPLACE view p5_employee_view AS 
SELECT eid, firstname, lastname, email_id, folder, status
FROM employeelist emp 
WHERE  eid > 120 AND eid <= 150;

-- ##########
-- # v_forward_msg(eid, forwardaddr)
-- ##########
CREATE OR REPLACE view p1_forward_msg_view as
SELECT eid, email2 AS forwardaddr
FROM employeelist
WHERE eid <= 30
order by eid;

update p1_forward_msg_view
set forwardaddr= substring('abcdefghijklmnopqrstuvwxyz', rand()*26+1, 1)
where forwardaddr=NULL;

CREATE OR REPLACE view p4_forward_msg_view as
SELECT eid, email2 AS forwardaddr
FROM employeelist
WHERE eid > 90 AND eid <= 120
order by eid;

update p4_forward_msg_view
set forwardaddr= substring('abcdefghijklmnopqrstuvwxyz', rand()*26+1, 1)
where forwardaddr=NULL;


-- ##########
-- # v_remail_msg(eid, pseudonym, presCond)
-- ##########
CREATE OR REPLACE view p2_remail_msg_view as 
SELECT eid,  concat(substring('ABCDEFGHIJKLMNOPQRSTUVWXYZ', rand()*26+1, 1),
              substring('abcdelhio', rand()*9+1, 1),
              substring('abcdelhio', rand()*9+1, 1),
              substring('abcdefghijklmnopqrstuvwxyz', rand()*26+1, 1)
             ) as pseudonym
FROM employeelist
where eid > 30 AND eid <= 60
order by eid;

CREATE OR REPLACE view p4_remail_msg_view as 
SELECT eid,  concat(substring('ABCDEFGHIJKLMNOPQRSTUVWXYZ', rand()*26+1, 1),
              substring('abcdelhio', rand()*9+1, 1),
              substring('abcdelhio', rand()*9+1, 1),
              substring('abcdefghijklmnopqrstuvwxyz', rand()*26+1, 1)
             ) as pseudonym
FROM employeelist
where eid > 90 AND eid <= 120
order by eid;

-- ##########
-- # filter_msg_view(eid, suffix)
-- ##########
-- CREATE OR REPLACE view filter_msg_view as
-- SELECT 1 as eid , "pgn.com" as suffix;
CREATE OR REPLACE view p1_filter_msg_view as
SELECT eid,
CASE
WHEN  eid% 3 = 0 THEN "pgn.com"
WHEN  eid% 3 = 1 THEN "linkedin.com"
WHEN  eid% 3 = 2 THEN "example.com"
END as suffix
FROM employeelist
WHERE eid <= 30 ;

CREATE OR REPLACE view p4_filter_msg_view as
SELECT eid,
CASE
WHEN  eid% 3 = 0 THEN "pgn.com"
WHEN  eid% 3 = 1 THEN "linkedin.com"
WHEN  eid% 3 = 2 THEN "example.com"
END as suffix
FROM employeelist
WHERE eid > 90 AND eid <= 120;

-- ##########
-- # v_mailhost(eid, username, mailhost, presCond)
-- ##########
CREATE OR REPLACE view p3_mailhost_view as 
SELECT eid, 
SUBSTRING(email_id, 1, LOCATE('@', email_id) - 1) AS username,
CASE
WHEN  eid% 3 = 0 THEN "phoenix_host"
WHEN  eid% 3 = 1 THEN "corvallis_host"
WHEN  eid% 3 = 2 THEN "seattle_host"
END AS mailhost 
FROM employeelist
WHERE  eid > 60 AND eid <= 90;

CREATE OR REPLACE view p4_mailhost_view as 
SELECT eid, 
SUBSTRING(email_id, 1, LOCATE('@', email_id) - 1) AS username,
CASE
WHEN  eid% 3 = 0 THEN "phoenix_host"
WHEN  eid% 3 = 1 THEN "corvallis_host"
WHEN  eid% 3 = 2 THEN "seattle_host"
END AS mailhost 
FROM employeelist
WHERE  eid > 90 AND eid <= 120;

-- ##########
-- # v_auto_msg(eid, subject, body)
-- ##########
-- # eid should be in p3 and p4
CREATE OR REPLACE view p3_auto_msg_view as 
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
WHERE  eid > 60 AND eid <= 90 ;

CREATE OR REPLACE view p4_auto_msg_view as 
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
WHERE  eid > 90 AND eid <= 120 ;

-- ##########
-- # v_alias(eid, email, nickname, presCond)
-- ##########
CREATE OR REPLACE view p3_alias_view as 
select eid, email_id, SUBSTRING_INDEX( email_id,'.',1) as nickname
FROM employeelist
WHERE  eid > 60 AND eid <= 90
order by eid;

CREATE OR REPLACE view p4_alias_view as 
select eid, email_id, SUBSTRING_INDEX( email_id,'.',1) as nickname
FROM employeelist
WHERE  eid > 90 AND eid <= 120
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
(SELECT msg.*,  false as is_system_notification, false as is_forward_msg
FROM message msg 
inner join p1_employee_view emp on msg.sender = emp.email_id
where subject not like "Delivery Status Notification%" and
      subject not like "FW: %" and
      subject not like "Out of Office AutoReply:%")
union 
(
select msg.*, true as is_system_notification, false as is_forward_msg
from message msg
inner join p1_employee_view emp on msg.sender = emp.email_id
where subject like "Delivery Status Notification%")
union
(select msg.*, false as is_system_notification, true as is_forward_msg
from message msg
inner join p1_employee_view emp on msg.sender = emp.email_id
where subject like "FW: %");

CREATE OR REPLACE VIEW p1_recipientinfo_view AS
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"forwardmsg and filtermsg" AS prescond
FROM p1_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p1_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"signature and encrypt and remailmsg" AS prescond
FROM p1_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p2_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"addressbook and autoresponder and mailhost and encrypt and signature" AS prescond
FROM p1_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p3_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"signature and addressbook and filtermsg and autoresponder and forwardmsg and mailhost and encrypt and remailmsg" AS prescond
FROM p1_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p4_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"true" AS prescond
FROM p1_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p5_employee_view emp on rec.rvalue = emp.email_id
);

# SELECT count(mid) -- 25139
# p3_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_from_remailer) 
-- CREATE OR REPLACE view p2_message_view AS 
-- SELECT msg.*,  false as is_system_notification, 
-- CASE    
-- WHEN  emp.verification_key is NULL THEN false   
-- WHEN  emp.verification_key is not NULL THEN true
-- END AS is_signed,
-- CASE
-- WHEN  emp.public_key is not Null THEN true   
-- else  false
-- END AS is_encrypted
-- FROM message msg 
-- inner join p2_employee_view emp on msg.sender = emp.email_id

# SELECT count(mid) -- 2988 (not 25139 because both sender and recipient should be the user of privacy email)
# p3_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_from_remailer) 
CREATE OR REPLACE view p2_message_view AS 
(SELECT msg.*,  false as is_system_notification, 
CASE    
WHEN  emp.verification_key is NULL THEN false   
WHEN  emp.verification_key is not NULL THEN true
END AS is_signed,
CASE
WHEN  emp.public_key is not Null THEN true   
WHEN  emp.public_key is Null THEN false   
END AS is_encrypted
FROM message msg 
inner join p2_employee_view emp on msg.sender = emp.email_id
where subject not like "Delivery Status Notification%"
and subject not like "FW: %"
and subject not like "Out of Office AutoReply:%")
union
(SELECT msg.*,  true as is_system_notification, 
CASE    
WHEN  emp.verification_key is NULL THEN false   
WHEN  emp.verification_key is not NULL THEN true
END AS is_signed,
CASE
WHEN  emp.public_key is not Null THEN true   
WHEN  emp.public_key is Null THEN false   
END AS is_encrypted
FROM message msg 
inner join p2_employee_view emp on msg.sender = emp.email_id
where subject like "Delivery Status Notification%");

CREATE OR REPLACE VIEW p2_recipientinfo_view AS
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"forwardmsg and filtermsg" AS prescond
FROM p2_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p1_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"signature and encrypt and remailmsg" AS prescond
FROM p2_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p2_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"addressbook and autoresponder and mailhost and encrypt and signature" AS prescond
FROM p2_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p3_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"signature and addressbook and filtermsg and autoresponder and forwardmsg and mailhost and encrypt and remailmsg" AS prescond
FROM p2_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p4_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"true" AS prescond
FROM p2_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p5_employee_view emp on rec.rvalue = emp.email_id
);

-- #create a view for p3_message for prodcut focusing on group usage. 
# SELECT count(mid) -- 27952
-- # p3_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_autoresponse) 
CREATE OR REPLACE view p3_message_view AS 
(SELECT msg.* , false as is_system_notification, false as is_autoresponse,
CASE    
WHEN  emp.verification_key is NULL THEN false   
WHEN  emp.verification_key is not NULL THEN true
END AS is_signed,
CASE
WHEN  emp.public_key is not Null THEN true   
WHEN  emp.public_key is Null THEN false   
END AS is_encrypted
FROM message msg 
inner join p3_employee_view emp on msg.sender = emp.email_id
where subject not like "Delivery Status Notification%"
and subject not like "FW: %"
and subject not like "Out of Office AutoReply:%")
union
(SELECT msg.* , true as is_system_notification, false as is_autoresponse,
CASE    
WHEN  emp.verification_key is NULL THEN false   
WHEN  emp.verification_key is not NULL THEN true
END AS is_signed,
CASE
WHEN  emp.public_key is not Null THEN true   
WHEN  emp.public_key is Null THEN false   
END AS is_encrypted
FROM message msg 
inner join p3_employee_view emp on msg.sender = emp.email_id
where subject like "Delivery Status Notification%"
)
union
(SELECT msg.* , false as is_system_notification, true as is_autoresponse,
CASE    
WHEN  emp.verification_key is NULL THEN false   
WHEN  emp.verification_key is not NULL THEN true
END AS is_signed,
CASE
WHEN  emp.public_key is not Null THEN true   
WHEN  emp.public_key is Null THEN false   
END AS is_encrypted
FROM message msg 
inner join p3_employee_view emp on msg.sender = emp.email_id
where subject like "Out of Office AutoReply:%")
;

CREATE OR REPLACE VIEW p3_recipientinfo_view AS
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"forwardmsg and filtermsg" AS prescond
FROM p3_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p1_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"signature and encrypt and remailmsg" AS prescond
FROM p3_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p2_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"addressbook and autoresponder and mailhost and encrypt and signature" AS prescond
FROM p3_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p3_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"signature and addressbook and filtermsg and autoresponder and forwardmsg and mailhost and encrypt and remailmsg" AS prescond
FROM p3_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p4_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"true" AS prescond
FROM p3_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p5_employee_view emp on rec.rvalue = emp.email_id
);

-- #create a view for p4_message for prodcut focusing on all feauture enabled. 
-- SELECT count(distinct msg.mid) -- 20138
# p3_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_from_remailer, is_autoresponse, is_forward_msg) 
CREATE OR REPLACE view p4_message_view AS 
(SELECT msg.* , false as is_system_notification, 
CASE    
WHEN  emp.verification_key is NULL THEN false   
WHEN  emp.verification_key is not NULL THEN true
END AS is_signed,
CASE
WHEN  emp.public_key is not Null THEN true   
WHEN  emp.public_key is Null THEN false   
END AS is_encrypted, 
false as is_autoresponse,
false as is_forward_msg
FROM message msg 
inner join p4_employee_view emp on msg.sender = emp.email_id
where subject not like "Delivery Status Notification%"
and subject not like "FW: %"
and subject not like "Out of Office AutoReply:%")
union
(SELECT msg.* , true as is_system_notification, 
CASE    
WHEN  emp.verification_key is NULL THEN false   
WHEN  emp.verification_key is not NULL THEN true
END AS is_signed,
CASE
WHEN  emp.public_key is not Null THEN true   
WHEN  emp.public_key is Null THEN false   
END AS is_encrypted, 
false as is_autoresponse,
false as is_forward_msg
FROM message msg 
inner join p4_employee_view emp on msg.sender = emp.email_id
where subject like "Delivery Status Notification%"
)
union
(SELECT msg.* , false as is_system_notification, 
CASE    
WHEN  emp.verification_key is NULL THEN false   
WHEN  emp.verification_key is not NULL THEN true
END AS is_signed,
CASE
WHEN  emp.public_key is not Null THEN true   
WHEN  emp.public_key is Null THEN false   
END AS is_encrypted, 
true as is_autoresponse,
false as is_forward_msg
FROM message msg 
inner join p4_employee_view emp on msg.sender = emp.email_id
where subject like "Out of Office AutoReply:%")
union
(SELECT msg.* , false as is_system_notification, 
CASE    
WHEN  emp.verification_key is NULL THEN false   
WHEN  emp.verification_key is not NULL THEN true
END AS is_signed,
CASE
WHEN  emp.public_key is not Null THEN true   
WHEN  emp.public_key is Null THEN false   
END AS is_encrypted, 
false as is_autoresponse,
true as is_forward_msg
FROM message msg 
inner join p4_employee_view emp on msg.sender = emp.email_id
where subject like "FW: %")
;

CREATE OR REPLACE VIEW p4_recipientinfo_view AS
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"forwardmsg and filtermsg" AS prescond
FROM p4_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p1_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"signature and encrypt and remailmsg" AS prescond
FROM p4_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p2_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"addressbook and autoresponder and mailhost and encrypt and signature" AS prescond
FROM p4_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p3_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"signature and addressbook and filtermsg and autoresponder and forwardmsg and mailhost and encrypt and remailmsg" AS prescond
FROM p4_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p4_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"true" AS prescond
FROM p4_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p5_employee_view emp on rec.rvalue = emp.email_id
);

# SELECT count(distinct msg.mid) -- 12434
CREATE OR REPLACE view p5_message_view AS 
(SELECT msg.* , false as is_system_notification
FROM message msg 
inner join p5_employee_view emp on msg.sender = emp.email_id
where subject not like "Delivery Status Notification%" and
      subject not like "FW: %" and
      subject not like "Out of Office AutoReply:%")
union 
(
select msg.*, true as is_system_notification
from message msg
inner join p5_employee_view emp on msg.sender = emp.email_id
where subject like "Delivery Status Notification%");

CREATE OR REPLACE VIEW p5_recipientinfo_view AS
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"forwardmsg and filtermsg" AS prescond
FROM p5_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p1_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"signature and encrypt and remailmsg" AS prescond
FROM p5_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p2_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"addressbook and autoresponder and mailhost and encrypt and signature" AS prescond
FROM p5_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p3_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"signature and addressbook and filtermsg and autoresponder and forwardmsg and mailhost and encrypt and remailmsg" AS prescond
FROM p5_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p4_employee_view emp on rec.rvalue = emp.email_id
)
union
(SELECT rec.rid, rec.mid, rec.rtype, rec.rvalue, 
"true" AS prescond
FROM p5_message_view msg 
inner join recipientinfo rec on msg.mid = rec.mid
inner join p5_employee_view emp on rec.rvalue = emp.email_id
);



