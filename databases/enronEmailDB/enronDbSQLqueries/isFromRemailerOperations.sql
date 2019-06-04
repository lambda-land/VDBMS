

-- alter table v_employee add index index_11(email_id);
-- alter table message add index index_22(sender);
-- alter table message add index index_44 (mid);

-- | count how many people in remail_msg send a message in DB => 23
-- select count( distinct emp.eid)
-- from v_message msg 
-- inner join v_employee emp on msg.sender = emp.email_id
-- inner join v_remail_msg remail on emp.eid = remail.eid 

-- | select all msg send by user who are enable the remail feature 
-- select *
-- from v_message msg 
-- inner join v_employee emp on msg.sender = emp.email_id
-- inner join v_remail_msg remail on emp.eid = remail.eid 

-- | messages that sender is enabled with remailer
-- create table remailerMsgTable as 
-- select msg.*
-- from v_message msg 
-- inner join v_employee emp on msg.sender = emp.email_id
-- inner join v_remail_msg remail on emp.eid = remail.eid 


-- UPDATE remailerMsgTable 
-- SET is_from_remailer = true

-- select count(distinct sender)
-- from remailerMsgTable

-- select * 
-- from remailerMsgTable

-- | update the is_from_remailer in v_message. if the sender is in the remail table 
-- UPDATE v_message
-- SET is_from_remailer = true 
-- where  v_message.mid in (
-- 	select  mid
--     from remailerMsgTable 
-- ) 

-- UPDATE v_message 
-- SET is_from_remailer =  false 
-- where is_from_remailer is NULL





