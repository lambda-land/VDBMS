-- | Translated SQL Query of autoresponder <remailmsg<Q1,Q3>, Empty>

(SELECT msg.sender as sendTo, msg.subject as re, auto.subject,  auto.body, concat ("remailmsg", " AND ", "autoresponder") as presCond
FROM v_message msg
inner join v_recipientinfo rec on msg.mid = rec.mid 
inner join v_employee emp on rec.rvalue = emp.email_id
inner join v_auto_msg auto on auto.eid = emp.eid
Where  msg.mid =  1082 and msg.is_from_remailer = False  )

union all 

(SELECT msg.sender as sendTo, msg.subject as re, auto.subject,  auto.body, concat ("NOT remailmsg", " AND ", "autoresponder") as presCond
FROM v_message msg
inner join v_recipientinfo rec on msg.mid = rec.mid 
inner join v_employee emp on rec.rvalue = emp.email_id
inner join v_auto_msg auto on auto.eid = emp.eid
Where  msg.mid =  1082 )





-- | Q1: if is_remail is true, then not auto-reply msg; else auto-reply.
-- SELECT msg.sender as sendTo, msg.subject as re, auto.subject,  auto.body
-- FROM v_message msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid 
-- inner join v_employee emp on rec.rvalue = emp.email_id
-- inner join v_auto_msg auto on auto.eid = emp.eid
-- Where  msg.mid =  1082 and msg.is_from_remailer = False  

-- | Q2.  Normal auto reply
-- SELECT msg.sender as sendTo, msg.subject as re, auto.subject,  auto.body
-- FROM v_message msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid 
-- inner join v_employee emp on rec.rvalue = emp.email_id
-- inner join v_auto_msg auto on auto.eid = emp.eid
-- Where  msg.mid =  1082 

