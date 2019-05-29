-- | translated query for interaction between autoresponder and forwardmsg

(SELECT  msg.sender as originator,  rec.rvalue as receipientAddr, msg.subject, forwardAddr, concat ("forwardmsg", " AND ", "autoresponder") as presCond
FROM v_message msg
inner join v_recipientinfo rec on msg.mid = rec.mid 
inner join v_employee emp on rec.rvalue = emp.email_id 
inner join v_forward_msg fmsg on fmsg.eid = emp.eid
where msg.mid = 9138 )

union all 

(SELECT  NULL as originator, rec.rvalue as receipientAddr, msg.subject, forwardAddr, concat (" forwardmsg", " AND ", "(NOT autoresponder)") as presCond
FROM v_message msg
inner join v_recipientinfo rec on msg.mid = rec.mid 
inner join v_employee emp on rec.rvalue = emp.email_id 
inner join v_forward_msg fmsg on fmsg.eid = emp.eid
where msg.mid = 9138	)





-- | standing in the situation where we call forward function 
-- | Q1 
--   forwarded message includes intact sender line and auto reply to originator-- 
--   then, the auto reply subject will reply to originator instead of rec.rvalue 
-- SELECT  msg.sender as originator,  msg.subject, forwardAddr
-- FROM v_message msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid 
-- inner join v_employee emp on rec.rvalue = emp.email_id 
-- inner join v_forward_msg fmsg on fmsg.eid = emp.eid
-- where msg.mid = 9138 

-- | Q2
--   * get the forward address of the recipient 
-- SELECT  rec.rvalue as receipientAddr, msg.subject, forwardAddr
-- FROM v_message msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid 
-- inner join v_employee emp on rec.rvalue = emp.email_id 
-- inner join v_forward_msg fmsg on fmsg.eid = emp.eid
-- where msg.mid = 9138 			

