-- | translated query for interaction between encrypt and forwardmsg

-- | no notification in real haskell Query
(SELECT  rec.rvalue as recipientAddr, public_key, forwardAddr, concat ("received an message in", rec.rvalue) as notification,  concat("encrypt", " AND", "forwardmsg") as presCond
FROM v_message msg
inner join v_recipientinfo rec on msg.mid = rec.mid 
inner join v_employee emp on rec.rvalue = emp.email_id 
inner join v_forward_msg fmsg on fmsg.eid = emp.eid
where msg.mid = 9138 and public_key is not NULL) 

union all 

(SELECT rec.rvalue as recipientAddr, public_key, NULL as forwardAddr, NULL as notification, concat("encrypt", " AND", "(NOT forwardmsg)") as presCond
FROM v_message msg
inner join v_recipientinfo rec on msg.mid = rec.mid 
inner join v_employee emp on rec.rvalue = emp.email_id 
where msg.mid = 9138)

union all 

(SELECT  rec.rvalue as recipientAddr, NULL as public_key, forwardAddr, NULL as notification, concat("(NOT encrypt)", " AND", "forwardmsg") as presCond
FROM v_message msg
inner join v_recipientinfo rec on msg.mid = rec.mid 
inner join v_employee emp on rec.rvalue = emp.email_id 
inner join v_forward_msg fmsg on fmsg.eid = emp.eid
where msg.mid = 9138)

-- | Q1 
--   * receive an encrypted message in original email address and then send the notification to the forward address
-- SELECT  rec.rvalue as recipientAddr, public_key, forwardAddr, concat ("received an encrypted message in", rec.rvalue) as notification
-- FROM v_message msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid 
-- inner join v_employee emp on rec.rvalue = emp.email_id 
-- inner join v_forward_msg fmsg on fmsg.eid = emp.eid
-- where msg.mid = 9138

-- | Q2 
-- SELECT rec.rvalue as recipientAddr, public_key
-- FROM v_message msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid 
-- inner join v_employee emp on rec.rvalue = emp.email_id 
-- where msg.mid = 9138

-- | Q3
--   * get the forward address of the recipient 
-- SELECT  rec.rvalue as recipientAddr, forwardAddr
-- FROM v_message msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid 
-- inner join v_employee emp on rec.rvalue = emp.email_id 
-- inner join v_forward_msg fmsg on fmsg.eid = emp.eid
-- where msg.mid = 9138
