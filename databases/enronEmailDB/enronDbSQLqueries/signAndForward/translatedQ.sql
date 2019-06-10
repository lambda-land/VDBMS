-- | translted query of interaction between signature and forwardmsg
(SELECT sender, subject, body, date, NULL as forwardAddr, concat("signature", " AND", "forwardmsg")
FROM v_message 
where mid = 9138)

union all 

(SELECT sender, subject, body, NULL as date, sign, NULL as forwardAddr, concat("signature", " AND ", "(NOT forwardmsg)") as presCond
FROM v_message msg
inner join v_employee emp on msg.sender = emp.email_id
where msg.mid = 9138)

union all 

(SELECT sender, subject, body, NULL as date, NULL as sign, forwardAddr, concat("(NOT signature)", " AND ", " forwardmsg") as presCond
FROM v_forward_msg  fmsg 
inner join v_employee emp on fmsg.eid = emp.eid
inner join v_recipientinfo rec on rec.rvalue = emp.email_id 
inner join v_message msg on msg.mid = rec.mid
where msg.mid = 9138)

union all 


(SELECT sender, subject, body, NULL as date, NULL as sign, NULL as forwardAddr, concat("(NOT signature)", " AND", "(NOT forwardmsg)") as presCond
FROM v_message 
where mid = 9138)

-- | Q1
-- SELECT sender, subject, body, date
-- FROM v_message 
-- where mid = 9138

-- | Q2
-- SELECT sender, subject, body, sign 
-- FROM v_message msg
-- inner join v_employee emp on msg.sender = emp.email_id
-- where msg.mid = 9138

--  | Q3
-- SELECT sender, subject, body, forwardAddr
-- FROM v_forward_msg  fmsg 
-- inner join v_employee emp on fmsg.eid = emp.eid
-- inner join v_recipientinfo rec on rec.rvalue = emp.email_id 
-- inner join v_message msg on msg.mid = rec.mid
-- where msg.mid = 9138

-- | Q4
-- SELECT sender, subject, body
-- FROM v_message 
-- where mid = 9138

