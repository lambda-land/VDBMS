-- | translated Query for the interaction between encrypt and remail 

(SELECT NULL as sender, rec.rvalue as recipientAddr, subject, public_key, NULL as pseudonym, concat("encrypt", " AND", "remailmsg") as presCond
FROM v_message  msg
inner join v_recipientinfo rec on msg.mid = rec.mid
inner join v_employee emp on emp.email_id = rec.rvalue 
where msg.mid = 9138)

union all 

(SELECT sender, rec.rvalue as recipientAddr, subject, public_key, NULL as pseudonym, concat("encrypt", " AND", "(NOT remailmsg)") as presCond
FROM v_message  msg
inner join v_recipientinfo rec on msg.mid = rec.mid
inner join v_employee emp on emp.email_id = rec.rvalue 
where msg.mid = 9138)

union all 

(SELECT sender, rec.rvalue as recipientAddr, subject, NULL as public_key, pseudonym, concat("( NOT encrypt) ", " AND", " remailmsg") as presCond
FROM v_message  msg
inner join v_recipientinfo rec on msg.mid = rec.mid
inner join v_employee emp on emp.email_id = rec.rvalue
inner join v_remail_msg rmsg on rmsg.eid = emp.eid 
where msg.mid = 9138)

union all 

(SELECT sender, rec.rvalue as recipientAddr, subject, NULL as public_key, NULL as pseudonym, concat("( NOT encrypt)", " AND", "(NOT remailmsg)") as presCond
FROM v_message  msg
inner join v_recipientinfo rec on msg.mid = rec.mid
inner join v_employee emp on emp.email_id = rec.rvalue
where msg.mid = 9138)



-- | Q1 : remove the sender's address from header line before encrypt 
-- SELECT rec.rvalue as recipientAddr, subject, public_key
-- FROM v_message  msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid
-- inner join v_employee emp on emp.email_id = rec.rvalue 
-- where msg.mid = 9138

-- | Q2
--   get public key
-- SELECT sender, rec.rvalue as recipientAddr, subject, public_key
-- FROM v_message  msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid
-- inner join v_employee emp on emp.email_id = rec.rvalue 
-- where msg.mid = 9138


-- | Q3 
-- get pseudony of sender from header
-- SELECT sender, rec.rvalue as recipientAddr, subject, pseudonym
-- FROM v_message  msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid
-- inner join v_employee emp on emp.email_id = rec.rvalue
-- inner join v_remail_msg rmsg on rmsg.eid = emp.eid 
-- where msg.mid = 9138

-- | Q4
-- get normal header and
-- SELECT sender, rec.rvalue as recipientAddr, subject
-- FROM v_message  msg
-- inner join v_recipientinfo rec on msg.mid = rec.mid
-- inner join v_employee emp on emp.email_id = rec.rvalue
-- where msg.mid = 9138

