-- | Q1: find the loop (foward and remail)  in the remailer side
-- SELECT emp.eid, emp.email_id, forward.forwardAddr,remail.pseudonym
-- FROM v_employee emp
-- inner join v_forward_msg forward on forward.eid = emp.eid
-- inner join v_remail_msg remail on remail.eid = emp.eid 


-- | Translated v-query
SELECT emp.eid, emp.email_id, forward.forwardAddr,remail.pseudonym, concat("forwardmsg", " AND ", " remailmsg") as presCond
FROM v_employee emp
inner join v_forward_msg forward on forward.eid = emp.eid
inner join v_remail_msg remail on remail.eid = emp.eid 

