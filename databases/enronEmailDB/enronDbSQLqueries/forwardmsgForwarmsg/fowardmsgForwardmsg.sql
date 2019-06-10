
-- | Q1: find the loop from email_id and forwardAddr
-- SELECT emp.eid, emp.email_id, forward.forwardAddr
-- FROM v_employee emp
-- inner join v_forward_msg forward on forward.eid = emp.eid
-- where emp.email_id in ( 
-- 	SELECT forward.forwardAddr
--     from v_forward_msg forward )

-- | translated VQ
SELECT emp.eid, emp.email_id, forward.forwardAddr,  "forwardmsg" as presCond
FROM v_employee emp
inner join v_forward_msg forward on forward.eid = emp.eid
where emp.email_id in ( 
	SELECT forward.forwardAddr
    from v_forward_msg forward )

    
-- SELECT * 
-- FROM v_forward_msg

-- UPDATE  v_forward_msg


-- SET forwardAddr = "chris.dorland@enron.com"
-- WHERE eid = 148;

-- | 118 email_id : chris.dorland@enron.com forwardAddr: chris.stokley@enron.com
-- 148  email_id : chris.stokley@enron.com forwardAddrr: chris.dorland@enron.com 

-- select * 
-- from v_employee
-- where eid = 148