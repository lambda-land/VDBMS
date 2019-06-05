
-- | Q1: find the loop from email_id and forwardAddr
SELECT *
FROM v_employee emp 
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