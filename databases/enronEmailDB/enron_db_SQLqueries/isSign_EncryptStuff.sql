
-- create view recipientPublicKey as
-- SELECT emp.eid, r.mid, r.rvalue, public_key
-- FROM recipientinfo r
-- inner join v_employee emp on r.rvalue = emp.email_id

-- select *
-- from message msg 
-- inner join v_employee emp
-- on emp.email_id = msg.sender
-- inner join recipientPublicKey rec
-- on rec.mid = msg.mid


-- alter table v_employee add index index_11(email_id);-- 
-- alter table message add index index_22(sender);
-- alter table recipientpublickeyTable add index index_33(mid);
-- alter table message add index index_44 (mid);




create view message_view_useIndex as 
select msg.*,
CASE    
WHEN  emp.sign is NULL THEN false   
WHEN  emp.sign is not NULL THEN true
END AS is_sign,
CASE
WHEN  emp.public_key is not Null and rec.public_key is not NULL THEN true   
else  false
END AS is_encrypyt 
from message msg 
inner join v_employee emp
on emp.email_id = msg.sender
inner join recipientpublickeyTable rec
on rec.mid = msg.mid
