create view v_alias as 
select emp.eid, rec.rvalue, SUBSTRING_INDEX( rec.rvalue,'@',1) as nickname
from message msg 
	inner join  
        recipientInfo rec on msg.mid = rec.mid  
	inner join
		employeelist emp on emp.email_id = msg.sender