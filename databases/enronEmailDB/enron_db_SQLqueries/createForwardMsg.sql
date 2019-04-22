create table  v_forward_msg as 
select eid, email2 as forwardAddr
from employeelist
where eid>=75 and eid < 125