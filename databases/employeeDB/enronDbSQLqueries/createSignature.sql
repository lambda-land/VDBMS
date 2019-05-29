alter view signature as 
select eid, 
CASE    
WHEN  status is NULL THEN  concat(firstname, " ", lastname)
WHEN status = "N/A" THEN concat(firstname, " ", lastname)
WHEN  status is not NULL THEN concat(firstname, " ", lastname, '    |    ', status, "   ", email_id)
END AS statusinsignature
from employeelist 
