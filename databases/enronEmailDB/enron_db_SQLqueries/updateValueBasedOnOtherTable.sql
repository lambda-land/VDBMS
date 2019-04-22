-- select a.* , b.statusinsignature
-- from v_employee a, signatureTable b
-- where 


-- update v_employee 
-- inner join signature_table 
-- on v_employee.eid = signature_table.eid 
-- set v_employee.sign = signature_table.statusinsignature
-- where v_employee.sign is not null -- and other conditions you might want


update v_employee 
inner join signature
on v_employee.eid = signature.eid 
set v_employee.sign = signature.statusinsignature
where v_employee.sign is not null -- and other conditions you might want


