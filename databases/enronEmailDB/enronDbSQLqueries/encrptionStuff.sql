

-- create view encryptedEmployee_view as 
-- select * from v_employee
-- where eid >=125


-- update encryptedEmployee_view 
-- set encryptedEmployee_view.public_key = conv(floor(rand() * 99999999999999), 20, 36)
-- where encryptedEmployee_view.public_key is null -- and other conditions you might want

update v_employee
inner join  encryptedEmployee_view
on v_employee.eid = encryptedEmployee_view.eid
set v_employee.public_key = conv(floor(rand() * 99999999999999), 20, 36)
where v_employee.public_key is null -- and other conditions you might want