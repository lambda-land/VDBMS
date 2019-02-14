-- | vqs for employee database.
module VDB.Example.EmployeeUseCase.EmployeeQs where


-- keep in mind that the employee use demos deploying
-- every single version for the client of spl. so qs
-- must be st the software generated by spl is actually
-- using it. i.e. qs aren't being run in the test, instead
-- they're running in deployment step. or better yet 
-- you can imagine that different divisions of the company
-- are using different versions of it. so qs demo situations
-- that the user/software has some information need that 
-- needs to get data from different versions. keep in mind
-- that the user/software can definitely specify the version
-- they're requiring at the end, which just requires applying
-- configuration to the final result of a vq or getting the
-- plain q of a vq and then running it on the appropriate 
-- variant. 

-- 
