-- | vqs for employee database.
module VDB.Example.EmployeeUseCase.EmployeeQs where

import VDB.Algebra
import qualified VDB.Condition as C
import qualified VDB.FeatureExpr as F
import VDB.Type

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
-- first set of quesries:
-- taken from the prima paper, adjusted to the employee database. 
-- e.g. instead of year 2003, we have year 1991, etc. 
-- can be used for comparison in terms of expressiveness and brevity.
-- 

-- intent: return the salary value of the emp 10004
--         on the year 1991.
-- query: 
-- prj_salary 
--    (sel_(empNo=10004, 1991-01-01<hiredate<1992-01-01)
--       v1 < (prj_(empno,hiredate,title) eng UNION other)
--             join_(title=title) job, 
--            prj_(empno, hiredate, salary) 
--                empacct join_(title=title) job>)
-- ASK ERIC: should it be empv1 or empv1 and not ...?
empVQ1subq1, empVQ1subq2, empVQ1subq3, empVQ1subq4 :: Algebra

empVQ1 :: Algebra
empVQ1 = Proj [(Lit True, salary)]
  Sel (C.And (Comp EQ (Attr empno) (Val $ SqlInt32 10004))
      (C.And (Comp GT (C.Val $ SqlLocalDate '1991-01-01') (Attr hiredate))
             (Comp LT (Attr hiredate) (C.Val $ SqlLocalDate '1992-01-01'))))
  (AChc empv1 
    ()
    ())

-- intent: return the managers (of department d001) on
--         the year 1991.
-- query:
empVQ2 :: Algebra
empVQ2 = undefined

-- intent: find all managers that the employee 1004 worked with,
--         on the year 1991. 
-- query:
empVQ3 :: Algebra
empVQ3 = undefined

-- intent: find all salary values of managers in all history,
--         during the period of manager appointment. (the periods
--         of salary and manager appointment need to overlap).
--         answer using data valid on the year 1991.
-- query:
empVQ4 :: Algebra
empVQ4 = undefined

-- intent: find the historical managers of department where the
--         employee 10004 worked, in all history. (the period 
--         of their appointments don't need to overlap.)
--         answer using data valid on the year 1991.
-- query:
empVQ5 :: Algebra
empVQ5 = undefined

-- intent: find all salary values of managers in all history.
--         (the periods of salary and manager appointment 
--         don't need to overlap.) 
--         answer using data valid on the year 1991.
-- query:
empVQ6 :: Algebra
empVQ6 = undefined

-- intent: for all managers that the employee 10004 worked with,
--         find all the departments that the manager managed.
--         (temporal join followed by non-temporal join)
--         (10004's and the manager's affiliation with a single 
--         department should overlap, but the manager's manager
--         position periods do not need to overlap, naturally.)
--         answer using data valid on the year 1991.
-- query:
empVQ7 :: Algebra
empVQ7 = undefined

-- intent: for all managers, find all managers in the department
--         that he/she worked in. (two worked during the same
--         period)
--         (non-temporal join followed by temporal-join)
--         answer using data valid o the year 1991.
-- query:
empVQ8 :: Algebra
empVQ8 = undefined

-- 
-- Q9-Q16 is a relaxation of Q1-Q8, in terms of period.
-- 

-- intent: return the salary values of the emp 10004 on 
--         1991-01-01 or after. 
-- query:
empVQ9 :: Algebra
empVQ9 = undefined

-- intent: return the managers (of department d001) on
--         1991-01-01 or after.
-- query:
empVQ10 :: Algebra
empVQ10 = undefined

-- intent: find all managers that employee 10004 worked with,
--         with overlapping period. answer using data valid 
--         on or after 1991-01-01.
-- query:
empVQ11 :: Algebra
empVQ11 = undefined

-- intent: find all salary values of managers in all history.
--         (the periods of salary and manager appointment need
--         to overlap) answer using data valid on or after
--         1991-01-01.
-- query:
empVQ12 :: Algebra
empVQ12 = undefined

-- intent: find the historical managers of department where
--         the employee 10004 worked, in all history.
--         (the period of their appointments don't need to 
--         overlap.) answer using data valid on or after
--         1991-01-01.
-- query:
empVQ13 :: Algebra
empVQ13 = undefined

-- intent: find all salary values of managers in all history.
--         (the periods of salary and manager appointment don't
--         need to overlap)
--         answer using data valid on or after the year 1991.
-- query:
empVQ14 :: Algebra
empVQ14 = undefined

-- intent: for all managers that the employee 10004 worked with, 
--         find all the departments that the manager managed.
--         (temporal join followed by non-temporal join)
--         (10004's and the manager's affiliation with a single
--         department should overlap, but the manager's manager 
--         position periods do not need to overlap, naturally.)
--         anwer using data valid on or after the year 1991.
-- query:
empVQ15 :: Algebra
empVQ15 = undefined

-- intent: for all managers, find all managers in the department 
--         that he/she worked in. (two worked during the same 
--         period) (non-temporal join followed by temporal-join)
--         answer using data valid on or after the year 1991.
-- query:
empVQ16 :: Algebra
empVQ16 = undefined


-- intent:
-- query:
-- empVQ4 :: Algebra
-- empVQ4 = undefined


-- intent:
-- query:
-- empVQ4 :: Algebra
-- empVQ4 = undefined


-- intent:
-- query:
-- empVQ4 :: Algebra
-- empVQ4 = undefined


-- intent:
-- query:


-- intent:
-- query:
