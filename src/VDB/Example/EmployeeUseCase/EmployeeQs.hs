-- | vqs for employee database.
module VDB.Example.EmployeeUseCase.EmployeeQs where

import Prelude hiding (Ordering(..))

import VDB.Algebra
import qualified VDB.Condition as C
import qualified VDB.FeatureExpr as F
import VDB.Type
import VDB.Name
import VDB.Variational
import VDB.Example.EmployeeUseCase.EmployeeSchema

import Database.HDBC 
-- import Data.Time.LocalTime
import Data.Time.Calendar

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

newtype QueryT = QueryT String
  deriving (Show, Eq)

-- | attaches the feature expression true to an attribute. 
trueAtt :: Attribute -> Opt Attribute
trueAtt a = (F.Lit True, a)

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
--            prj_(empno, hiredate, salary) 
--                empacct join_(title=title) job)
-- note:
-- the year 1991 is included in variants v3, v4, and v5. we only
-- write the query for these variants for a fair comparison against
-- prima.
-- classification: 3-0-2-1
empVQ1 :: Algebra
empVQ1 = Proj [trueAtt salary] $
  Sel (C.And empCond
             yearCond)
  (Proj [trueAtt empno, trueAtt hiredate, trueAtt salary] $ 
    Sel (C.Comp EQ (C.Attr title) (C.Attr title)) $ SetOp Prod (TRef empacct) (TRef job))

empVQ1T :: QueryT
empVQ1T = QueryT $ 
  "SELECT salary" ++
  "FROM (SELECT empno, hiredate, salary" ++
        "FROM empacct INNER JOIN job)" ++
  "WHERE empNo = 10004 AND 1991-01-01 < hiredate AND hiredate < 1992-01-01"

-- | the year 1991 condition
yearCond :: C.Condition
yearCond = C.And (C.Comp GT (C.Val $ SqlLocalDate $ ModifiedJulianDay 19910101) (C.Attr hiredate))
                 (C.Comp LT (C.Attr hiredate) (C.Val $ SqlLocalDate $ ModifiedJulianDay 19920101))

-- | employee id = 10004 condition
empCond :: C.Condition
empCond = C.Comp EQ (C.Attr empno) (C.Val $ SqlInt32 10004)

-- more optimized based on relational alg opt rules. prj and sel place
-- have been exchanged. check translations of them to see if they return
-- the same query.
-- classification: 3-0-2-1
empVQ1' :: Algebra
empVQ1' = Proj [trueAtt salary] $
  Proj [trueAtt empno, trueAtt hiredate, trueAtt salary] $ 
    Sel (C.And empCond
               yearCond) $
    Sel (C.Comp EQ (C.Attr title) (C.Attr title)) $ SetOp Prod (TRef empacct) (TRef job)    

-- more optimized based on sel_c sel_c' == sel_{c and c'}
-- classification: 3-0-2-1
empVQ1'' :: Algebra
empVQ1'' = Proj [trueAtt salary] $
  Proj [trueAtt empno, trueAtt hiredate, trueAtt salary] $ 
    Sel (empCond
         `C.And` yearCond
         `C.And` (C.Comp EQ (C.Attr title) (C.Attr title))) $ SetOp Prod (TRef empacct) (TRef job)    

-- the naive query of empVQ1:
--            v3 or v4 <prj_salary (sel_(empNo=10004, 1991-01-01<hiredate<1992-01-01)
--                                       prj_(empno, hiredate, salary) 
--                                            empacct join_(title=title) job),
--                      prj_salary (sel_(empNo=10004, 1991-01-01<hiredate<1992-01-01) job)>
-- classification: 3-1-2-1
empVQ1naive :: Algebra
empVQ1naive = AChc (F.Or empv3 empv4)
        (Proj [trueAtt salary] $
              Sel (C.And empCond
                         yearCond) $
                  Proj [trueAtt empno, trueAtt hiredate, trueAtt salary] $ 
                       Sel (C.Comp EQ (C.Attr title) (C.Attr title)) $ SetOp Prod (TRef empacct) (TRef job))
        (Proj [trueAtt salary] $
              Sel (C.And empCond
                         yearCond)
                  (TRef job))

-- intent: return the managers (of department d001) on
--         the year 1991.
-- query:
-- prj_managerno (sel_(1991-01-01<hiredate<1992-01-01 and deptno = d001)
--                 empacct join_(managerno=empno) dept)
-- note:
-- the naive and manually optimized queries are basically the same.
-- classification: 3-0-2-1
empVQ2 :: Algebra
empVQ2 = Proj [trueAtt managerno] $
  Sel ((C.Comp EQ (C.Attr deptno) (C.Val $ SqlInt32 001))
       `C.And` yearCond
       `C.And` (C.Comp EQ (C.Attr empno) (C.Attr managerno))) $
      SetOp Prod (TRef empacct) (TRef dept)

empVQ2T :: QueryT
empVQ2T = QueryT $
  "SELECT managerno" ++
  "FROM empacct INNER JOIN dept ON managerno = empNo" ++
  "WHERE deptno = 001 AND 1991-01-01 < hiredate AND hiredate < 1992-01-01"

-- classification: 5-3-2-1
empVQ2naive :: Algebra
empVQ2naive = AChc empv3 empVQ2 (AChc empv4 empVQ2 $ AChc empv5 empVQ2 Empty)

-- intent: find all managers that the employee 1004 worked with,
--         on the year 1991. 
-- query:
-- prj_managerno (dept join_(deptno=deptno)
--                prj_deptno (sel_(empNo=10004, 1991-01-01<hiredate<1992-01-01) empacct))
-- note:
-- the naive and manually optimized queries are basically the same.
-- classification: 3-0-2-1
empVQ3 :: Algebra
empVQ3 = Proj [trueAtt managerno] $
  Sel (C.Comp EQ (C.Attr deptno) (C.Attr deptno)) $
      SetOp Prod (TRef dept) $
                 Proj [trueAtt deptno] $
                      Sel ((C.Comp EQ (C.Attr deptno) (C.Val $ SqlInt32 001))
                          `C.And` yearCond) $
                          TRef empacct

empVQ3T :: QueryT
empVQ3T = QueryT $
  "SELECT managerno" ++
  "FROM dept as t0, " ++
                  "(SELECT deptno" ++
                  " FROM empacct" ++
                  " WHERE deptno = 001 AND 1991-01-01 < hiredate AND hiredate < 1992-01-01) as t1" ++
  "WHERE t0.deptno = t1.deptno"

-- ASK Eric: should I consider the first two variants? I think I should! YES!
-- classification: 5-3-2-1
empVQ3naive :: Algebra
empVQ3naive = AChc empv3 empVQ3 (AChc empv4 empVQ3 $ AChc empv5 empVQ3 Empty)

-- intent: find all salary values of managers in all history,
--         during the period of manager appointment. (the periods
--         of salary and manager appointment need to overlap).
--         answer using data valid on the year 1991.
-- query:
-- prj_salary (((sel_(1991-01-01<hiredate<1992-01-01) empacct)
--              join_(managerno = empno) dept) join_(title = title) job)
-- note: 
-- check to see if the join only occurs for valid variants!!
-- i.e. ... join dept is only valid for v3, v4, and v5. 
-- and ... join job is not valid for v5.
-- classification: 3-0-3-2
empVQ4 :: Algebra
empVQ4 = Proj [trueAtt salary] $
  (Sel (C.Comp EQ (C.Attr title) (C.Attr title))
       (SetOp Prod (Sel (C.Comp EQ (C.Attr managerno) (C.Attr empno))
                        (SetOp Prod (Sel yearCond
                                         (TRef empacct))
                                    (TRef dept)))
                   (TRef job)))

-- classification: 5-3-3-2
empVQ4naive :: Algebra
empVQ4naive = AChc (F.Or empv3 empv4)
  empVQ4
  (AChc empv5 
        (Proj [trueAtt salary] $
              Sel (C.Comp EQ (C.Attr managerno) (C.Attr empno)) $
                  SetOp Prod (Sel yearCond (TRef empacct)) (TRef dept))
        Empty)

-- intent: find the historical managers of department where the
--         employee 10004 worked, in all history. (the period 
--         of their appointments don't need to overlap.)
--         answer using data valid on the year 1991.
-- query:
-- prj_managerno
--     sel_(1991-01-01<hiredate<1992-01-01)
--         ((sel_(empno == 10004) empacct) join_(deptno = deptno) dept)
-- classification: 3-0-2-1
empVQ5 :: Algebra
empVQ5 = Proj [trueAtt managerno] $
  Sel (C.And yearCond 
             (C.Comp EQ (C.Attr deptno) (C.Attr deptno))) $
      SetOp Prod (Sel empCond (TRef empacct))
                 (TRef dept)

-- a less efficient vq in terms of relational algebra and sql.
-- since we're joining first and then applying the selection of
-- the particular employee. i.e.:
-- query:
-- prj_managerno
--     sel_(1991-01-01<hiredate<1992-01-01 and empno == 10004)
--         (empacct join_(deptno = deptno) dept)
-- classification: 3-0-2-1
empVQ5' :: Algebra
empVQ5' = Proj [trueAtt managerno] $
  Sel (C.And yearCond $
       C.And empCond 
             (C.Comp EQ (C.Attr deptno) (C.Attr deptno))) $
      SetOp Prod (TRef empacct)
                 (TRef dept)

-- classification: 5-3-2-1
empVQ5naive :: Algebra
empVQ5naive = AChc empv3 empVQ5 $ AChc empv4 empVQ5 $ AChc empv5 empVQ5 Empty

-- classification: 5-1-2-1
empVQ5naive' :: Algebra
empVQ5naive' = AChc (F.disjFexp [empv3, empv4, empv5]) empVQ5 Empty

-- intent: find all salary values of managers in all history.
--         (the periods of salary and manager appointment 
--         don't need to overlap.) 
--         answer using data valid on the year 1991.
-- query:
-- classification:
-- note: there's no way to get the period of manager appointment.
empVQ6 :: Algebra
empVQ6 = empVQ4

-- intent: for all managers that the employee 10004 worked with,
--         find all the departments that the manager managed.
--         (temporal join followed by non-temporal join)
--         (10004's and the manager's affiliation with a single 
--         department should overlap, but the manager's manager
--         position periods do not need to overlap, naturally.)
--         answer using data valid on the year 1991.
-- query:
-- prj_deptname
--     empvq3 join_(managerno = managerno) dept
-- classification: 3-0-2-2
empVQ7 :: Algebra
empVQ7 = Proj [trueAtt deptname] $
  Sel (C.Comp EQ (C.Attr managerno) (C.Attr managerno)) $
      SetOp Prod empVQ3 (TRef dept)

-- just wondering about!!
empVQ7naiveHelper :: Algebra
empVQ7naiveHelper = Proj [trueAtt deptname] $
  Sel (C.Comp EQ (C.Attr managerno) (C.Attr managerno)) $
      SetOp Prod empVQ3naive (TRef dept)

-- classification: 5-3-2-2
empVQ7naive :: Algebra
empVQ7naive = AChc empv3 empVQ7 $ AChc empv4 empVQ7 $ AChc empv5 empVQ7 Empty

-- note: Just wondering what happens!!!
empVQ7naive' :: Algebra
empVQ7naive' = AChc empv3 empVQ7naiveHelper $ 
                          AChc empv4 empVQ7naiveHelper $ 
                                     AChc empv5 empVQ7naiveHelper Empty


-- intent: for all managers, find all managers in the department
--         that he/she worked in. (two worked during the same
--         period)
--         (non-temporal join followed by temporal-join)
--         answer using data valid o the year 1991.
-- query:
-- classification:
empVQ8 :: Algebra
empVQ8 = undefined

-- 
-- Q9-Q16 is a relaxation of Q1-Q8, in terms of period.
-- 

-- intent: return the salary values of the emp 10004 on 
--         1991-01-01 or after. 
-- query:
-- classification:
empVQ9 :: Algebra
empVQ9 = undefined

-- intent: return the managers (of department d001) on
--         1991-01-01 or after.
-- query:
-- classification:
empVQ10 :: Algebra
empVQ10 = undefined

-- intent: find all managers that employee 10004 worked with,
--         with overlapping period. answer using data valid 
--         on or after 1991-01-01.
-- query:
-- classification:
empVQ11 :: Algebra
empVQ11 = undefined

-- intent: find all salary values of managers in all history.
--         (the periods of salary and manager appointment need
--         to overlap) answer using data valid on or after
--         1991-01-01.
-- query:
-- classification:
empVQ12 :: Algebra
empVQ12 = undefined

-- intent: find the historical managers of department where
--         the employee 10004 worked, in all history.
--         (the period of their appointments don't need to 
--         overlap.) answer using data valid on or after
--         1991-01-01.
-- query:
-- classification:
empVQ13 :: Algebra
empVQ13 = undefined

-- intent: find all salary values of managers in all history.
--         (the periods of salary and manager appointment don't
--         need to overlap)
--         answer using data valid on or after the year 1991.
-- query:
-- classification:
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
-- classification:
empVQ15 :: Algebra
empVQ15 = undefined

-- intent: for all managers, find all managers in the department 
--         that he/she worked in. (two worked during the same 
--         period) (non-temporal join followed by temporal-join)
--         answer using data valid on or after the year 1991.
-- query:
-- classification:
empVQ16 :: Algebra
empVQ16 = undefined

-------------------------------------------
-- analysis queries
-------------------------------------------

-- intent: for all employees get their salary
-- query: 
empVQ17 :: Algebra
empVQ17 = undefined


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
