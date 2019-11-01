-- | vqs for employee database.
module VDBMS.UseCases.EmployeeUseCase.EmployeeQuery where

import VDBMS.QueryLang.RelAlg.Variational.Algebra
import VDBMS.UseCases.EmployeeUseCase.EmployeeSchema
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import qualified VDBMS.QueryLang.RelAlg.Variational.Condition as C
import VDBMS.UseCases.SmartConstructor
import VDBMS.DBMS.Value.CompOp
import Prelude hiding (Ordering(..))
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

--
-- * Constant values used for employee use cases
--

-- | the year 1991 condition
--   ModifiedJulianDay Int (Count days from 1858-11-17)
--   1991-01-01: ModifiedJulianDay 48257
--   1992-01-01: ModifiedJulianDay 48622
date19910101, date19920101 :: Day
date19910101 = ModifiedJulianDay 48257
date19920101 = ModifiedJulianDay 48622

-- | 1991-01-01 < hiredate < 1992-01-0
yearCond :: C.Condition 
yearCond = C.And (C.Comp GT (C.Val $ SqlLocalDate date19910101) (C.Att  hiredate))
                 (C.Comp LT (C.Att hiredate) (C.Val $ SqlLocalDate date19920101))

-- |  hiredate > 1991-01-01
yearAfterCond :: C.Condition 
yearAfterCond = C.Comp GT (C.Att hiredate) (C.Val $ SqlLocalDate date19910101) 

-- | employee id = 10004 condition
empCond :: C.Condition
empCond = C.Comp EQ (C.Att empno) (C.Val $ SqlInt32 10004)

empno_value :: SqlValue 
empno_value  = SqlInt32 10004

departno_value :: SqlValue
departno_value = SqlString "d001"

--
-- * Queries based on Prima paper
--

-- 1(Q1A). 
-- first set of quesries:
-- taken from the prima paper, adjusted to the employee database. 
-- e.g. instead of year 2003, we have year 1991, etc. 
-- 

-- intent: return the salary value of the emp 10004
--         on the year 1991. 
-- query: 
-- prj_salary 
--    (sel_(empNo=10004, 1991-01-01<hiredate<1992-01-01)
--                (empacct join_(title=title) job)
--
-- the variatonal query of empQ1:
-- * v-query considering 5 versions
--   v3 <empQ1, empty>
-- 
-- note:
-- the year 1991 is included in variants v3, v4, and v5. we only
-- write the query for these variants for a fair comparison against
-- prima.

empQ1T :: QueryT
empQ1T = QueryT $ 
  "SELECT salary" ++
  "FROM (SELECT empno, hiredate, salary" ++
        "FROM empacct INNER JOIN job)" ++
  "WHERE empNo = 10004 AND 1991-01-01 < hiredate AND hiredate < 1992-01-01"

empQ1 :: Algebra
empQ1 = Proj [trueAttr salary] $ genRenameAlgebra $
          Sel (VsqlCond (C.And empCond yearCond)) $ 
            genRenameAlgebra $ joinTwoRelation empacct job "title"

empVQ1 :: Algebra
empVQ1 = AChc empv3 empQ1 Empty

-- 2(Q1B). 
-- intent: return the managers (of department d001) on
--         the year 1991.
-- variational query:
--   v3 <empQ2, empty>
-- plain query(empQ2):
-- prj_managerno (sel_(1991-01-01<hiredate<1992-01-01 and deptno = d001)
--                 empacct join_(empno = managerno) dept)
-- Note:
-- 1. Attribute deptno only exist in v3,v4,v5.
empQ2T :: QueryT
empQ2T = QueryT $
  "SELECT managerno" ++
  "FROM empacct INNER JOIN dept ON managerno = empNo" ++
  "WHERE deptno = d001 AND 1991-01-01 < hiredate AND hiredate < 1992-01-01"

empQ2 :: Algebra
empQ2 = Proj [trueAttr managerno] $ genRenameAlgebra $ 
                  Sel (VsqlCond cond) $ genRenameAlgebra $ 
                  joinTwoRelation empacct dept "deptno"
      where cond = (C.Comp EQ (C.Att deptno) (C.Val departno_value)) `C.And ` yearCond

-- | VQ2 or VQ2naive, which one should use??
empVQ2 :: Algebra
empVQ2 = AChc empv3 empQ2 Empty

-- 3 (Q2A). 
-- intent: find all managers that the employee 10004 worked with,
--         on the year 1991. 
-- variational query:
--   v3 <empQ3, empty>
--
-- plain query(empQ3):
-- prj_managerno sel_(empNo=10004, 1991-01-01<hiredate<1992-01-01) 
--        (dept join_(deptno=deptno) empacct)
-- note:
-- the naive and manually optimized queries are basically the same.
empQ3T :: QueryT
empQ3T = QueryT $
  "SELECT managerno" ++
  "FROM empacct join dept on deptno" ++  
  "WHERE empno = 10004 AND 1991-01-01 < hiredate AND hiredate < 1992-01-01) as t1"

empQ3 :: Algebra
empQ3 = Proj [trueAttr managerno] $ genRenameAlgebra $ 
  Sel (VsqlCond ((yearCond `C.And` (C.Comp EQ (C.Att empno) (C.Val empno_value)) ))) $ genRenameAlgebra $ 
  joinTwoRelation empacct dept "deptno" 

-- | v3 or v4 or v5 <q3, empty>
empVQ3 :: Algebra
empVQ3 = AChc empv3 empQ3 Empty

-- 4(Q2B).
-- intent: find all salary values of managers in all history,
--         during the period of manager appointment. (the periods
--         of salary and manager appointment need to overlap).
--         answer using data valid on the year 1991.
-- * variational query:
--   v3 <empQ4, empty>
-- 
-- * palin query(empQ4):
--    prj_(managerno, salary) 
--     sel_(1991-01-01<hiredate<1992-01-01) 
--       (empacct join_(title = title) job join_(managerno = empno) dept)
--      
-- note: 
-- check to see if the join only occurs for valid variants!!
-- i.e. ... join dept is only valid for v3, v4, and v5. 
-- and ... join job is not valid for v5.
-- and there's no way to get the period of manager appointment.

empQ4:: Algebra
empQ4 = Proj [trueAttr managerno, trueAttr salary] $ genRenameAlgebra $ 
          Sel (VsqlCond yearCond) $ genRenameAlgebra $ 
          Join (genRenameAlgebra join_empacct_job) (genRenameAlgebra (tRef dept)) cond 
    where join_empacct_job = joinTwoRelation empacct job "title" 
          cond = C.Comp EQ (C.Att empno) (C.Att managerno)

empVQ4 :: Algebra
empVQ4 = AChc empv4 empQ4 Empty

-- 5(Q3A).
-- Intent: Find the historical managers of department where the employee 10004 worked, in all history. 
--         (The period of their appointments don't need to overlap.)
--         Answer using data valid on the year 1991.
-- Process: 1. find the departments where 10004 worked
--          2. get managerno from those departments 
-- 
-- * variational queries:
--   v3 <empQ5, empty> 
-- * plain queries(empQ5):
--       SELECT managerno
--       from dept
--       where deptno in 
--       (SELECT deptno 
--       FROM empacct
--       where empno = 10004 and 1991-01-01<hiredate<1992-01-01 )
--  =>
--       SELECT managerno
--       FROM  
--       (SELECT * 
--       FROM empacct natural join dept 
--       where empno = 10004 and 1991-01-01<hiredate<1992-01-01 ) 
empQ5 :: Algebra
empQ5 = Proj [trueAttr managerno] $ genRenameAlgebra $ 
          Sel (VsqlIn deptno sub) $ genRenameAlgebra $ 
            tRef dept  
      where sub = Proj [trueAttr deptno] $ genRenameAlgebra $ 
                    Sel (VsqlCond cond) $ genRenameAlgebra $ 
                    tRef empacct
            cond = (C.Comp EQ (C.Att empno) (C.Val empno_value)) `C.And` yearCond

empVQ5 :: Algebra
empVQ5 = AChc empv3 empQ5 Empty

--6(Q3B).
-- intent: find all salary values of managers in all history.
--         (the periods of salary and manager appointment 
--         don't need to overlap.) 
--         answer using data valid on the year 1991.
-- query:
-- 
-- note: there's no way to get the period of manager appointment.
empVQ6 :: Algebra
empVQ6 = empVQ4

-- 7(Q4A).
-- intent: For all managers that the employee 10004 with, find all the departments that the manager managed. 
--         (10004's and the manager's affiliation with a single department should overlap, but
--         the manager's manager position periods do not need to overlap, naturally.)
--         Answer using data valid on the year 1991.
-- Process: 1. get managers that 10005 with
--          2. get departments for those managers 
-- 
-- * variational queries:
--   v3  <empQ7, empty>
-- * plain queries for each version:
--      SELECT deptname 
--      from dept 
--      where managerno in 
--      (SELECT managerno 
--      FROM v3_empacct JOIN dept ON v3_empacct.deptno = dept.deptno
--      where empno = 10004 and 1991-01-01<hiredate<1992-01-01 ) 
--     ** subquery here is the same with empQ3
empQ7 :: Algebra
empQ7 = Proj [trueAttr deptname] $ genRenameAlgebra $ 
          Sel (VsqlIn managerno empQ3) $ genRenameAlgebra $ 
            tRef dept

-- | v3 or v4 or v5 <q2, empty>
empVQ7 :: Algebra
empVQ7 = AChc empv3 empQ7 Empty

-- 8(Q4B).
-- intent: For all managers, find all managers in the department that he/she worked in. (two worked during the same period)
--         (non-temporal join follwed by temporal-join)
--          Answer using data valid on the year 1991.
-- 
-- Process: Join the table empacct and dept and return the manager name and department name 
-- 
-- * variational queries:
-- * plain queries for each version:
--      SELECT name, deptname 
--      from emppact join dept on empno = managerno 
--      where 1991-01-01<hiredate<1992-01-01
-- Note: Two worked during same period, we consider it as two people hire at the same hiredate.
empQ8 :: Algebra
empQ8 = Proj [trueAttr name, trueAttr deptname] $ genRenameAlgebra $ 
          Sel (VsqlCond yearCond) $ genRenameAlgebra $ 
            Join (genRenameAlgebra (tRef empacct)) (genRenameAlgebra (tRef dept)) cond 
          where cond = C.Comp EQ (C.Att empno) (C.Att managerno)

empVQ8 :: Algebra
empVQ8 = AChc empv3 empQ8 Empty

-- 
-- Q9-Q16 is a relaxation of Q1-Q8, in terms of period.
-- 

-- 9(Q5A).
-- intent: return the salary values of the emp 10004 on 
--         1991-01-01 or after. 
-- 
-- plain query:
-- prj_salary 
--    (sel_(empNo=10004, hiredate>1991-01-01)
--            prj_(empno, hiredate, salary) 
--                empacct join_(title=title) job)
-- 
-- the variatonal query of empQ1:
-- * v-query considering 5 versions
--   (v3 or v4) < q1_v3v4, v5< q1_v5, empty>>>
-- * plain queries for each versiton 
--   q1_v3v4:
--     prj_salary 
--     (sel_(empNo=10004, hiredate>1991-01-01>))
--     (empacct join_(title=title) job)
--   q1_v5:
--      prj_salary
--     (sel_(empNo=10004, hiredate>1991-01-01))
--     empacct 
-- Variational query:
-- v3 or v4 <empQ9_v3v4, v5<empQ9_v5, empty> >
empQ9T :: QueryT
empQ9T = QueryT $ 
  "SELECT salary" ++
  "FROM (SELECT empno, hiredate, salary" ++
        "FROM empacct INNER JOIN job)" ++
  "WHERE empNo = 10004 AND hiredate > 1991-01-01"

empVQ9 :: Algebra
empVQ9 = AChc (F.Or empv3 empv4) empQ9_v3v4 $ AChc empv5 empQ9_v5 Empty
            where empQ9_v3v4 = Proj [trueAttr salary] $ genRenameAlgebra $
                                  Sel (VsqlCond (C.And empCond yearAfterCond)) $ 
                                   genRenameAlgebra $ joinTwoRelation empacct job "title"
                  empQ9_v5 = Proj [trueAttr salary] $ genRenameAlgebra $ 
                              Sel (VsqlCond (C.And empCond yearAfterCond)) $ genRenameAlgebra $ 
                                tRef empacct 

-- 10(Q5B). 
-- intent: return the managers (of department d001) on
--         1991-01-01 or after.
-- variational query:
--   v3 or v4 or v5 <q2, empty>
-- query:
--   prj_managerno (sel_(hiredate>1991-01-01and deptno = d001)
--                   empacct join_(managerno=empno) dept)
-- Note:
-- 1. Attribute deptno only exist in v3,v4,v5.
empQ10T :: QueryT
empQ10T = QueryT $
  "SELECT managerno" ++
  "FROM empacct INNER JOIN dept ON managerno = empNo" ++
  "WHERE deptno = d001 AND hiredate > 1991-01-01 "

empQ10 :: Algebra
empQ10 = Proj [trueAttr managerno] $ genRenameAlgebra $ 
                  Sel (VsqlCond cond) $ genRenameAlgebra $ 
                  joinTwoRelation empacct dept "deptno"
      where cond = (C.Comp EQ (C.Att deptno) (C.Val departno_value)) `C.And ` yearAfterCond

empVQ10 :: Algebra
empVQ10 = AChc (empv3 `F.Or` empv4 `F.Or` empv5) empQ10 Empty

-- 11(Q6A)
-- intent: find all managers that employee 10004 worked with,
--         with overlapping period. answer using data valid 
--         on or after 1991-01-01.
-- variational query:
--   v3 or v4 or v5 <q, empty>
-- query:
--   prj_managerno (sel_(empNo=10004, hiredate>1991-01-01) 
--             (dept join_(deptno=deptno) empacct))
empQ11T :: QueryT
empQ11T = QueryT $
  "SELECT managerno" ++
  "FROM empacct join dept on deptno" ++  
  "WHERE empno = 10004 AND hiredate > 1991-01-01"

empQ11 :: Algebra
empQ11 = Proj [trueAttr managerno] $ genRenameAlgebra $ 
  Sel (VsqlCond ((yearAfterCond `C.And` (C.Comp EQ (C.Att empno) (C.Val empno_value)) ))) $ genRenameAlgebra $ 
  joinTwoRelation empacct dept "deptno" 

empVQ11 :: Algebra
empVQ11 = AChc (empv3 `F.Or` empv4 `F.Or` empv5) empQ10 Empty

-- 12(Q6B)
-- intent: find all salary values of managers in all history.
--         (the periods of salary and manager appointment need
--         to overlap) answer using data valid on or after
--         1991-01-01.
-- * variational query:
--   v3 o v4<empQ12_v3v4, v5<empQ12_v5, empty>>
-- 
-- * palin query for each version:
--   * for v3, v4:
--    prj_(managerno, salary) 
--     sel_(hiredate>1991-01-01) 
--       (empacct join_(title = title) job join_(managerno = empno) dept) 
--   * for v5:
--    prj_(managerno, salary) 
--     sel_(hiredate>1991-01-01) 
--       (empacct join_( empno = managerno) dept)      
-- note: 
-- check to see if the join only occurs for valid variants!!
-- i.e. ... join dept is only valid for v3, v4, and v5. 
-- and ... join job is not valid for v5.
-- and there's no way to get the period of manager appointment.
empQ12_v3v4 :: Algebra
empQ12_v3v4 = Proj [trueAttr managerno, trueAttr salary] $ genRenameAlgebra $ 
          Sel (VsqlCond yearAfterCond) $ genRenameAlgebra $ 
          Join (genRenameAlgebra join_empacct_job) (genRenameAlgebra (tRef dept)) cond 
    where join_empacct_job = joinTwoRelation empacct job "title" 
          cond = C.Comp EQ (C.Att empno) (C.Att managerno)

empQ12_v5 :: Algebra
empQ12_v5 = Proj [trueAttr managerno, trueAttr salary] $ genRenameAlgebra $ 
          Sel (VsqlCond yearAfterCond) $ genRenameAlgebra $ 
          Join (genRenameAlgebra (tRef empacct)) (genRenameAlgebra (tRef dept)) cond 
    where cond = C.Comp EQ (C.Att empno) (C.Att managerno)

empVQ12 :: Algebra
empVQ12 = AChc (F.Or empv3 empv4)
            empQ12_v3v4
            (AChc empv5 empQ12_v5 Empty)

-- 13(Q7A)
-- intent: find the historical managers of department where
--         the employee 10004 worked, in all history.
--         (the period of their appointments don't need to 
--         overlap.) answer using data valid on or after
--         1991-01-01.
-- Process: 1. find the departments where 10004 worked
--          2. get managerno from those departments 
-- 
-- * variational queries:
--   (v3 or v4 or v5) <empQ13, empty> 
-- * plain queries for each version:
--   * For v3,v4,v5:
--       SELECT managerno
--       from dept
--       where deptno in 
--       (SELECT deptno 
--       FROM empacct
--       where empno = 10004 and hiredate>1991-01-01 )
-- 
empQ13 :: Algebra
empQ13 = Proj [trueAttr managerno] $ genRenameAlgebra $ 
          Sel (VsqlIn deptno sub) $ genRenameAlgebra $ 
            tRef dept  
      where sub = Proj [trueAttr deptno] $ genRenameAlgebra $ 
                    Sel (VsqlCond cond) $ genRenameAlgebra $ 
                    tRef empacct
            cond = (C.Comp EQ (C.Att empno) (C.Val empno_value)) `C.And ` yearAfterCond

empVQ13 :: Algebra
empVQ13 = AChc (empv3 `F.Or` empv4 `F.Or` empv5) empQ13 Empty

-- 14(Q7B)
-- intent: find all salary values of managers in all history.
--         (the periods of salary and manager appointment don't
--         need to overlap)
--         answer using data valid on or after the year 1991. 
empVQ14 :: Algebra
empVQ14 = empVQ12

-- 15(Q8A)
-- intent: for all managers that the employee 10004 worked with, 
--         find all the departments that the manager managed.
--         (temporal join followed by non-temporal join)
--         (10004's and the manager's affiliation with a single
--         department should overlap, but the manager's manager 
--         position periods do not need to overlap, naturally.)
--         anwer using data valid on or after the year 1991.
-- Process: 1. get managers that 10005 with
--          2. get departments for those managers 
-- 
-- * variational queries:
--   (v3 or v4 or v5) <empQ15, empty>
-- * plain queries for each version:
--   * For v3,v4,v5:
--      SELECT deptname 
--      from dept 
--      where managerno in 
--      (SELECT managerno 
--      FROM v3_empacct JOIN dept ON v3_empacct.deptno = dept.deptno
--      where empno = 10004 and hiredate>1991-01-01 )
-- =>  
--      SELECT deptname 
--      FROM v3_empacct JOIN dept ON v3_empacct.deptno = dept.deptno
--      where empno = 10004 and hiredate>1991-01-01 )
--     ** subquery here is the same with empQ11
empQ15 :: Algebra
empQ15 = Proj [trueAttr deptname] $ genRenameAlgebra $ 
          Sel (VsqlIn managerno empQ11) $ genRenameAlgebra $ 
            tRef dept

-- | v3 or v4 or v5 <q2, empty>
empVQ15 :: Algebra
empVQ15 = AChc (empv3 `F.Or` empv4 `F.Or` empv5) empQ15 Empty

-- 16(Q8B)
-- intent: for all managers, find all managers in the department 
--         that he/she worked in. (two worked during the same 
--         period) (non-temporal join followed by temporal-join)
--         answer using data valid on or after the year 1991.
empVQ16 :: Algebra
empVQ16 = AChc empv3 empQ16_v3 (AChc empv4 empQ16_v4 (AChc empv5 empQ16_v5 Empty))

empQ16_v3 :: Algebra
empQ16_v3 = Proj [trueAttr name, trueAttr deptname] $ genRenameAlgebra $ 
          Sel (VsqlCond yearCond) $ genRenameAlgebra $ 
            Join (genRenameAlgebra (tRef empacct)) (genRenameAlgebra (tRef dept)) cond 
          where cond = C.Comp EQ (C.Att empno) (C.Att managerno)

empQ16_v4 :: Algebra 
empQ16_v4 = Proj [trueAttr name, trueAttr deptname] $ genRenameAlgebra $ 
          Sel (VsqlCond yearAfterCond) $ genRenameAlgebra $ 
            Join (genRenameAlgebra join_empacct_empbio) (genRenameAlgebra (tRef dept)) cond 
          where join_empacct_empbio = joinTwoRelation empacct empbio "empno" 
                cond = C.Comp EQ (C.Att empno) (C.Att managerno)

empQ16_v5 :: Algebra
empQ16_v5 = Proj [trueAttr firstname, trueAttr lastname, trueAttr deptname] $ genRenameAlgebra $ 
              Sel (VsqlCond yearAfterCond) $ genRenameAlgebra $ 
                Join (genRenameAlgebra join_empacct_empbio) (genRenameAlgebra (tRef dept)) cond 
            where join_empacct_empbio = joinTwoRelation empacct empbio "empno" 
                  cond = C.Comp EQ (C.Att empno) (C.Att managerno)
