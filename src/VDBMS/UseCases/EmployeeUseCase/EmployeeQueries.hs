-- | vqs for employee database.
module VDBMS.UseCases.EmployeeUseCase.EmployeeQueries where

import VDBMS.QueryLang.RelAlg.Variational.Algebra
import VDBMS.UseCases.EmployeeUseCase.EmployeeSchema
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import qualified VDBMS.QueryLang.RelAlg.Variational.Condition as C
import VDBMS.QueryLang.RelAlg.Variational.SmartConstructor
import VDBMS.DBMS.Value.CompOp
import Prelude hiding (Ordering(..))
import Database.HDBC 
import VDBMS.VDB.Name hiding (name)
import VDBMS.VDB.GenName

-- import Data.Time.LocalTime
import Data.Time.Calendar

-- need to run the following
-- numVarintQ empVQ8 empConfs
-- numUniqueVariantQ empVQ8

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
empCond = C.Comp EQ (C.Att empno) (C.Val empno_value)

empSqlCond :: VsqlCond
empSqlCond = VsqlCond empCond

empno_value :: SqlValue 
empno_value  = SqlInt32 10004

departno_value :: SqlValue
departno_value = SqlString "d001"

temp :: Name
temp = "temp"

v345 :: F.FeatureExpr
v345 = F.Or v34 empv5

v34 :: F.FeatureExpr
v34 = F.Or empv3 empv4

v45 :: F.FeatureExpr
v45 = F.Or empv4 empv5

-- empFromEmpacct :: Rename Algebra
-- empFromEmpacct = genSubquery "emp" $ Sel (VsqlCond empCond) (renameNothing (tRef empacct))

-- empFromEmpacctUnnamed :: Rename Algebra
-- empFromEmpacctUnnamed = genRenameAlgebra $ Sel (VsqlCond empCond) (renameNothing (tRef empacct))

--
-- * Queries based on Prima paper
-- Intents are taken from the prima paper, adjusted to the employee database. 
-- 1. We have year 1991, instead of year 2003. 
-- 2. We use features to identify the variants, instead of timestamps.

-- 1(Q1A). intent: Return the salary value of the employee whose employee number (empno) is 10004
--         for VDB variant V3.
-- 
-- note:
-- the year 1991 is included in variants v3, v4, and v5. we only
-- write the query for these variants for a fair comparison against
-- prima.
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- v_3 ⟨π (salary) ((ρ temp (σ (empno=1004) empacct)) ⋈_{temp.title=job.title} job), ε⟩
-- 
empVQ1, empVQ1_alt0, empVQ1_alt1, empVQ1_alt2 :: Algebra
empVQ1 = 
  choice empv3 
         (project (pure $ trueAttr salary_)  
          (join (renameQ temp (select empSqlCond $ tRef empacct))
                (tRef job)
                (joinEqCond (att2attrQual title_ temp) (att2attrQualRel title_ job))))
         Empty

-- Note that there's a slight difference between empVQ1 and empVQ1_alt0:
-- the former returns a table that has pres cond of v_3 while the latter
-- returns a table that has a pres cond equal to FM and its only attribute
-- has pres cond of v_3.
-- 
-- π (salary^\{v_3}) ((ρ temp (σ (empno=1004) empacct)) ⋈_{temp.title=job.title} job)
-- 
empVQ1_alt0 = 
  project (pure $ att2optatt salary_ empv3)  
          (join (renameQ temp (select empSqlCond $ tRef empacct))
                (tRef job)
                (joinEqCond (att2attrQual title_ temp) (att2attrQualRel title_ job)))

-- π (salary^\{v_3}) (σ (empno=1004) (empacct ⋈_{empacct.title=job.title} job))
-- 
empVQ1_alt1 = 
  project (pure $ att2optatt salary_ empv3)  
          (select empSqlCond 
                 (join (tRef empacct)
                       (tRef job)
                       (joinEqCond (att2attrQualRel title_ empacct) (att2attrQualRel title_ job))))

-- v_3 ⟨π (salary) (σ (empno=1004) (empacct ⋈_{empacct.title=job.title} job)), ε ⟩
-- 
empVQ1_alt2 = 
  choice empv3 
         (project (pure $ trueAttr salary_)
                  (select empSqlCond
                          (join (tRef empacct)
                                (tRef job)
                                (joinEqCond (att2attrQualRel title_ empacct) (att2attrQualRel title_ job)))))
         Empty
-- 
-- note: to ensure that naming is correct remove temp from the first, and have an incorrect query to check the system.
-- π (salary^\{v_3}) ((σ (empno=1004) empacct) ⋈_{empacct.title=job.title} job)
empVQ1_alt_typeErr = 
  project (pure $ att2optatt salary_ empv3)  
          (join (select empSqlCond (tRef empacct))
                (tRef job)
                (joinEqCond (att2attrQualRel title_ empacct) (att2attrQualRel title_ job)))

-- 2. intent: Return the salary values of the employee whose employee number (\empno) is 10004, 
--         for VDB variants \vThree\ to \vFive. 
--
-- Note: --> not sure why we need this note!
-- 1. Attribute deptno only exist in v3,v4,v5.
-- 
-- #variants = 3?
-- #unique_variants = 2?
-- 
-- π (salary) (v_3 ∨ v_4 ⟨ρ (temp) (σ (empno=10004) empacct) ⋈_{temp.title=job.title} job,
--                        v_5 ⟨σ (empno=10004) empactt, ε ⟩⟩)
-- 
empVQ2, empVQ2_alt1, empVQ2_alt2, empVQ2_alt3 :: Algebra
empVQ2 = 
  project (pure $ trueAttr salary_)
          (choice v34
                  q1
                  (choice empv5 q2 Empty))
    where
      q1 = join (renameQ temp q2)
                (tRef job)
                (joinEqCond (att2attrQual title_ temp) (att2attrQualRel title_ job))
      q2 = (select empSqlCond $ tRef empacct)

-- π (salary^{v_3 ∨ v_4 ∨ v_5}) (v_3 ∨ v_4 ⟨ρ (temp) (σ (empno=10004) empacct) ⋈_{temp.title=job.title} job,
--                                          σ (empno=10004) empactt⟩)
-- 
empVQ2_alt1 = 
  project (pure $ att2optatt salary_ (F.Or (F.Or empv3 empv4) empv5))
          (choice v34
                  q1
                  q2)
    where
      q1 = join (renameQ temp q2)
                (tRef job)
                (joinEqCond (att2attrQual title_ temp) (att2attrQualRel title_ job))
      q2 = (select empSqlCond $ tRef empacct)

-- π (salary^{v_3 ∨ v_4 ∨ v_5}) 
--   (ρ (temp) (σ (empno=10004) empacct) ⋈_{temp.title=job.title} 
--    v_3 ∨ v_4 ⟨job, ε⟩)
-- 
empVQ2_alt2 = 
  project (pure $ att2optatt salary_ v345)
          (join q1
                (choice (F.Or empv3 empv4) (tRef job) Empty)
                (joinEqCond (att2attrQual title_ temp) (att2attrQualRel title_ job)))
    where
      q1 = renameQ temp (select empSqlCond $ tRef empacct)

-- π (salary) 
--   (ρ (temp) (σ (empno=10004) empacct) ⋈_{temp.title=job.title} 
--    v_3 ∨ v_4 ⟨job, ε⟩)
-- 
empVQ2_alt3 = 
  project (pure $ trueAttr salary_)
          (join q1 
                (choice v34 (tRef job) Empty)
                (joinEqCond (att2attrQual title_ temp) (att2attrQualRel title_ job)))
    where
      q1 = renameQ temp (select empSqlCond $ tRef empacct)


-- 3.intent: Return the manager's name (of department d001) for VDB variant V3. 
-- 
-- #variants = 1?
-- #unique_variants = 1?
-- 
-- v_3 ⟨π (name) ((ρ (temp) (σ (deptno=d001) empacct)) ⋈_{temp.empno=dept.managerno} dept), ε⟩ 
-- 
empVQ3 :: Algebra
empVQ3 = 
  choice empv3 
         (project (pure $ trueAttr name_)
                  (join (renameQ temp 
                                 (select (eqAttValSqlCond deptno_ departno_value)
                                         (tRef empacct)))
                        (tRef dept)
                        (joinEqCond (att2attrQual empno_ temp) (att2attrQualRel managerno_ dept) )))
         Empty


-- 4.intent: Return the manager's name (of department d001), for VDB variants \vThree\ to \vFive.
-- 
-- #variants = 3?
-- #unique_variants = 3?
-- 
-- v_3 ∨ v_4 ∨ v_5 ⟨π (name, firstname, lastname) 
--                    (v_3⟨empacct, empbio⟩ ⋈_{empno=managerno} 
--                                          σ (deptno="d001") dept, ε⟩
-- 
empVQ4, empVQ4_alt1 :: Algebra
empVQ4 = 
  choice v345
         (project ([trueAttr name_, 
                    trueAttr firstname_, 
                    trueAttr lastname_])
                  (join (choice empv3
                               (tRef empacct)
                               (tRef empbio))
                        (select (eqAttValSqlCond deptno_ departno_value)
                                (tRef dept))
                        (joinEqCond (att2attr empno_) (att2attr managerno_))))
         Empty

-- v_3 ∨ v_4 ∨ v_5 ⟨π (name^{v_3 ∨ v_4}, firstname^{v_5}, lastname^{v_5}) 
--                    (v_3⟨empacct, empbio⟩ ⋈_{empno=managerno} 
--                                          σ (deptno="d001") dept, ε⟩
-- 
empVQ4_alt1 =
  choice v345
         (project ([att2optatt name_ v34, 
                    att2optatt firstname_ empv5, 
                    att2optatt lastname_ empv5])
                  (join (choice empv3
                               (tRef empacct)
                               (tRef empbio))
                        (select (eqAttValSqlCond deptno_ departno_value)
                                (tRef dept))
                        (joinEqCond (att2attr empno_) (att2attr managerno_))))
         Empty

-- 5.intent: Find all managers that the employee 10004 worked with, for VDB variant \vThree. 
--
-- #variants = 1?
-- #unique_variants = 1?
-- 
-- v_3⟨π (managerno) (ρ (temp) (σ (empno=10004) empacct) ⋈_{temp.deptno=dept.deptno} dept), ε⟩
-- 
empVQ5 :: Algebra
empVQ5 = 
  choice empv3 
         (project (pure $ trueAttr managerno_)
                  (join (renameQ temp (select empSqlCond (tRef empacct)))
                        (tRef dept)
                        (joinEqCond (att2attrQual deptno_ temp) (att2attrQualRel deptno_ dept))))
         Empty

-- -- 6.intent: Find all managers that employee 10004 worked with, for VDB variants \vThree\ to \vFive.
-- --
-- -- Queries in LaTex: 
-- -- \begin{align*} 
-- -- \pQ = &  \pi_{\managerno} (\sigma_{\empno=10004} (\empacct \bowtie_{\empacct.\deptno = \dept.\deptno} \dept)) \\
-- -- \vQ = & \chc[(\vThree \vee \vFour \vee \vFive)]{\pQ, \empRel}
-- -- \end{align*} 
-- empQ6 :: Algebra
-- empQ6 = Proj [trueAttr managerno] $ genRenameAlgebra $ 
--          Sel (VsqlCond empCond) $ genRenameAlgebra $ 
--     joinTwoRelation empacct dept "deptno" 

-- empVQ6 :: Algebra
-- empVQ6 =AChc (empv3 `F.Or` empv4 `F.Or` empv5) empQ6 Empty

-- -- 7.intent: Find all salary values of managers, during the period of manager appointment, for VDB variant \vThree. 
-- --
-- -- Queries in LaTex: 
-- -- \begin{align*} 
-- -- \pQ  =  & \pi_{(\managerno, \salary)}((\dept \\
-- -- & \bowtie_{\managerno = \empno} \empacct) \\
-- -- & \bowtie_{\empacct.\titleatt = \job.\titleatt} \job) \\
-- -- \vQ =  &\chc[\vThree]{\pQ, \empRel}
-- -- \end{align*} 
-- empQ7 :: Algebra
-- empQ7 = Proj [trueAttr managerno, trueAttr salary] $ genRenameAlgebra $ 
--           Join (genRenameAlgebra join_empacct_job) (genRenameAlgebra (tRef dept)) cond 
--     where join_empacct_job = joinTwoRelation empacct job "title" 
--           cond = C.Comp EQ (C.Att empno) (C.Att managerno)

-- empVQ7 :: Algebra
-- empVQ7 = AChc empv4 empQ7 Empty

-- -- 8.intent: Find all salary values of managers, during the period of manager appointment, for VDB variants \vThree\ to \vFive.
-- --
-- -- Queries in LaTex: 
-- -- \begin{align*} 
-- -- \pQ  =  & \pi_{(\managerno, \salary)}((\dept \\
-- -- & \bowtie_{\managerno = \empno} \empacct) \\
-- -- & \bowtie_{\empacct.\titleatt = \job.\titleatt} \job) \\
-- -- \pQ{'}= &  \pi_{(\managerno, \salary)} (\empacct \bowtie_{\empno = \managerno} \dept) \\ 
-- -- \vQ = & \chc[(\vThree \vee \vFour)]{\pQ, \chc[\vFive] {\pQ{'}, \empRel}}
-- -- \end{align*} 
-- empQ8 :: Algebra
-- empQ8 = Proj [trueAttr managerno, trueAttr salary] $ genRenameAlgebra $ 
--           Join (genRenameAlgebra (tRef empbio)) (genRenameAlgebra (tRef dept)) cond 
--           where cond = C.Comp EQ (C.Att empno) (C.Att managerno)

-- empVQ8 :: Algebra
-- empVQ8 = AChc (empv3 `F.Or` empv4) empQ7 $ AChc empv5 empQ8 Empty

-- -- 9.intent: Find the historical managers of the department where the employee 10004 worked for them in VDB variant \vThree. 
-- --
-- -- Queries in LaTex: 
-- -- \begin{align*} 
-- -- \temp{} = & \sigma_{\empno=10004} \empacct \\ 
-- -- \pQ = & \pi_{\managerno} (\temp{} \bowtie_{\temp{}.\deptno = \dept.\deptno} \dept  )\\
-- -- \vQ = & \chc[\vThree]{\pQ, \empRel}
-- -- \end{align*} 
-- empQ9 :: Algebra
-- empQ9 = Proj [trueAttr managerno] $ genRenameAlgebra $ 
--           Join temp (genRenameAlgebra (tRef dept)) join_cond 
--           where temp = genSubquery "temp" $ Proj [trueAttr managerno] $ genRenameAlgebra $ tRef empacct 
--                 join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "temp" "deptno")) (C.Att (qualifiedAttr dept "deptno"))

-- empVQ9 :: Algebra
-- empVQ9 = AChc empv3 empQ9 Empty

-- -- 10.intent: Find the historical managers of department where the employee 10004 worked, in all history, for VDB variants \vThree\ to \vFive.
-- --
-- -- Queries in LaTex: 
-- -- \begin{align*} 
-- -- \temp{} = & \sigma_{\empno=10004} \empacct \\ 
-- -- \pQ = & \pi_{\managerno} (\temp{} \bowtie_{\temp{}.\deptno = \dept.\deptno} \dept  )\\
-- -- \vQ = & \chc[(\vThree \vee \vFour \vee \vFive)]{\pQ, \empRel}
-- -- \end{align*} 
-- empVQ10 :: Algebra
-- empVQ10 = AChc (empv3 `F.Or` empv4 `F.Or` empv5) empQ9 Empty

-- -- 11.intent: For all managers that the employee, whose employee number (\empno) is 10004, has worked with, 
-- --            find all the departments that the manager managed, for VDB variant \vThree. 
-- --
-- -- Queries in LaTex: 
-- -- \begin{align*} 
-- -- \temp{} =  & \pi_{(\managerno, \deptno)} (\sigma_{\empno=10004} (\empacct \bowtie_{\empacct.\deptno = \empacct.\deptno} \dept))\\
-- -- \pQ = & \pi_{(\dept.\managerno, \dept.\deptno)} (\temp{} \bowtie_{\temp.\managerno = \dept.\managerno} \dept) \\
-- -- \vQ = & \chc[\vThree]{\pQ, \empRel}
-- -- \end{align*}
-- empQ11 :: Algebra
-- empQ11 = Proj (map trueAttr qualifiedAttrList)$ genRenameAlgebra $ 
--           Join temp (genRenameAlgebra (tRef dept)) join_cond 
--           where qualifiedAttrList = genQualifiedAttrList [(dept, "managerno"), (dept, "deptno")]
--                 temp = genSubquery "temp" $ Proj [trueAttr managerno, trueAttr deptno] $ genRenameAlgebra $ 
--                         Sel (VsqlCond empCond) $ genRenameAlgebra $ 
--                           joinTwoRelation empacct dept "deptno"
--                 join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "temp" "managerno")) (C.Att (qualifiedAttr dept "managerno"))

-- empVQ11 :: Algebra
-- empVQ11 = AChc empv3 empQ11 Empty

-- -- 12.intent: For all managers that the employee, whose employee number (\empno) is 10004, has worked with, 
-- --            find all the departments that the manager managed, for VDB variants \vThree\ to \vFive.
-- --
-- -- Queries in LaTex: 
-- -- \begin{align*} 
-- -- \temp{} =  & \pi_{(\managerno, \deptno)} (\sigma_{\empno=10004} (\empacct \bowtie_{\empacct.\deptno = \empacct.\deptno} \dept))\\
-- -- \pQ = & \pi_{(\dept.\managerno, \dept.\deptno)} (\temp{} \bowtie_{\temp.\managerno = \dept.\managerno} \dept) \\
-- -- \vQ = & \chc[(\vThree \vee \vFour \vee \vFive)]{\pQ, \empRel}
-- -- \end{align*} 
-- empVQ12 :: Algebra
-- empVQ12 = AChc (empv3 `F.Or` empv4 `F.Or` empv5) empQ11 Empty

-- -- 13.intent: For all managers, find all managers in the department that he/she worked in, 
-- --            for VDB variant \vThree. 
-- --
-- -- Queries in LaTex: 
-- -- \begin{align*} 
-- -- \temp{} = & \pi_{(\managerno, \deptno)} \dept \\
-- -- \pQ = & \pi_{(\dept\managerno, \deptname, \dept.\managerno)}(\temp{} \bowtie_{\temp.\deptno = \dept.\deptno} \dept)\\
-- -- \vQ = & \chc[\vThree]{\pQ, \empRel}
-- -- \end{align*} 
-- empQ13 :: Algebra
-- empQ13 = Proj (map trueAttr [qualifiedAttr dept "managerno", deptname]) $ genRenameAlgebra $ 
--           Join temp (genRenameAlgebra (tRef dept)) join_cond 
--           where temp = genSubquery "temp" $ Proj [trueAttr managerno, trueAttr deptno] $ genRenameAlgebra $ tRef dept 
--                 join_cond = C.Comp EQ (C.Att (subqueryQualifiedAttr "temp" "deptno")) (C.Att (qualifiedAttr dept "deptno"))

-- empVQ13 :: Algebra
-- empVQ13 = AChc empv3 empQ13 Empty

-- -- 14.intent: For all managers, find all managers in the department that he/she worked in, 
-- --            for VDB variants \vThree\ to \vFive.
-- --
-- -- Queries in LaTex: 
-- -- \begin{align*} 
-- -- \temp{} = & \pi_{(\managerno, \deptno)} \dept \\
-- -- \pQ = & \pi_{(\dept.\managerno, \deptname)}(\temp{} \bowtie_{\temp.\deptno = \dept.\deptno} \dept)\\
-- -- \vQ = & \chc[(\vThree \vee \vFour \vee \vFive)]{\pQ, \empRel}
-- -- \end{align*} 
-- empVQ14 :: Algebra
-- empVQ14 = AChc (empv3 `F.Or` empv4 `F.Or` empv5) empQ13 Empty