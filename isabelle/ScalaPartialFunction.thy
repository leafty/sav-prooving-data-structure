theory ScalaPartialFunction
imports Datatype
begin

datatype ('a, 'b) PartialFunction = PartialFunction "'a \<Rightarrow> bool" "'a \<Rightarrow> 'b"

primrec isDefinedAt :: "('a, 'b) PartialFunction \<Rightarrow> 'a \<Rightarrow> bool" (infix "isDefAt" 65) where
"(PartialFunction defAt fun) isDefAt a = defAt a"

primrec app :: "('a, 'b) PartialFunction \<Rightarrow> 'a \<Rightarrow> 'b" (infix "apply" 65) where
"(PartialFunction defAt fun) apply a  = fun a"


end

