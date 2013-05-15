theory ScalaOption
imports Datatype
begin
datatype 'a Option = None | Some 'a

primrec get :: "'a Option \<Rightarrow> 'a \<Rightarrow> 'a" (infix "get" 65) where 
"None get dummy = dummy" |
"Some(v) get _  = v"

end

