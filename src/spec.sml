structure FuncSpec =
struct
  datatype sort =
    Kind
  | ProperType
  | IntSort
  | BoolSort
  type sorts = sort list
  type axiom = sort * sort
  type axioms = axiom list
  type rule = sort * sort * sort
  type rules = rule list

  type spec = sorts * axioms * rules

  fun rho (sp : spec) (s1, s2) =
    (case List.find (fn x => #1 x = s1 andalso #2 x = s2) (#3 sp) of
      SOME triple => SOME (#3 triple)
    | NONE => NONE)

  fun plus (sp : spec) s1 =
    case List.find (fn a => #1 a = s1) (#2 sp) of
      SOME s' => SOME (#2 s')
    | NONE => NONE
end

