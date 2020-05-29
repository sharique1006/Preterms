(*symbol & variables are string & arity is int*)
type symbol = string
type variable = string
type arity = int
(*signature is a list of pairs of symbols & their arities*)
type signature = (symbol * arity) list
(*term is a variable or a Node of pair of symbol & term list*)
type term = V of variable | Node of symbol * (term list)
(*substitution is a list of pairs of variables & terms*)
type substitution = (variable * term) list
exception NOT_UNIFIABLE
exception Invalid_argument

(*Examples of terms*)
let t1 = V "var1";;
let t2 = Node ("z", []);;
let t3 = Node ("f", [Node ("a", []); Node ("b", [])]);;
let t4 = Node ("g", [t2]);;
let t5 = Node ("f", [Node ("a", []);Node ("y", [V "var2"; Node ("c", [])])])
let t6 = Node ("f", [Node ("a", []);Node ("y", [Node ("b", []);Node ("c", [Node ("d", [])])])])
let t7 = Node ("f", [V "var1";Node ("y", [V "var2";Node ("c", [V "var3"])])]);;
let t8 = Node ("f", [V "var1";Node ("g", [V "var2"; Node ("d", [Node("a",[]);V "var1";V "var2";V "var4";V "var7"]);  Node ("c", [])])]);;
let t9 = Node ("f", [V "var1";Node ("g", [V "var2";Node ("d", [Node("a",[]);V "var1";V "var2";V "var4";V "var7"]); Node ("c", [V "var3"]); Node("b",[])])]);;
let t10 = Node("s", [V "sd"; Node("f", [V "d"; V "q"; V "w"]); V "kj"]);;
let t11 = Node("s", [Node("g", []); Node("f", [V "h"; V "sd"; V "k"]); V "ds"]);;
let t12 = Node("s", [V "sd"; V "l"; V "kj"]);;
let t13 = Node("s", [V "l"; Node("f", [V "h"; V "sd"; V "k"]); V "ds"]);;
let t14 = Node ("a", [V "v1";Node("b",[V "v2"; V "v3"])]);;
let t15 = Node ("a", [V "v1";Node("b",[V "v3"; V "v2"])]);;
let t16 = Node ("a", [V "v1"; Node ("b", [Node ("x", []); V "v2"; V "v3"])]);;
let t17 = Node ("a", [Node ("x", []); Node ("b", [V "v1"; V "v3"; V "v2"])]);;
let term1 = Node ("a", [V "x"; Node ("b", [V "x"; Node("c",[])])]);;
let term2 = Node ("a", [V "y"; Node ("b", [Node("d", [V "y"; Node("e",[])]); Node("c",[])])]);;
let term3 = Node("a", [V "x"; V "y"; V "z"]);;
let term4 = Node("a",[V "y"; V "z"; Node("b",[])]);;
let term5 = Node("a",[V "x";V "y";V "z"]);;
let term6 = Node("a",[V "y"; V "z"; Node("b",[V "x"; Node("c",[])])]);;
let term7 = Node("a",[V "s"; Node("b", [V "t"; Node("c", [V "t"]); V "u"])]);;
let term8 = Node("a",[V "t"; Node("b", [V "s"; V "s"; V "u"])]);;
let term9 = Node("a",[V "t"; Node("b", [V"s"; Node("c", [Node("d",[])]); V "s"])]);;
let term10 =Node("a", [Node("b", [V "x"; Node("c",[])]); Node("d",[V "y"; V "x"])]);;
let term11 = Node("a", [V "z" ;Node("d", [Node("f", [V "z"]); V "x"])]);;
let term12 = Node("a",[V "z"; Node("d", [Node("f", [V "z"]); V "e"])]);;

(*Examples of signatures*)
let ss1 = [("a", 0); ("f", 2); ("g", 1); ("b", 0)];;
let ss2 = [("b", -1); ("f", 2); ("g", 1)];;
let ss3 = [("d", 5); ("f", 2); ("g", 3)];;
let ss4 = [("a", 0); ("f", 2); ("g", 1); ("g", 1)];;
let ss5 = [];;
let ss6 = [("d", 5); ("f", 2); ("g", 3); ("c", 1)];;

(*function which checks if a is present in the given list or not*)
let rec is_present a alist = match alist with
                | [] -> false
                | x :: xs -> if x=a then true 
                      else is_present a xs;;

(*function which is same as List.map - maps each element of x to f x*)
let rec map f l = match l with
                  | [] -> []
                  | x :: xs -> (f x) :: (map f xs);;

(*function to check if signature is valid or not
  1. Signature is valid if none of its symbol are repeated 
  2. There is atleast one symbol with zero arity
  3. There are no symbols which have negative arity*)
let rec check_sig_helper s symblist aritvalid = match s with
                      | [] -> (aritvalid = true)
                      | x :: xs -> let (a,b) = x in
                            if (b < 0 || (is_present a  symblist)) then false
                            else if (b = 0) then check_sig_helper xs (a::symblist) true
                            else check_sig_helper xs (a::symblist) (false || aritvalid);; 


(*Main function to check signature which calls the check_sig_helper*)
let check_sig (s:signature) = check_sig_helper s [] false;; 

(*function to check if a term is well formed or not according to a given signature
    1. Term is valid if it is a Variable
    2. Trem is valid if its a Node & the symbol of the node is present in the signature 
      & number of children of that node is exactly equal to the arity of that symbol in the given signature*)
let rec wfterm_helper l s = match l with
                          | [] -> true
                          | x :: xs ->  match x with
                                          | V var -> wfterm_helper xs s
                                          | Node (sym,tlist) ->  if (is_present (sym, List.length tlist) s) then wfterm_helper xs s
                                                                  else false;;           
    
(*Main function to check term is valid or not according to a given signature*)                  
let wfterm (s:signature) (t:term) = match t with
                                | V _ -> true
                                | Node (sym, []) -> (is_present (sym,0) s)
                                | Node (sym, tlist) -> if (is_present (sym, List.length tlist) s) then wfterm_helper tlist s
                                                        else false;;

(*function to find the height of a term, each term is a tree, so we need to find the height of a tree*)
let rec height_helper l i = match l with
                                  | [] -> i
                                  | x::xs -> match x with 
                                              | V var -> height_helper xs (i) 
                                              | Node (sym,tlist) -> height_helper xs ( 1+(max(height_helper tlist 0) i)) ;;

(*Main function to find the height of a term*)
let ht (t:term) = match t with
                | V var -> 0
                | Node (sym,tlist) -> (height_helper tlist 0) ;;


(*function to count the total number of nodes & variables in a term*)
let rec size_helper l i = match l with
                                  | [] -> i
                                  | x::xs -> match x with 
                                              | V var -> 1 + size_helper xs (i) 
                                              | Node (sym,tlist) -> size_helper xs ( 1+((size_helper tlist 0)+i)) ;;

(*Main function to find the size of a tree*)
let size (t:term) = match t with
                | V var -> 1
                | Node (sym,tlist) -> (size_helper tlist 1) ;;

(*Function to get a list of all variables present in a given term*)
let rec vars_helper l vlist = match l with
                                  | [] -> vlist
                                  | x::xs -> match x with 
                                              | V var -> if (is_present var vlist)=false then vars_helper xs (var::vlist) else vars_helper xs vlist
                                              | Node (sym,tlist) -> vars_helper xs (vars_helper tlist vlist) ;;

(*main function to find all the variables present in a given term, calls the function vars_helper*)
let vars (t:term) = match t with
                | V var -> [var]
                | Node (sym,tlist) -> (vars_helper tlist []) ;;


(*Examples of substitutions*)
let s1 = [("var1", Node ("m", [])); ("var2", Node("n", []))];;
let s2 = [("var2", Node ("i", [])); ("var3", Node("j", [])) ];;
let s3 = [("var1",Node("b",[])); ("var2",Node("a",[])); ("var3",Node("e",[]));("var4",Node("d",[Node("a",[]);V "var1";V "var2";V "var4";V "var7"])); ("var7",Node("c",[Node("a",[])]))]
let s4 = [("var1",V "var2");  ("var4",V "var7"); ("var3",V "var2")];;

(*function which finds the term of the variable which matches with the given variable*)
let rec get_term var sub = match sub with
                      | [] -> V var
                      | (x,y) :: xs -> if var=x then y else get_term var xs;;

(*function to find the substitution of a given term according to a given substitution
  Basically in the given term for each variable present in the term replace it by the corresponding term in the substitution*)
let rec subst (t:term) (s:substitution) = match t with
                            | V var -> get_term var s
                            | Node (sym, tlist) -> Node (sym, (map (fun el -> subst el s) tlist));;

(*Function which checks if given variable is present in list or not*)
let rec present x = function
    | V y -> x = y
    | Node (_, lst) -> List.exists (present x) lst ;;

(*compose_term finds a term - if variable x is present in the substitution s then return the term assoociated with the matched variable in s else return y*)
let rec compose_term x y s = match s with
                | [] -> y
                | (a,b)::xs -> if x=a then b else compose_term x y xs;;

(*present_sub is a boolean which returns true if given variable is present in the given substitution else false*)
let rec present_sub v s1 = match s1 with
                  | [] -> false
                  | (x,y)::xs -> if v=x then true else present_sub v xs;;

(*compose_s2 adds all those pairs in s2 whose variables are not present in s1 in the given list s*)
let rec compose_s2 s1 s2 s = match s2 with
                    | [] -> s
                    | (x,y) :: xs -> if (present_sub x s1)=true then compose_s2 s1 xs s else compose_s2 s1 xs ((x,y)::s);;

(*compose_s1 adds all pairs of s1 to the list s by after replacing the term of each variable in s1 , if present in s2*)
let rec compose_s1 s1 s2 s = match s1 with
                            | [] -> s
                            | (x,y) :: xs -> compose_s1 xs s2 ((x, (subst y s2)) :: s);;

(*Main function to find composition of s1 s2*)
let composition s1 s2 = compose_s2 s1 s2 (compose_s1 s1 s2 []);;

(*make_pairs is same as List.combine which given two list returns a list of paired elements with pairs from l1 & l2 if they have same length*)
let rec make_pairs l1 l2 = match l1,l2 with
                  | _::_,[] -> raise Invalid_argument
                  | [],_::_ -> raise Invalid_argument
                  | [],[] -> []
                  | x::xs, y::ys -> (x,y) :: make_pairs xs ys;;

(*function which returns false if a given variable is present in variable term*)
let rec present2 x t = match t with
              | V y -> if (x=y) then false else true
              | Node (_, lst) -> List.exists (present2 x) lst ;;

(*Given a term1*term2 list checks if var is present in the term list of term2 or not*)
let rec present_vars var l = match l with
                  | [] -> false
                  | (x,y) :: xs -> match y with
                                | V v -> if var=v then false else present_vars var xs;
                                | Node (sym, tlist) -> if (present2 var y)=true then true else present_vars var xs;;

(*copy of present_vars except that it matches x*)
let rec present_vars2 var l = match l with
                  | [] -> false
                  | (x,y) :: xs -> match x with
                                | V v -> if var=v then false else present_vars var xs;
                                | Node (sym, tlist) -> if (present var x)=true then true else present_vars2 var xs;;

(*function to fing the unifier of given terms
  First make pair (t1,t2) 
    If first term of t1 is variable & second term of t2 is also variable the if both varibales are same then do nothing else add the pair of variable & term to list
    If t1 matches with variable & t2 matches with Node then the variable of t1 is present in the term list of Node of t2 then Unifies does not exist else append the variable & term to list
    If t1 has Node & t2 also has Node then if the symbols of both node are same & both have same number of children then unify the term list of both nodes
    else they cannot be unified*)
let rec unify list = match list with
      | [] -> []
      | (x,y) :: tl -> (unify tl) @ (unif (x,y) tl)
      and unif (s,t) tl = match (s,t) with
                  | (V var1, V var2) -> if (var1=var2) then [] else if (present_vars var1 tl)=true then raise NOT_UNIFIABLE else [(var1,t)]
                  | (V var, (Node (sym, tlist) as t)) -> if ((present var t)=true || (present_vars var tl)=true) then raise NOT_UNIFIABLE else [(var,t)]
                  | ((Node (sym, tlist) as t), V var) -> if ((present var t)=true || (present_vars2 var tl)=true) then raise NOT_UNIFIABLE else [(var,t)]
                  | (Node (sym1, tlist1), Node (sym2, tlist2)) -> if (sym1=sym2) && (List.length tlist1 = List.length tlist2) then unify (make_pairs tlist1 tlist2) 
                                                                  else raise NOT_UNIFIABLE;;

(*Function to check if given variable is present in a term which is a variable in the substitution*)
let rec already_present var l = match l with
                    | [] -> false
                    | (x,y) :: xs -> match y with
                                  | V v ->  if var=v then true else already_present var xs
                                  | Node (s,t) -> already_present var xs;;

(*removes conflicts of the type v2, V v3 && v3, V v2*)
let rec remove_conflicts res l = match l with
                    | [] -> res
                    | (x,y) :: xs -> if (already_present x res) = true then remove_conflicts res xs else remove_conflicts ((x,y)::res) xs;;

(*Function to check whether t1 & t2 are same terms*)
let check_same t1 t2 = match (t1,t2) with
                    | V v1, V v2 -> if v1=v2 then true else false
                    | V v1, Node (sym, tlist) | Node(sym,tlist), V v1-> false
                    | Node(s1,t1), Node (s2,t2) -> if s1=s2 && t1=t2 then true else false;;

(*applies the substitution till there is no change in the term or applying substitution has no effect on the term*)
let rec while_subst temp t sub = if (check_same temp (subst t sub))=true then temp else if (check_same t (subst t sub))=false then while_subst temp (subst t sub) sub else t;; 

(*applies subst on each term of the substitution to make it in reduced form*)
let rec apply_subst res l sub = match l with
                    | [] -> res
                    | (x,y) :: xs -> apply_subst ((x, (while_subst y y sub))::res) xs sub;;

(*Checks if the pair (v,t) is present in l*)
let rec repeated v t l = match l with
                    | [] -> false
                    | (x,y)::xs -> if (x=v) && (check_same t y)=true then true else repeated v t xs;;

(*Function to remove repeated pairs from the substitution*)
let rec remove_repititions res l = match l with
                    | [] ->   res
                    | (x,y)::xs -> if (repeated x y res) = true then remove_repititions res xs else remove_repititions ((x,y)::res) xs;;

(*Main function to find the most general unifier of two terms*)
let mgu (t1:term) (t2:term) = remove_repititions [] (remove_conflicts [] (apply_subst [] (unif (t1,t2) []) (unif (t1,t2) [])));;