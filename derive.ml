(* It seems the idea is that taking a derivative of a grammar, we
 * should rewrite the grammar and then we can defer the decision of
 * whether a string matched a grammar until having consumed the 
 * entire string. I.e. 
 * rec(ct, G) = rec(t, Dc(G))
 * rec([], G) = nullable(G)
 *)

type pattern = Epsilon | Empty | Lit of char | NT of string
type rule    = Rule of string * (pattern list)
type grm     = Grm of string * (rule list)

let chr c = [Lit c]

let explode s =
	let rec loop n = 
		if n < String.length s
		then (s.[n]) :: loop (n + 1)
		else []
	in
		loop 0


let str s = 
	let rec loop n = 
		if n < String.length s
		then chr (s.[n]) @ loop (n + 1)
		else []
	in
		loop 0

exception No_rule
(* construct a rule *)
let (+>) name ps = [Rule (name, ps)]

(* add branch to rule *)
let (|>) (rules : rule list) ps =
	match rules with 
	| [] -> raise No_rule
	| (Rule (name, _)) :: rs -> Rule (name, ps) :: rules

let (!!) name = [NT name]

let digit =
	"digit" +> 
		chr '0' |> chr '1' |> chr '2' |> chr '3' |>
		chr '4' |> chr '5' |> chr '6' |> chr '7' |>
		chr '8' |> chr '9'

let num =
	"num" +> !!"digit" |> !!"digit" @ !!"num"

let ope =
  "ope" +> 
    chr '+' |> chr '-' |> chr '*' |> chr '/'

let expr =
  "expr" +> (!!"expr" @ !!"ope" @ !!"expr")
         |> (chr '(' @ !!"expr" @ chr ')')
         |> !!"num"

let expr_grm =
	Grm ("expr", expr @ ope @ num @ digit)

let num_grm =
  Grm ("num", num @ digit)

let s = 
  "S" +> (!!"S" @ chr '+' @ !!"S")
      |> chr '1'

let s_grm =
  Grm ("S", s)

let pp_pattern = function
	| Epsilon -> "ε"
	| Empty   -> "Ø"
	| Lit c   -> String.make 1 c
	| NT n    -> n
let pp_rule = function
	| Rule (s, patterns) -> s ^ "->" ^ String.concat " " (List.map pp_pattern patterns)
let pp_grm = function
	| Grm (start, rules) -> 
			"start: " ^ start ^ "\n"  ^ 
			String.concat "\n" (List.map pp_rule rules) ^
			"\n"
			
let list_grm = Grm("List", [
	Rule ("List", [Lit 'x']);
	Rule ("List", [NT "List"; Lit 'x']);
])

let paren_grm = Grm("S",[
	Rule ("S", [Epsilon]);
	Rule ("S", [NT "S"; Lit '('; NT "S"; Lit ')']);
])

(* Return the list of rules defining a NT symbol *)
let get_rules grm name =
	match grm with 
	| Grm(_, rules) -> List.find_all (fun (Rule (name', ps)) -> name' = name) rules

let make_nt x s = "d" ^ (String.make 1 x) ^ "(" ^ s ^ ")"

let derive_pattern x = function 
	| Lit y when y = x -> Epsilon
	| Epsilon
	| Empty 
	| Lit _ -> Empty
	| NT s -> NT (make_nt x s)

let rec fix eq f x =
	let fx = f x in
	if eq fx x then fx else fix eq f fx


let eq_lists l1 l2 = 
	List.for_all (fun e1 -> List.exists (fun e2 -> e1 = e2) l2) l1 &&
	List.for_all (fun e2 -> List.exists (fun e1 -> e1 = e2) l1) l2
	
let (++) e ls = if List.exists (fun e' -> e = e') ls then ls else e :: ls
let (@@) ls1 ls2 = List.fold_left (fun acc_ls e1 -> e1 ++ acc_ls) ls2 ls1

let nullable_cache =
  Hashtbl.create 101

let cached_find s =
  if Hashtbl.mem nullable_cache s
  then Some (Hashtbl.find nullable_cache s)
  else None

let all_symbs = Hashtbl.create 101

let rec refresh_all_symbs = function
  | [] -> ()
  | (Rule(s,_)) :: rs -> 
      begin 
        Hashtbl.replace all_symbs s true;
        refresh_all_symbs rs;
      end

let add_nullable s = (Hashtbl.replace nullable_cache s true; s)
let is_nullable s = Hashtbl.find nullable_cache s

(* returns the set of nullable symbols in a grammar *)
let nullable_symbs = function
	| Grm(start, rules) -> 
		let rec g acc_symbs = function 
			| Rule(s, []           )-> []
			| Rule(s, Lit _   :: _ )
			| Rule(s, Empty   :: _ )-> []
			| Rule(s, Epsilon :: [])-> [add_nullable s]
			| Rule(s, Epsilon :: ps)-> g acc_symbs (Rule (s, ps))
			| Rule(s, NT s'   :: ps)-> 
          match cached_find s' with
          | None ->
                if List.exists (fun a -> a = s') acc_symbs
                then 
                  if ps = []
                  then [add_nullable s]
                  else g acc_symbs (Rule(s, ps))
                else []	
          | Some true ->
              if ps = []
              then [add_nullable s]
              else g acc_symbs (Rule(s,ps))
          | Some false -> []
		in 
    let null_symbs = 
      fix eq_lists 
				(fun old_symbs -> 
					List.fold_left 
					(fun acc ls -> ls @@ acc) 
					[] 
					(List.rev_map (g old_symbs) rules))
        [] in
    let () = refresh_all_symbs rules in
    begin
      Hashtbl.fold (fun symb _ _ ->
        if Hashtbl.mem nullable_cache symb
        then ()
        else Hashtbl.replace nullable_cache symb false;
      ) all_symbs ();
      null_symbs;
    end


let nullable_p grm = function 
	| Lit _ | Empty -> false
	| Epsilon -> true
	| NT s -> 
      if Hashtbl.mem nullable_cache s
      then Hashtbl.find nullable_cache s
      else 
        begin
          let symb = nullable_symbs grm in
          try is_nullable s
          with Not_found -> begin
            (*print_endline ("Symbol not in cache: " ^ s);*)
            (*print_endline ("Cache   : " ^ *)
              (*Hashtbl.fold (fun key _ acc -> key ^ " " ^ acc) nullable_cache "");*)
            (*print_endline ("Computed: " ^ String.concat " " symb);*)
            (*print_endline ("Gramar follows");*)
            (*print_endline (pp_grm grm);*)
            (*raise Not_found*)
            Hashtbl.replace nullable_cache s false;
            false;
          end
        end
			

let compact_rule = function
  | Rule(s, ps) as rule ->
      if List.exists (fun p -> p = Empty) ps
      then None
      else Some rule

let derive_rule_cache = Hashtbl.create 101

let rec derive_rule grm x = function
	| Rule(s, ps) as rule-> 
      if Hashtbl.mem derive_rule_cache (x, rule)
      then begin
        Hashtbl.find derive_rule_cache (x, rule)
      end
      else 
        let res =
          match ps with
          | [] -> []
          | p :: ps ->
              match compact_rule (Rule (make_nt x s, derive_pattern x p :: ps)) with
              | None -> 
                  if nullable_p grm p
                  then derive_rule grm x (Rule (s, ps))
                  else []
              | Some r -> r :: 
                if nullable_p grm p
                then derive_rule grm x (Rule (s, ps))
                else []
        in
        begin
          Hashtbl.replace derive_rule_cache (x, rule) res;
          res
        end

let remove_redundant_rules old_rules new_rules =
  let all_rules = List.rev_append new_rules old_rules in
  let get_rules name =
    List.find_all (function 
      | Rule (name', _) -> name = name') all_rules in
  let rec loop = function
    | [] -> []
    | (Rule(name, ps)) as r :: rs ->
        if List.exists (function
          | NT name -> get_rules name = []
          | _ -> false 
        ) ps
        then loop rs
        else r :: loop rs
  in
    fix eq_lists loop new_rules

let derive_grm x = function 
	| Grm(start, rules) as grm -> 
        Grm(make_nt x start,
            rules @@
            (remove_redundant_rules rules (
            List.concat (List.rev_map (derive_rule grm x) rules))))

let recognize seq grm =
	let rec loop (Grm (start, rules) as grm) = function
		| [] -> 
        begin
          (*print_endline "DONE";*)
          (*print_endline (pp_grm grm);*)
          (*print_endline ("Nullables: " ^ String.concat " " (nullable_symbs grm));*)
          List.exists (fun s -> s = start) (nullable_symbs grm)
        end
		| c :: seq -> 
        begin
          print_endline ("["^string_of_int (List.length rules)^"] @'"^String.make 1 c^"'");
          (*print_endline "Deriving...";*)
          let grm' = derive_grm c grm in
          begin
            (*print_endline "finished derive_grm";*)
            loop grm' seq
          end
        end
	in
		loop grm seq
		
let rec_str str grm = recognize (explode str) grm

let p_str = "1*1+1+1/1*1+1"

let _ = begin
	print_endline ("Start parsing: " ^ p_str);
	let ps = rec_str p_str expr_grm in
	if ps then print_endline "OK"
	else print_endline "Not member"
end
