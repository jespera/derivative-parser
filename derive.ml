let new_fix no_new comb f = function y ->
  let rec loop x =
    let fx = f x in
    if no_new fx x then x else loop (comb fx x)
  in
    loop y

let fix eq f x = 
  let rec loop x =
    let fx = f x in
    if eq fx x then x else loop fx 
  in
    loop x

let opt_map_tail f xs =
  let rec loop acc = function 
    | [] -> acc
    | x :: xs -> 
        match f x with
        | None -> loop acc xs
        | Some v -> loop (v :: acc) xs
  in
  loop [] xs


let (++) x xs = if List.mem x xs then xs else x :: xs

let (@@) xs ys = List.fold_left (fun zs x -> x ++ zs) ys xs

module Grammar =
  struct
    type pattern   = Epsilon | Empty | Lit of char | NT of string
    type pre_rule  = Rule of pattern list list | Derived of pre_rule Lazy.t 

    module RuleOrder = struct
      type t = string
      let compare = Pervasives.compare
    end
    module RuleMap = Map.Make(RuleOrder)
    type rules = pre_rule RuleMap.t    
        
    module NullOrder = struct
      type t = string
      let compare = Pervasives.compare
    end
    module NullMap = Map.Make(NullOrder)
    type nullables = bool option NullMap.t
    (* should only allow monotonic additions where None < Some false 
     * and None < Some true and nothing else *)

    let string_of_null_opt = function
      | None -> "_|_"
      | Some f -> string_of_bool f

    let string_of_nullmap nm =
      NullMap.fold (fun name value acc -> name ^ "->" ^ string_of_null_opt value ^ " " ^ acc) nm ""


    type grm       = {
      start:string; 
      rules:rules;
    }

    let (!!) r = match r with
    | Rule _ -> r
    | Derived cont -> Lazy.force cont
 
    let rec string_of_pre = function
      | Rule(ps_lists) -> "["^String.concat " | " 
        (
          List.map (function ps_list -> 
            "[" ^ String.concat " " (List.map (function
                | Epsilon -> "ε" 
                | Empty   -> "Ø"
                | Lit c   -> String.make 1 c
                | NT s    -> s) ps_list)
            ^ "]"
          ) ps_lists
        )
      ^"]"
      | Derived v when Lazy.lazy_is_val v -> 
          "?<" ^ string_of_pre (Lazy.force v) ^ ">"
      | Derived v -> "?"

    let string_of_rule name pre_rule acc =
      (name ^ " ::= " ^ string_of_pre pre_rule) :: acc

    let string_of_rules rules =
      String.concat "\n" (RuleMap.fold string_of_rule rules [])

    let make_grm start = 
      {
        start = start;
        rules = RuleMap.empty;
      }

    exception Error
    exception Lazy_error

    (* Return the rules that can be reached from the start-node *)
    let get_reachable grm = 
      let start_ps_lists = !!(RuleMap.find grm.start grm.rules) in
      let start_rules =
        RuleMap.add grm.start start_ps_lists RuleMap.empty in
      (* given the rules in cur_rules, find all rules from grm.rules
       * that are referenced from cur_rules
       *)
      let f cur_rules_map = 
        (* for each name->pre_rule binding in cur_rules_map
         * we scan the ps_lists and for each (NT name') we 
         * add the pair (name', cur_rules.map[name']) to the output set
         * (if not already added)
         *)
        RuleMap.fold 
        (fun name rule acc_new -> 
          match rule with
          | Rule ps_lists ->
              List.fold_left (fun acc_new ps_list -> 
                List.fold_left (fun acc_new p -> 
                  match p with 
                  | NT name' -> 
                      if RuleMap.mem name' cur_rules_map
                      then acc_new
                      else begin
                        try
                          (name', RuleMap.find name' grm.rules) :: acc_new 
                        with Not_found -> 
                          (* partial grammar *)
                          acc_new
                      end
                  | _ -> acc_new
                ) acc_new ps_list
              ) 
              acc_new ps_lists
          | Derived _ -> raise Lazy_error
        )
        cur_rules_map
        []
      in
      new_fix 
      (fun new_rules old_rules_map -> new_rules = [])
      (fun new_rules cur_rules_map -> 
        (* add new_rules to cur_rules_map *)
        List.fold_left 
          (fun acc_map (name, pre_rule) -> RuleMap.add name !!pre_rule acc_map) 
          cur_rules_map 
          new_rules
      )
      f start_rules

    let contains_true = function
      | None -> false
      | Some false -> false
      | Some true -> true

    let compute_nullables grm = 
      let reachable_rules = get_reachable grm in
      let eq fx x = fx = x in
      let rec compute_null name ps_lists is_null acc_nulls =
        let p_null = function
          | Epsilon -> true
          | Empty 
          | Lit _ -> false
          | NT s -> 
              if NullMap.mem s acc_nulls 
              then contains_true (NullMap.find s acc_nulls)
              else false
        in
        match ps_lists with 
        | [] -> is_null
        | ps_list :: ps_lists ->
            if List.for_all p_null ps_list && ps_list != []
            then Some true
            else compute_null name ps_lists is_null acc_nulls
      in
      let g name pre_rule acc_nulls =
        match !!pre_rule with
        | Rule ps_lists -> 
            let is_nullable = compute_null name ps_lists None acc_nulls in
            NullMap.add name is_nullable acc_nulls
        | _ -> raise Error
      in
      let f x =
        (* pass each rule and compute nullability status of all symbols;
         * if a symbol has a rule S -> [[ε];...] then its nullable or if
         * it references a rule already known to be nullable
         *)
        RuleMap.fold g reachable_rules x in
      fix eq f NullMap.empty

    let derive_x_nt x name = "d" ^ String.make 1 x ^ "["^name^"]"

    let is_empty_pre ps_lists = 
      List.for_all (List.mem Empty) ps_lists


    let remove_empty ps_lists rules = 
      let rec loop acc = function
        | [] -> List.rev acc
        | ps :: ps_rest -> 
            if List.exists (function 
                  | NT r -> not(RuleMap.mem r rules)
                  | _ -> false
                ) ps
            then loop acc ps_rest
            else loop (ps :: acc) ps_rest
      in
      Rule (loop [] ps_lists)


    let prune_rules rules =
      let prunef acc_rulesf =
        let f name pre_rule acc_rules = 
          match !!pre_rule with
          | Rule ps_lists -> 
              if is_empty_pre ps_lists 
              then acc_rules
              else 
                RuleMap.add name (remove_empty ps_lists acc_rulesf) acc_rules
          | _ -> raise Lazy_error
        in
          RuleMap.fold f acc_rulesf RuleMap.empty in
      in 
        fix (=) prunef rules in

    (* A call 'derive x grm' constructs (lazily) a new grammar that corresponds
     * to grm after x has be accepted. *)
    let derive_grm x grm = 
      let derive_rule rule_name pre_rule = 
        (*print_endline ("derive_rule called for " ^ rule_name);*)
        let null_map = compute_nullables grm in
        let rec f acc = function 
          | [] -> acc
          | Epsilon :: ps -> f acc ps
          | Empty :: _ -> acc
          | Lit c :: ps -> 
              if c = x
              then 
                if ps = [] then [Epsilon] :: acc
                else ps :: acc
              else acc
          | NT s :: ps ->
              match NullMap.find s null_map with
              | Some false
              | None -> (NT (derive_x_nt x s) :: ps) :: acc
              | Some true -> 
                  f ((NT (derive_x_nt x s) :: ps) :: acc) ps
        in 
        match pre_rule with
        | Rule ps_lists -> Rule (List.fold_left f [] ps_lists)
        | _ -> raise Lazy_error
      in
      let lazy_derive_rule rule_name pre_rule acc_rules = 
        begin
          (*print_endline ("lazy_derive for " ^ rule_name);*)
          RuleMap.add 
          (derive_x_nt x rule_name) 
          (Derived (lazy (derive_rule rule_name pre_rule)))
          acc_rules
        end
      in
      begin
        let reachable_rules = get_reachable grm in
        let good_rules = prune_rules reachable_rules in
        (* for each reachable rule, construct the derived rule and add it to the
         * grammar given *)
        {start = derive_x_nt x grm.start;
         rules = RuleMap.fold lazy_derive_rule good_rules grm.rules 
        }
      end



    let add_rule name p_rule grm =
      {grm with 
        rules = RuleMap.add name p_rule grm.rules;
      }

    let nop = Rule []
    let (+|) (Rule ps_lists) ps_list = Rule (ps_list :: ps_lists)
    let (+>) grm (name, p_rule) = add_rule name p_rule grm

    let explode str =
      let s_len = String.length str in
      let rec loop n =
        if n = s_len then []
        else str.[n] :: loop (n + 1)
      in
        loop 0

    let recognize str grm = 
      begin
        print_endline ("Trying to recognize string: " ^ str);
        let rec loop grm = function
          | [] -> 
              begin
                print_endline "\nDone deriving; resulting grammar:";
                print_endline ("start: " ^ grm.start);
                print_endline (string_of_rules grm.rules);
                print_endline ("Checking for nullability...");
                let res = NullMap.find grm.start (compute_nullables grm) in
                print_endline (string_of_bool (Some true = res));
              end
          | c :: cs -> 
              begin
                print_string (String.make 1 c);
                flush stdout;
                loop (derive_grm c grm) cs
              end
        in
          loop grm (explode str)
      end
  end

let s_grm =
  let open Grammar in
  add_rule "Q" (Rule [[Epsilon]]) (
  add_rule "S" (Rule [
    [NT "Q"]; 
    [NT "S"; Lit '('; NT "S"; Lit ')']
    ]) (make_grm "S")
  )

let list_grm =
  let open Grammar in
  (make_grm "S") +> 
  ("List", nop 
    +| [Lit 'x']
    +| [NT "List"; Lit ';'; Lit 'x'])



let exp_grm =
  let open Grammar in
  (make_grm "Exp") +>
  ("Exp", nop
   +| [NT "Num"]
   +| [NT "Exp"; Lit '+'; NT "Exp"]) +>
  ("Num", nop
   +| [NT "Digit"]
   +| [NT "Num"; NT "Digit"]) +>
  ("Digit", nop
   +| [Lit '0']
   +| [Lit '1']
   +| [Lit '2']
   +| [Lit '3']
   +| [Lit '4']
   +| [Lit '5']
   +| [Lit '6']
   +| [Lit '7']
   +| [Lit '8']
   +| [Lit '9']
  )


let gtree_grm =
  let open Grammar in
  (make_grm "GT") +>
  ("GT", nop 
  +| [NT "NODE_TYPE"; Lit '['; NT "GT_LIST"; Lit ']']) +>
  ("NODE_TYPE", nop
  +| [NT "CHAR"; NT "NODE_TYPE"]
  +| [NT "CHAR"]) +>
  ("GT_LIST", nop
  +| [Epsilon]
  +| [NT "GT_ONE"]) +>
  ("GT_ONE", nop
  +| [NT "GT"]
  +| [NT "GT"; Lit ','; NT "GT_ONE"]) +>
  ("CHAR", nop
  +| [Lit 'a']
  +| [Lit 'b']
  +| [Lit 'c']
  +| [Lit 'd']
  +| [Lit 'e']
  +| [Lit 'f']
  +| [Lit 'g']
  +| [Lit 'h']
  +| [Lit 'i']
  +| [Lit 'j']
  +| [Lit 'k']
  +| [Lit 'l']
  +| [Lit 'm']
  +| [Lit 'n']
  +| [Lit 'o']
  +| [Lit 'p']
  +| [Lit 'q']
  +| [Lit 'r']
  +| [Lit 's']
  +| [Lit 't']
  +| [Lit 'u']
  +| [Lit 'v']
  +| [Lit 'x']
  +| [Lit 'y']
  +| [Lit 'z']
  +| [Lit '0']
  +| [Lit '1']
  +| [Lit '2']
  +| [Lit '3']
  +| [Lit '5']
  +| [Lit '6']
  +| [Lit '7']
  +| [Lit '8']
  +| [Lit '9'])

let () = begin
  let res = Grammar.recognize "statement[const[int[a[]]],const[]]" gtree_grm in
  res
  (*print_endline (string_of_bool (res = Some true))*)
end
