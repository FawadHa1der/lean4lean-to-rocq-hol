
type unit0 =
| Tt

type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type sumbool =
| Left
| Right

type uint =
| Nil0
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

val revapp : uint -> uint -> uint

val rev : uint -> uint

module Little :
 sig
  val succ : uint -> uint
 end

type uint0 =
| Nil1
| D10 of uint0
| D11 of uint0
| D12 of uint0
| D13 of uint0
| D14 of uint0
| D15 of uint0
| D16 of uint0
| D17 of uint0
| D18 of uint0
| D19 of uint0
| Da of uint0
| Db of uint0
| Dc of uint0
| Dd of uint0
| De of uint0
| Df of uint0

type uint1 =
| UIntDecimal of uint
| UIntHexadecimal of uint0

val pred : nat -> nat

val add : nat -> nat -> nat

val sub : nat -> nat -> nat

val tail_add : nat -> nat -> nat

val tail_addmul : nat -> nat -> nat -> nat

val tail_mul : nat -> nat -> nat

val of_uint_acc : uint -> nat -> nat

val of_uint : uint -> nat

val of_hex_uint_acc : uint0 -> nat -> nat

val of_hex_uint : uint0 -> nat

val of_num_uint : uint1 -> nat

val eqb : bool -> bool -> bool

module type EqLtLe =
 sig
  type t
 end

module MakeOrderTac :
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 sig
 end

module Nat :
 sig
  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val to_little_uint : nat -> uint -> uint

  val to_uint : nat -> uint
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val seq : nat -> nat -> nat list

val firstn : nat -> 'a1 list -> 'a1 list

val skipn : nat -> 'a1 list -> 'a1 list

val nth_error : 'a1 list -> nat -> 'a1 option

val rev0 : 'a1 list -> 'a1 list

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val find : ('a1 -> bool) -> 'a1 list -> 'a1 option

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val pred_N : positive -> n

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool

  val coq_Nsucc_double : n -> n

  val coq_Ndouble : n -> n

  val coq_lor : positive -> positive -> positive

  val coq_land : positive -> positive -> n

  val coq_lxor : positive -> positive -> n

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_succ_nat : nat -> positive
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool

  val of_succ_nat : nat -> positive

  val pow : positive -> positive -> positive

  val size_nat : positive -> nat

  val size : positive -> positive

  val gcdn : nat -> positive -> positive -> positive

  val gcd : positive -> positive -> positive

  val shiftl : positive -> n -> positive

  val eq_dec : positive -> positive -> sumbool
 end

module N :
 sig
  val succ_double : n -> n

  val double : n -> n

  val sub : n -> n -> n

  val compare : n -> n -> comparison

  val leb : n -> n -> bool

  val pos_div_eucl : positive -> n -> (n, n) prod

  val coq_lor : n -> n -> n

  val coq_land : n -> n -> n

  val coq_lxor : n -> n -> n

  val succ : n -> n

  val pred : n -> n

  val add : n -> n -> n

  val mul : n -> n -> n

  val eqb : n -> n -> bool

  val ltb : n -> n -> bool

  val max : n -> n -> n

  val div2 : n -> n

  val pow : n -> n -> n

  val log2 : n -> n

  val div_eucl : n -> n -> (n, n) prod

  val div : n -> n -> n

  val modulo : n -> n -> n

  val gcd : n -> n -> n

  val shiftl : n -> n -> n

  val shiftr : n -> n -> n

  val to_nat : n -> nat

  val of_nat : nat -> n

  val eq_dec : n -> n -> sumbool
 end

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val eqb0 : ascii -> ascii -> bool

val n_of_digits : bool list -> n

val n_of_ascii : ascii -> n

val nat_of_ascii : ascii -> nat

type string =
| EmptyString
| String of ascii * string

val eqb1 : string -> string -> bool

val append : string -> string -> string

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val eqb : z -> z -> bool

  val max : z -> z -> z

  val eq_dec : z -> z -> sumbool
 end

type name =
| NameAnon
| NameStr of name * string
| NameNum of name * n

val name_eqb : name -> name -> bool

val list_eqb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val name_mem : name -> name list -> bool

val names_unique : name list -> bool

type level =
| LZero
| LSucc of level
| LMax of level * level
| LIMax of level * level
| LParam of name
| LMVar of name

val level_eqb : level -> level -> bool

val level_wf : name list -> level -> bool

val level_has_meta : level -> bool

val lookup_level : name list -> level list -> name -> level

val subst_level : name list -> level list -> level -> level

type binder_info =
| BDefault
| BImplicit
| BStrictImplicit
| BInstImplicit

type literal =
| LitNat of n
| LitString of string

type expr =
| EBVar of nat
| EFVar of name
| EMVar of name
| ESort of level
| EConst of name * level list
| EApp of expr * expr
| ELam of name * binder_info * expr * expr
| EPi of name * binder_info * expr * expr
| ELet of name * expr * expr * expr * bool
| ELit of literal
| EProj of name * nat * expr
| EMData of expr

val literal_eqb : literal -> literal -> bool

val expr_eqb : expr -> expr -> bool

val lift : nat -> nat -> expr -> expr

val subst : nat -> expr -> expr -> expr

val instantiate : expr -> expr -> expr

val subst_many : nat -> expr list -> expr -> expr

val instantiate_many : expr -> expr list -> expr

val subst_levels : name list -> level list -> expr -> expr

val scoped : nat -> expr -> bool

type binding = { binding_type : expr; binding_value : expr option }

type context = { bound_context : binding list;
                 free_context : (name, binding) prod list }

val empty_context : context

val push_binding : context -> expr -> expr option -> context

val find_free : name -> (name, binding) prod list -> binding option

type inductive_data = { ind_num_params : nat; ind_num_indices : nat;
                        ind_all : name list; ind_ctors : name list;
                        ind_num_nested : nat; ind_is_rec : bool;
                        ind_is_reflexive : bool; ind_is_unsafe : bool }

type constructor_data = { ctor_induct : name; ctor_index : nat;
                          ctor_num_params : nat; ctor_num_fields : nat;
                          ctor_is_unsafe : bool }

type recursor_rule = { rule_ctor : name; rule_nfields : nat; rule_rhs : expr }

type recursor_data = { rec_all : name list; rec_num_params : nat;
                       rec_num_indices : nat; rec_num_motives : nat;
                       rec_num_minors : nat; rec_rules : recursor_rule list;
                       rec_k : bool; rec_is_unsafe : bool }

type primitive_kind =
| PNatAdd
| PNatPred
| PNatSub
| PNatMul
| PNatPow
| PNatGcd
| PNatMod
| PNatDiv
| PNatBEq
| PNatBLE
| PNatLAnd
| PNatLOr
| PNatXor
| PNatBitwise
| PNatShiftLeft
| PNatShiftRight
| PCharOfNat
| PStringOfList

val primitive_kind_eqb : primitive_kind -> primitive_kind -> bool

type quotient_kind =
| QType
| QCtor
| QLift
| QInd

type decl_kind =
| DAssumption
| DDefinition
| DTheorem
| DOpaque
| DUnsupported
| DInductive of inductive_data
| DConstructor of constructor_data
| DRecursor of recursor_data
| DPrimitive of primitive_kind
| DQuotient of quotient_kind
| DUnsafe of decl_kind
| DPartial

type reducibility_hints =
| HintOpaque
| HintAbbrev
| HintRegular of n

val hints_lt : reducibility_hints -> reducibility_hints -> bool

type declaration = { decl_name : name; decl_params : name list;
                     decl_type : expr; decl_value : expr option;
                     decl_kind_of : decl_kind; decl_hints : reducibility_hints }

val effective_hints : declaration -> reducibility_hints

type environment = declaration list

val find_decl : name -> environment -> declaration option

type reject_reason =
| UnknownConstant
| UnknownFreeVariable
| LooseBoundVariable
| UnknownUniverse
| UniverseArity
| ExpectedSort
| ExpectedPi
| TypeMismatch
| NotDefinitionallyEqual
| DuplicateDeclaration
| DuplicateUniverse
| MalformedDeclaration
| MetaVariable

type decline_reason =
| OutOfFuel
| UnsupportedExpression
| UnsupportedDeclaration

type 'a result =
| Accept of 'a
| Reject of reject_reason
| Decline of decline_reason

val bind : 'a1 result -> ('a1 -> 'a2 result) -> 'a2 result

val require : bool -> reject_reason -> unit0 result

val instantiate_levels : name list -> level list -> expr -> expr

type reduction_mode =
| NormalReduction
| EagerReduction

val has_external_local_at : nat -> expr -> bool

val has_external_local : expr -> bool

val nat_probe_allowed : reduction_mode -> expr -> expr -> bool

val true_probe_allowed : reduction_mode -> expr -> bool

val eager_reduce_name : name

val is_eager_reduce_argument : expr -> bool

type sublevel =
| SubConst of name list * nat
| SubVar of name list * name * nat

val guard_insert : name -> name list -> name list

val const_atom : name list -> nat -> sublevel list

val combine_levels :
  sublevel list result -> sublevel list result -> sublevel list result

val normalize_aux : nat -> level -> name list -> nat -> sublevel list result

val normalize_level : nat -> level -> sublevel list result

val guard_subset : name list -> name list -> bool

val sublevel_le : sublevel -> sublevel -> bool

val sublevels_le : sublevel list -> sublevel list -> bool

val level_le : nat -> level -> level -> bool result

val level_equiv : nat -> level -> level -> bool result

val levels_equiv : nat -> level list -> level list -> bool result

val nat_probe_head :
  (name -> environment -> declaration option) -> name -> environment ->
  (expr, expr list) prod -> bool

val pair_probe_guard : bool -> bool -> (unit0 -> bool) -> bool

val normal_whnf_rounds : nat

val eager_whnf_rounds : nat

val whnf_round_limit : reduction_mode -> nat

type whnf_round =
| WhnfDone of expr
| WhnfContinue of expr

val run_whnf_rounds :
  nat -> (expr -> whnf_round result) -> expr -> expr result

val core_name : string -> name

val core_nat_name : name

val core_zero_name : name

val core_succ_name : name

val core_bool_name : name

val core_false_name : name

val core_true_name : name

val core_char_name : name

val core_char_of_nat : name

val core_string_name : name

val core_string_of_list : name

val core_list_name : name

val core_nat : expr

val core_spine : expr -> expr list -> (expr, expr list) prod

val core_apps : expr -> expr list -> expr

val core_occurs : nat -> expr -> bool

val core_level_positive : level -> bool

val core_inductive : environment -> name -> inductive_data option

val core_constructor : environment -> name -> constructor_data option

val core_structure : environment -> name -> bool

val core_ctor_shape :
  environment -> name -> name -> nat -> nat -> expr -> bool

val core_nat_ready : environment -> bool

val core_bool_ready : environment -> bool

val core_string_ready : environment -> bool

val core_supported : environment -> expr -> bool

val check_level : name list -> level -> unit0 result

val check_levels : name list -> level list -> unit0 result

val get_constant :
  environment -> name list -> name -> level list -> declaration result

type methods = { infer_method : (context -> expr -> expr result);
                 infer_type_method : (context -> expr -> expr result);
                 whnf_method : (context -> expr -> expr result);
                 whnf_core_method : (bool -> context -> expr -> expr result);
                 defeq_method : (context -> expr -> expr -> bool result);
                 method_mode : reduction_mode;
                 eager_defeq_method : (context -> expr -> expr -> bool result) }

val inference_only : methods -> methods

val application_type_defeq :
  methods -> context -> expr -> expr -> expr -> bool result

val sort_of : methods -> context -> expr -> level result

val core_apply_type : methods -> context -> expr -> expr list -> expr result

val core_projection_field :
  methods -> nat -> context -> name -> expr -> bool -> nat -> nat -> expr ->
  expr result

val core_infer_projection :
  methods -> nat -> environment -> context -> name -> nat -> expr -> expr
  result

val core_nat_value : expr -> n option

val core_nat_constructor : n -> expr

val core_shiftr : nat -> n -> n -> n result

val core_binary_nat :
  nat -> environment -> primitive_kind -> n -> n -> expr option result

val core_reduce_nat :
  methods -> nat -> environment -> context -> expr -> expr option result

val core_cont : ascii -> bool

val core_digit : ascii -> n

val core_append_digit : n -> ascii -> n

val core_utf8 : string -> n list option

val core_char_list : n list -> expr

val core_expand_string : string -> expr result

val core_major_induct : nat -> expr -> name option

val core_make_structure :
  environment -> name -> level list -> expr list -> expr -> expr option

val core_to_constructor :
  methods -> nat -> environment -> context -> name -> bool -> expr -> expr
  result

val core_find_rule : name -> recursor_rule list -> recursor_rule option

val core_reduce_recursor :
  methods -> nat -> environment -> context -> expr -> expr option result

val core_reduce_projection_with :
  methods -> (context -> expr -> expr result) -> environment -> context ->
  name -> nat -> expr -> expr option result

val core_reduce_projection :
  methods -> environment -> context -> name -> nat -> expr -> expr option
  result

val core_reduce_quotient :
  methods -> environment -> context -> expr -> expr option result

val infer_step :
  methods -> nat -> environment -> name list -> bool -> context -> expr ->
  expr result

val core_beta_collect : expr -> expr list -> expr list -> expr

val core_beta : expr -> expr list -> expr

val core_unfold : environment -> name list -> expr -> expr option result

val whnf_core_step :
  methods -> nat -> environment -> name list -> bool -> context -> expr ->
  expr result

val finish_whnf_unfold : environment -> name list -> expr -> whnf_round result

val whnf_round_step :
  methods -> nat -> environment -> name list -> context -> expr -> whnf_round
  result

val whnf_loop :
  nat -> methods -> nat -> environment -> name list -> context -> expr ->
  expr result

val eta_compare : methods -> context -> expr -> expr -> expr -> bool result

val core_alpha : nat -> expr -> expr -> (bool, nat) prod

val core_alpha_eq : expr -> expr -> bool

val core_compare_args :
  methods -> context -> expr list -> expr list -> bool result

val core_same_head : nat -> expr -> expr -> bool result

val core_congruent_apps :
  methods -> nat -> context -> expr -> expr -> bool result

val core_delta_info : environment -> expr -> declaration option

val core_delta_sides : environment -> expr -> expr -> (bool, bool) prod

val core_erasing_delta : environment -> expr -> bool

val core_delta_congruent :
  methods -> nat -> environment -> context -> expr -> expr -> bool result

val compare_heads : methods -> nat -> context -> expr -> expr -> bool result

val core_compare_fields :
  methods -> context -> name -> expr -> nat -> expr list -> bool result

val core_structure_eta :
  methods -> environment -> context -> expr -> expr -> bool result

val core_unit_like :
  methods -> environment -> context -> expr -> expr -> bool result

val core_try_string_expansion :
  methods -> context -> expr -> expr -> bool option result

val core_compare_fallback :
  methods -> nat -> environment -> context -> expr -> expr -> bool result

val compare_after_whnf :
  methods -> nat -> environment -> context -> expr -> expr -> bool result

val core_quick :
  methods -> nat -> context -> expr -> expr -> bool option result

val core_proof_irrel :
  methods -> nat -> context -> expr -> expr -> bool option result

type conversion_progress =
| ConversionDone of bool
| ConversionStuck of expr * expr

val core_offset :
  methods -> environment -> context -> expr -> expr -> bool option result

val core_try_unfold_proj_app :
  methods -> context -> expr -> expr option result

val core_opposite_projection :
  methods -> environment -> context -> expr -> expr -> (expr, expr) prod
  option result

val core_lazy_delta :
  nat -> methods -> nat -> environment -> name list -> context -> expr ->
  expr -> conversion_progress result

val core_finish_conversion :
  methods -> nat -> environment -> context -> expr -> expr -> bool result

val core_is_true : expr -> bool

val core_true_shortcut :
  methods -> environment -> context -> expr -> expr -> bool result

val defeq_step :
  methods -> nat -> environment -> name list -> context -> expr -> expr ->
  bool result

val checker_mode :
  reduction_mode -> nat -> environment -> name list -> methods

val checker : nat -> environment -> name list -> methods

val infer : nat -> environment -> name list -> context -> expr -> expr result

val whnf : nat -> environment -> name list -> context -> expr -> expr result

val defeq :
  nat -> environment -> name list -> context -> expr -> expr -> bool result

val check :
  nat -> environment -> name list -> context -> expr -> expr -> unit0 result

val check_defeq :
  nat -> environment -> name list -> context -> expr -> expr -> unit0 result

type ind_local = { il_id : name; il_user : name; il_binder : binder_info;
                   il_type : expr }

type ind_state = { ist_next : nat; ist_context : context }

val initial_ind_state : ind_state

val local_expr : ind_local -> expr

val local_exprs : ind_local list -> expr list

val ind_fresh :
  ind_state -> name -> binder_info -> expr -> (ind_local, ind_state) prod

val abstract_local : name -> nat -> expr -> expr

val close_pi : ind_local list -> expr -> expr

val close_lam : ind_local list -> expr -> expr

val apply_exprs : expr -> expr list -> expr

val apply_locals : expr -> ind_local list -> expr

val split_app_aux : expr -> expr list -> (expr, expr list) prod

val split_app : expr -> (expr, expr list) prod

val has_inductive : name list -> expr -> bool

val raw_arity : expr -> nat

val recursive_constructor : name list -> expr -> bool

val reflexive_constructor : name list -> expr -> bool

val level_never_zero : level -> bool

val ind_sort :
  nat -> environment -> name list -> ind_state -> expr -> level result

val consume_type_annotations : expr -> expr

val checked_domain :
  nat -> environment -> name list -> ind_state -> expr -> expr result

val open_telescope :
  nat -> nat -> environment -> name list -> ind_state -> expr -> ((ind_local
  list, expr) prod, ind_state) prod result

val open_parameters :
  nat -> nat -> environment -> name list -> ind_state -> expr -> ((ind_local
  list, expr) prod, ind_state) prod result

val apply_parameters :
  ind_local list -> nat -> environment -> name list -> ind_state -> expr ->
  expr result

val primitive_name : primitive_kind -> name

val primitive_kinds : primitive_kind list

val primitive_lookup : name -> primitive_kind option

val primitive_bitwise_name : name

val primitive_bool : expr

val primitive_char : expr

val primitive_string : expr

val primitive_list_char : expr

val primitive_arrow : expr -> expr -> expr

val primitive_signature : primitive_kind -> expr

val primitive_zero : expr

val primitive_succ : expr -> expr

val primitive_one : expr

val primitive_two : expr

val primitive_true : expr

val primitive_false : expr

val primitive_call : primitive_kind -> expr list -> expr

val primitive_check_signature : nat -> expr -> expr -> unit0 result

val primitive_authenticated :
  nat -> environment -> primitive_kind -> unit0 result

val primitive_dependencies :
  nat -> environment -> primitive_kind -> unit0 result

val primitive_closed : nat -> nat -> expr -> unit0 result

type primitive_equation = { primitive_context : context;
                            primitive_lhs : expr; primitive_rhs : expr }

val primitive_equation_at : context -> expr -> expr -> primitive_equation

val primitive_x_context : context

val primitive_xy_context : context

val primitive_equations :
  primitive_kind -> expr -> primitive_equation list option

val primitive_check_equations :
  nat -> nat -> environment -> primitive_equation list -> unit0 result

val primitive_path : string list -> name

val primitive_const : string list -> level list -> expr

module PrimitiveQuote :
 sig
  type term = nat -> expr

  val embed : expr -> term

  val app : term -> term -> term

  val apps : term -> term list -> term

  val lam : term -> (term -> term) -> term

  val pi : term -> (term -> term) -> term

  val arrow : term -> term -> term

  val run : term -> expr

  val const : string list -> level list -> term

  val prop : term

  val type0 : term

  val nat : term

  val bool : term

  val tru : term

  val fal : term

  val zero : term

  val one : term

  val two : term

  val succ : term -> term

  val call : primitive_kind -> term list -> term

  val eq : term -> term -> term -> term

  val refl : term -> term -> term

  val not : term -> term

  val dec : term -> term

  val is_true : term -> term -> term

  val is_false : term -> term -> term

  val ite : term -> term -> term -> term -> term -> term

  val dite : term -> term -> term -> (term -> term) -> (term -> term) -> term

  val bool_dec : term -> term
 end

module PQ :
 sig
  type term = nat -> expr

  val embed : expr -> term

  val app : term -> term -> term

  val apps : term -> term list -> term

  val lam : term -> (term -> term) -> term

  val pi : term -> (term -> term) -> term

  val arrow : term -> term -> term

  val run : term -> expr

  val const : string list -> level list -> term

  val prop : term

  val type0 : term

  val nat : term

  val bool : term

  val tru : term

  val fal : term

  val zero : term

  val one : term

  val two : term

  val succ : term -> term

  val call : primitive_kind -> term list -> term

  val eq : term -> term -> term -> term

  val refl : term -> term -> term

  val not : term -> term

  val dec : term -> term

  val is_true : term -> term -> term

  val is_false : term -> term -> term

  val ite : term -> term -> term -> term -> term -> term

  val dite : term -> term -> term -> (term -> term) -> (term -> term) -> term

  val bool_dec : term -> term
 end

type primitive_reflection = { reflection_type : expr; reflection_true : 
                              expr; reflection_false : expr;
                              reflection_dec : expr }

val primitive_reflection_type : bool -> expr

val primitive_reflection_make : bool -> primitive_reflection

val primitive_reflection_ite : primitive_reflection -> expr

val primitive_reflection_dite : primitive_reflection -> expr

val primitive_eq_closed :
  nat -> environment -> PQ.term -> PQ.term -> unit0 result

val primitive_check_closed :
  nat -> environment -> PQ.term -> PQ.term -> unit0 result

val primitive_check_reflection :
  nat -> environment -> primitive_reflection -> bool -> bool -> unit0 result

type primitive_condition =
| PCBool
| PCNatLE
| PCNatEq

val primitive_condition_prop : primitive_condition -> expr

val primitive_condition_dec : primitive_condition -> expr

val primitive_condition_ite :
  primitive_condition -> PQ.term -> PQ.term list -> PQ.term -> PQ.term ->
  PQ.term

val primitive_condition_dite :
  primitive_condition -> PQ.term list -> (PQ.term -> PQ.term) -> (PQ.term ->
  PQ.term) -> PQ.term

val primitive_condition_decide :
  primitive_condition -> PQ.term list -> PQ.term

val primitive_condition_proof : primitive_condition -> expr

val primitive_check_condition :
  nat -> environment -> primitive_condition -> bool -> bool -> unit0 result

val primitive_go_name : bool -> name

val primitive_le : PQ.term -> PQ.term -> PQ.term

val primitive_go_type : expr

val primitive_fuel_top : bool -> expr

val primitive_fuel_step : bool -> bool -> expr

val primitive_check_fuel_rec :
  nat -> environment -> bool -> expr -> unit0 result

val primitive_whnf_core : nat -> environment -> context -> expr -> expr result

val primitive_unfold : environment -> expr -> expr result

val primitive_lambda_telescope :
  nat -> nat -> environment -> ind_state -> expr -> ((ind_local list, expr)
  prod, ind_state) prod result

val primitive_no_free : nat -> name -> expr -> unit0 result

val primitive_proof : nat -> environment -> context -> expr -> unit0 result

type primitive_probe = { probe_pack : expr; probe_dom : expr;
                         probe_functional : expr }

val primitive_check_go :
  nat -> environment -> ind_state -> expr -> unit0 result

val primitive_unfold_nat_well_founded :
  nat -> environment -> ind_state -> expr -> expr -> primitive_probe result

val primitive_run_probe :
  nat -> environment -> ind_state -> primitive_probe -> expr list -> (expr ->
  expr) -> unit0 result

val primitive_first_measure : expr

val primitive_check_gcd : nat -> environment -> expr -> unit0 result

val primitive_bool_operator_type : expr

val primitive_check_bitwise : nat -> environment -> expr -> unit0 result

val primitive_check_boolean_operator :
  nat -> environment -> primitive_kind -> expr -> unit0 result

val primitive_check_bitwise_instance :
  nat -> environment -> primitive_kind -> expr -> unit0 result

val primitive_is_text : primitive_kind -> bool

val primitive_ensure_type : nat -> environment -> expr -> unit0 result

val primitive_check_text_interface :
  nat -> environment -> primitive_kind -> unit0 result

val primitive_check_nat_equations :
  nat -> environment -> primitive_kind -> expr -> unit0 result

val classify_primitive :
  nat -> environment -> name -> name list -> expr -> expr -> primitive_kind
  option result

val nat_name : name

val bool_name : name

val reserved_names : name list

type input_safety =
| InputSafe
| InputPartial
| InputUnsafe

type input_decl =
| InputAxiom of name * name list * expr * bool
| InputDefinition of reducibility_hints * name * name list * expr * expr
   * input_safety
| InputTheorem of name * name list * expr * expr
| InputOpaque of name * name list * expr * expr * bool
| InputUnsupported

val check_header :
  nat -> environment -> name -> name list -> expr -> unit0 result

val check_proposition :
  nat -> environment -> name list -> expr -> unit0 result

val checked_constant :
  nat -> environment -> name -> name list -> expr -> expr option -> decl_kind
  -> environment result

val admit : nat -> environment -> input_decl -> environment result

type ind_spec = { spec_decl : declaration; spec_ctors : declaration list }

type ind_checked = { checked_spec : ind_spec;
                     checked_indices : ind_local list; checked_level : 
                     level }

type ind_stats = { stats_params : ind_local list;
                   stats_types : ind_checked list; stats_names : name list;
                   stats_levels : level list; stats_result : level;
                   stats_unsafe : bool; stats_state : ind_state }

type ind_motive = { motive_type_info : ind_checked; motive_local : ind_local;
                    motive_major : ind_local }

type ind_recursive_arg = { ra_field : ind_local;
                           ra_arguments : ind_local list; ra_inductive : 
                           nat; ra_indices : expr list }

type ind_minor = { minor_ctor : declaration; minor_owner : nat;
                   minor_local : ind_local; minor_fields : ind_local list;
                   minor_recursive : ind_recursive_arg list }

val same_names : name list -> name list -> bool

val ind_names : declaration list -> name list

val all_ctor_names : ind_spec list -> name list

val rec_name : name -> name

val gather_ctors : name list -> declaration list -> declaration list result

val gather_specs :
  declaration list -> declaration list -> ind_spec list result

val check_primitive_inductive : name list -> nat -> ind_spec list -> bool

val check_inductive_types :
  ind_spec list -> nat -> environment -> name list -> ind_local list -> level
  option -> ind_state -> (ind_checked list, ind_state) prod result

val valid_ind_app_at :
  ind_checked list -> ind_stats -> expr -> expr list -> nat -> nat option

val valid_ind_app : ind_stats -> expr -> nat option

val ind_app_indices : ind_stats -> expr -> expr list

val check_positive :
  nat -> nat -> environment -> name list -> ind_stats -> ind_state -> expr ->
  unit0 result

val derived_inductive : ind_stats -> ind_checked -> declaration

val inductive_data_eqb : inductive_data -> inductive_data -> bool

val constructor_data_eqb : constructor_data -> constructor_data -> bool

val map_result : ('a1 -> 'a2 result) -> 'a1 list -> 'a2 list result

val check_field :
  nat -> environment -> name list -> ind_stats -> ind_state -> ind_local ->
  unit0 result

val check_ctors :
  declaration list -> name -> nat -> nat -> environment -> name list ->
  ind_stats -> ind_state -> (declaration list, ind_state) prod result

val check_all_ctors :
  ind_checked list -> nat -> environment -> name list -> ind_stats ->
  ind_state -> (declaration list, ind_state) prod result

val large_elimination :
  nat -> environment -> name list -> ind_stats -> ind_state -> bool result

val k_target : nat -> ind_stats -> bool result

val fresh_elim_name : nat -> nat -> name list -> name result

val build_motives :
  ind_checked list -> ind_stats -> level -> ind_state -> (ind_motive list,
  ind_state) prod

val build_recursive_args :
  ind_local list -> nat -> environment -> name list -> ind_stats -> ind_state
  -> (ind_recursive_arg list, ind_state) prod result

val build_ihs :
  ind_recursive_arg list -> ind_motive list -> ind_state -> (ind_local list,
  ind_state) prod result

val build_minors :
  declaration list -> nat -> nat -> environment -> name list -> ind_stats ->
  ind_motive list -> ind_state -> (ind_minor list, ind_state) prod result

val build_all_minors :
  ind_checked list -> nat -> nat -> environment -> name list -> ind_stats ->
  ind_motive list -> ind_state -> (ind_minor list, ind_state) prod result

val recursive_value :
  ind_stats -> level list -> ind_motive list -> ind_minor list ->
  ind_recursive_arg -> expr result

val build_rule :
  ind_stats -> level list -> ind_motive list -> ind_minor list -> ind_minor
  -> recursor_rule result

val build_recursor :
  ind_stats -> name list -> ind_motive list -> ind_minor list -> bool -> nat
  -> ind_motive -> declaration result

val build_recursors :
  ind_motive list -> nat -> ind_stats -> name list -> ind_motive list ->
  ind_minor list -> bool -> declaration list result

val rule_eqb :
  name list -> name list -> recursor_rule -> recursor_rule -> bool

val recursor_data_eqb :
  name list -> name list -> recursor_data -> recursor_data -> bool

val verify_rec_metadata : declaration -> declaration -> unit0 result

val derive_inductive :
  nat -> environment -> name list -> nat -> ind_spec list -> declaration list
  result

val verify_member_metadata : declaration -> declaration -> unit0 result

val verify_members : declaration list -> declaration list -> unit0 result

val prepare_inductive :
  environment -> declaration list -> declaration list -> declaration list ->
  ((name list, nat) prod, ind_spec list) prod result

val checking_view : input_safety -> declaration -> declaration

val safety_environment : input_safety -> declaration list -> declaration list

module NilEmpty :
 sig
  val string_of_uint : uint -> string
 end

module NilZero :
 sig
  val string_of_uint : uint -> string
 end

type nested_elimination = { nested_params : ind_local list;
                            nested_context : context;
                            nested_specs : ind_spec list;
                            nested_mapping : (expr, name) prod list;
                            nested_aux_names : name list;
                            nested_aux_count : nat }

type nested_work = { nw_specs : ind_spec list;
                     nw_mapping : (expr, name) prod list; nw_next_aux : 
                     nat; nw_next_local : nat }

val nested_set_specs : nested_work -> ind_spec list -> nested_work

val nested_set_local : nested_work -> nat -> nested_work

val nested_open_params :
  nat -> nat -> ind_state -> expr -> ((ind_local list, expr) prod, ind_state)
  prod result

val nested_instantiate_params : nat -> expr list -> expr -> expr result

val nested_lookup_local :
  nat -> name -> ind_local list -> ind_local list -> expr result

val nested_rebase :
  nat -> ind_local list -> ind_local list -> expr -> expr result

val nested_has_new : nat -> name list -> expr -> bool result

val nested_any_new : nat -> name list -> expr list -> bool result

val nested_candidate :
  nat -> environment -> nested_work -> expr -> (((declaration,
  inductive_data) prod, level list) prod, expr list) prod option result

val nested_same_flags : nat -> expr -> expr -> bool result

val nested_key_eq : nat -> expr -> expr -> bool result

val nested_find_mapping :
  nat -> expr -> (expr, name) prod list -> name option result

val nested_replace_prefix : nat -> name -> name -> name -> name result

val nested_aux_name : nat -> name

val nested_unique_aux :
  nat -> name list -> name -> name list -> nat -> ((name, name list) prod,
  nat) prod result

val nested_used_names : environment -> nested_work -> name list

val nested_make_ctors :
  nat -> environment -> name list -> ind_local list -> level list -> expr
  list -> name -> name list -> name list -> nat -> declaration list result

val nested_expand_family :
  nat -> environment -> name list -> ind_local list -> ind_local list ->
  level list -> expr list -> name list -> nested_work -> nested_work result

val nested_replace_root :
  nat -> environment -> name list -> ind_local list -> ind_local list -> expr
  -> nested_work -> (expr option, nested_work) prod result

val nested_rewrite :
  nat -> environment -> name list -> ind_local list -> ind_local list -> expr
  -> nested_work -> (expr, nested_work) prod result

val nested_rewrite_ctors :
  nat -> environment -> name list -> nat -> ind_local list -> declaration
  list -> nested_work -> (declaration list, nested_work) prod result

val nested_replace_spec :
  nat -> nat -> ind_spec -> ind_spec list -> ind_spec list result

val nested_worklist :
  nat -> nat -> environment -> name list -> nat -> ind_local list ->
  nested_work -> nested_work result

val eliminate_nested :
  nat -> environment -> name list -> nat -> ind_spec list ->
  nested_elimination result

val restore_lookup : name -> (expr, name) prod list -> expr option

val restore_name : name -> (name, name) prod list -> name

val local_replacement : name -> ind_local list -> expr list -> expr option

val instantiate_locals : ind_local list -> expr list -> nat -> expr -> expr

val nested_ctor_pattern :
  environment -> nested_elimination -> name -> (expr, name) prod option

val restore_ctor_name :
  nat -> environment -> nested_elimination -> name -> name result

val rewrite_nested_head :
  nat -> environment -> nested_elimination -> (name, name) prod list -> name
  -> level list -> expr list -> expr result

val restore_nested_expr :
  nat -> environment -> nested_elimination -> (name, name) prod list -> expr
  -> expr result

val restore_open :
  nat -> ind_state -> expr -> (ind_local list, expr) prod result

val restore_nested_type :
  nat -> environment -> nested_elimination -> (name, name) prod list -> expr
  -> expr result

val indexed_rec_name : name -> nat -> name

val auxiliary_rec_names : name -> name list -> nat -> (name, name) prod list

val restore_rule :
  nat -> environment -> nested_elimination -> (name, name) prod list ->
  recursor_rule -> recursor_rule result

val restore_recursor :
  nat -> environment -> nested_elimination -> (name, name) prod list -> name
  list -> name -> declaration result

val restore_constructor :
  nat -> environment -> nested_elimination -> name -> declaration result

val restore_inductive :
  environment -> nested_elimination -> name list -> name -> declaration result

val name_prefix : name -> name -> bool

val uses_reserved_nested : expr -> bool

val admit_inductive_nested :
  nat -> environment -> declaration list -> declaration list -> declaration
  list -> environment result

val mark_unsafe_inductive : declaration -> declaration

val inductive_input_unsafe : declaration list -> bool

val admit_inductive_extended :
  nat -> environment -> declaration list -> declaration list -> declaration
  list -> environment result

module Accessor :
 sig
  val core_name : string -> name

  val core_nat_name : name

  val core_zero_name : name

  val core_succ_name : name

  val core_bool_name : name

  val core_false_name : name

  val core_true_name : name

  val core_char_name : name

  val core_char_of_nat : name

  val core_string_name : name

  val core_string_of_list : name

  val core_list_name : name

  val core_nat : expr

  val core_spine : expr -> expr list -> (expr, expr list) prod

  val core_apps : expr -> expr list -> expr

  val core_occurs : nat -> expr -> bool

  val core_level_positive : level -> bool

  val core_inductive :
    (name -> environment -> declaration option) -> environment -> name ->
    inductive_data option

  val core_constructor :
    (name -> environment -> declaration option) -> environment -> name ->
    constructor_data option

  val core_structure :
    (name -> environment -> declaration option) -> environment -> name -> bool

  val core_ctor_shape :
    (name -> environment -> declaration option) -> environment -> name ->
    name -> nat -> nat -> expr -> bool

  val core_nat_ready :
    (name -> environment -> declaration option) -> environment -> bool

  val core_bool_ready :
    (name -> environment -> declaration option) -> environment -> bool

  val core_string_ready :
    (name -> environment -> declaration option) -> environment -> bool

  val check_level : name list -> level -> unit0 result

  val check_levels : name list -> level list -> unit0 result

  val get_constant :
    (name -> environment -> declaration option) -> environment -> name list
    -> name -> level list -> declaration result

  val inference_only : methods -> methods

  val sort_of : methods -> context -> expr -> level result

  val core_apply_type : methods -> context -> expr -> expr list -> expr result

  val core_projection_field :
    methods -> nat -> context -> name -> expr -> bool -> nat -> nat -> expr
    -> expr result

  val core_infer_projection :
    (name -> environment -> declaration option) -> methods -> nat ->
    environment -> context -> name -> nat -> expr -> expr result

  val core_nat_value : expr -> n option

  val core_nat_constructor : n -> expr

  val core_shiftr : nat -> n -> n -> n result

  val core_binary_nat :
    (name -> environment -> declaration option) -> nat -> environment ->
    primitive_kind -> n -> n -> expr option result

  val core_reduce_nat :
    (name -> environment -> declaration option) -> methods -> nat ->
    environment -> context -> expr -> expr option result

  val core_cont : ascii -> bool

  val core_digit : ascii -> n

  val core_append_digit : n -> ascii -> n

  val core_utf8 : string -> n list option

  val core_char_list : n list -> expr

  val core_expand_string : string -> expr result

  val core_major_induct : nat -> expr -> name option

  val core_make_structure :
    (name -> environment -> declaration option) -> environment -> name ->
    level list -> expr list -> expr -> expr option

  val core_to_constructor :
    (name -> environment -> declaration option) -> methods -> nat ->
    environment -> context -> name -> bool -> expr -> expr result

  val core_find_rule : name -> recursor_rule list -> recursor_rule option

  val core_reduce_recursor :
    (name -> environment -> declaration option) -> methods -> nat ->
    environment -> context -> expr -> expr option result

  val core_reduce_projection_with :
    (name -> environment -> declaration option) -> methods -> (context ->
    expr -> expr result) -> environment -> context -> name -> nat -> expr ->
    expr option result

  val core_reduce_projection :
    (name -> environment -> declaration option) -> methods -> environment ->
    context -> name -> nat -> expr -> expr option result

  val core_reduce_quotient :
    (name -> environment -> declaration option) -> methods -> environment ->
    context -> expr -> expr option result

  val infer_step :
    (name -> environment -> declaration option) -> methods -> nat ->
    environment -> name list -> bool -> context -> expr -> expr result

  val core_beta_collect : expr -> expr list -> expr list -> expr

  val core_beta : expr -> expr list -> expr

  val core_unfold :
    (name -> environment -> declaration option) -> environment -> name list
    -> expr -> expr option result

  val whnf_core_step :
    (name -> environment -> declaration option) -> methods -> nat ->
    environment -> name list -> bool -> context -> expr -> expr result

  val finish_whnf_unfold :
    (name -> environment -> declaration option) -> environment -> name list
    -> expr -> whnf_round result

  val whnf_round_step :
    (name -> environment -> declaration option) -> methods -> nat ->
    environment -> name list -> context -> expr -> whnf_round result

  val whnf_loop :
    (name -> environment -> declaration option) -> nat -> methods -> nat ->
    environment -> name list -> context -> expr -> expr result

  val eta_compare : methods -> context -> expr -> expr -> expr -> bool result

  val core_alpha : nat -> expr -> expr -> (bool, nat) prod

  val core_alpha_eq : expr -> expr -> bool

  val core_compare_args :
    methods -> context -> expr list -> expr list -> bool result

  val core_same_head : nat -> expr -> expr -> bool result

  val core_congruent_apps :
    methods -> nat -> context -> expr -> expr -> bool result

  val core_delta_info :
    (name -> environment -> declaration option) -> environment -> expr ->
    declaration option

  val core_delta_sides :
    (name -> environment -> declaration option) -> environment -> expr ->
    expr -> (bool, bool) prod

  val core_erasing_delta :
    (name -> environment -> declaration option) -> environment -> expr -> bool

  val core_delta_congruent :
    (name -> environment -> declaration option) -> methods -> nat ->
    environment -> context -> expr -> expr -> bool result

  val compare_heads : methods -> nat -> context -> expr -> expr -> bool result

  val core_compare_fields :
    methods -> context -> name -> expr -> nat -> expr list -> bool result

  val core_structure_eta :
    (name -> environment -> declaration option) -> methods -> environment ->
    context -> expr -> expr -> bool result

  val core_unit_like :
    (name -> environment -> declaration option) -> methods -> environment ->
    context -> expr -> expr -> bool result

  val core_try_string_expansion :
    methods -> context -> expr -> expr -> bool option result

  val core_compare_fallback :
    (name -> environment -> declaration option) -> methods -> nat ->
    environment -> context -> expr -> expr -> bool result

  val compare_after_whnf :
    (name -> environment -> declaration option) -> methods -> nat ->
    environment -> context -> expr -> expr -> bool result

  val core_quick :
    methods -> nat -> context -> expr -> expr -> bool option result

  val core_proof_irrel :
    methods -> nat -> context -> expr -> expr -> bool option result

  val core_offset :
    (name -> environment -> declaration option) -> methods -> environment ->
    context -> expr -> expr -> bool option result

  val core_try_unfold_proj_app :
    methods -> context -> expr -> expr option result

  val core_opposite_projection :
    (name -> environment -> declaration option) -> methods -> environment ->
    context -> expr -> expr -> (expr, expr) prod option result

  val core_lazy_delta :
    (name -> environment -> declaration option) -> nat -> methods -> nat ->
    environment -> name list -> context -> expr -> expr ->
    conversion_progress result

  val core_finish_conversion :
    (name -> environment -> declaration option) -> methods -> nat ->
    environment -> context -> expr -> expr -> bool result

  val core_true_shortcut :
    (name -> environment -> declaration option) -> methods -> environment ->
    context -> expr -> expr -> bool result

  val defeq_step :
    (name -> environment -> declaration option) -> methods -> nat ->
    environment -> name list -> context -> expr -> expr -> bool result

  val checker_mode :
    (name -> environment -> declaration option) -> reduction_mode -> nat ->
    environment -> name list -> methods
 end

type 'x compare0 =
| LT
| EQ
| GT

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> sumbool
 end

module OrderedTypeFacts :
 functor (O:OrderedType) ->
 sig
  module TO :
   sig
    type t = O.t
   end

  module IsTO :
   sig
   end

  module OrderTac :
   sig
   end

  val eq_dec : O.t -> O.t -> sumbool

  val lt_dec : O.t -> O.t -> sumbool

  val eqb : O.t -> O.t -> bool
 end

module KeyOrderedType :
 functor (O:OrderedType) ->
 sig
  module MO :
   sig
    module TO :
     sig
      type t = O.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : O.t -> O.t -> sumbool

    val lt_dec : O.t -> O.t -> sumbool

    val eqb : O.t -> O.t -> bool
   end
 end

module Raw :
 functor (X:OrderedType) ->
 sig
  module MX :
   sig
    module TO :
     sig
      type t = X.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : X.t -> X.t -> sumbool

    val lt_dec : X.t -> X.t -> sumbool

    val eqb : X.t -> X.t -> bool
   end

  module PX :
   sig
    module MO :
     sig
      module TO :
       sig
        type t = X.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : X.t -> X.t -> sumbool

      val lt_dec : X.t -> X.t -> sumbool

      val eqb : X.t -> X.t -> bool
     end
   end

  type key = X.t

  type 'elt t = (X.t, 'elt) prod list

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val elements : 'a1 t -> 'a1 t

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val option_cons :
    key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list

  val map2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

  val map2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t

  val fold_right_pair :
    ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3

  val map2_alt :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key, 'a3)
    prod list

  val at_least_one :
    'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option

  val at_least_one_then_f :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
    'a3 option
 end

module type Int =
 sig
  type t

  val i2z : t -> z

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> sumbool

  val ge_lt_dec : t -> t -> sumbool

  val eq_dec : t -> t -> sumbool
 end

module Z_as_Int :
 sig
  type t = z

  val _0 : z

  val _1 : z

  val _2 : z

  val _3 : z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val max : z -> z -> z

  val eqb : z -> z -> bool

  val ltb : z -> z -> bool

  val leb : z -> z -> bool

  val eq_dec : z -> z -> sumbool

  val gt_le_dec : z -> z -> sumbool

  val ge_lt_dec : z -> z -> sumbool

  val i2z : t -> z
 end

module Coq_Raw :
 functor (I:Int) ->
 functor (X:OrderedType) ->
 sig
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  val tree_rect :
    'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
    -> 'a1 tree -> 'a2

  val tree_rec :
    'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
    -> 'a1 tree -> 'a2

  val height : 'a1 tree -> I.t

  val cardinal : 'a1 tree -> nat

  val empty : 'a1 tree

  val is_empty : 'a1 tree -> bool

  val mem : X.t -> 'a1 tree -> bool

  val find : X.t -> 'a1 tree -> 'a1 option

  val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

  val remove_min :
    'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod

  val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

  val remove : X.t -> 'a1 tree -> 'a1 tree

  val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  val t_left : 'a1 triple -> 'a1 tree

  val t_opt : 'a1 triple -> 'a1 option

  val t_right : 'a1 triple -> 'a1 tree

  val split : X.t -> 'a1 tree -> 'a1 triple

  val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

  val elements_aux : (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list

  val elements : 'a1 tree -> (key, 'a1) prod list

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  val enumeration_rect :
    'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
    enumeration -> 'a2

  val enumeration_rec :
    'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
    enumeration -> 'a2

  val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

  val equal_more :
    ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
    enumeration -> bool

  val equal_cont :
    ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
    enumeration -> bool

  val equal_end : 'a1 enumeration -> bool

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

  val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

  val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

  val map2_opt :
    (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
    ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
    tree

  module Proofs :
   sig
    module MX :
     sig
      module TO :
       sig
        type t = X.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : X.t -> X.t -> sumbool

      val lt_dec : X.t -> X.t -> sumbool

      val eqb : X.t -> X.t -> bool
     end

    module PX :
     sig
      module MO :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> sumbool

        val lt_dec : X.t -> X.t -> sumbool

        val eqb : X.t -> X.t -> bool
       end
     end

    module L :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> sumbool

        val lt_dec : X.t -> X.t -> sumbool

        val eqb : X.t -> X.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> sumbool

          val lt_dec : X.t -> X.t -> sumbool

          val eqb : X.t -> X.t -> bool
         end
       end

      type key = X.t

      type 'elt t = (X.t, 'elt) prod list

      val empty : 'a1 t

      val is_empty : 'a1 t -> bool

      val mem : key -> 'a1 t -> bool

      val find : key -> 'a1 t -> 'a1 option

      val add : key -> 'a1 -> 'a1 t -> 'a1 t

      val remove : key -> 'a1 t -> 'a1 t

      val elements : 'a1 t -> 'a1 t

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

      val option_cons :
        key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list

      val map2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

      val map2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

      val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t

      val fold_right_pair :
        ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3

      val map2_alt :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
        'a3) prod list

      val at_least_one :
        'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option

      val at_least_one_then_f :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option
        -> 'a3 option
     end

    val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    val flatten_e : 'a1 enumeration -> (key, 'a1) prod list
   end
 end

module IntMake :
 functor (I:Int) ->
 functor (X:OrderedType) ->
 sig
  module E :
   sig
    type t = X.t

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> sumbool
   end

  module Raw :
   sig
    type key = X.t

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * I.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2

    val height : 'a1 tree -> I.t

    val cardinal : 'a1 tree -> nat

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : X.t -> 'a1 tree -> bool

    val find : X.t -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : X.t -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : X.t -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux :
      (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list

    val elements : 'a1 tree -> (key, 'a1) prod list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> sumbool

        val lt_dec : X.t -> X.t -> sumbool

        val eqb : X.t -> X.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> sumbool

          val lt_dec : X.t -> X.t -> sumbool

          val eqb : X.t -> X.t -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> sumbool

          val lt_dec : X.t -> X.t -> sumbool

          val eqb : X.t -> X.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = X.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : X.t -> X.t -> sumbool

            val lt_dec : X.t -> X.t -> sumbool

            val eqb : X.t -> X.t -> bool
           end
         end

        type key = X.t

        type 'elt t = (X.t, 'elt) prod list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        val find : key -> 'a1 t -> 'a1 option

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        val remove : key -> 'a1 t -> 'a1 t

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
          'a3) prod list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key, 'a1) prod list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = E.t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key, 'a1) prod list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module Make :
 functor (X:OrderedType) ->
 sig
  module E :
   sig
    type t = X.t

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> sumbool
   end

  module Raw :
   sig
    type key = X.t

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val height : 'a1 tree -> Z_as_Int.t

    val cardinal : 'a1 tree -> nat

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : X.t -> 'a1 tree -> bool

    val find : X.t -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : X.t -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : X.t -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux :
      (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list

    val elements : 'a1 tree -> (key, 'a1) prod list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> sumbool

        val lt_dec : X.t -> X.t -> sumbool

        val eqb : X.t -> X.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> sumbool

          val lt_dec : X.t -> X.t -> sumbool

          val eqb : X.t -> X.t -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> sumbool

          val lt_dec : X.t -> X.t -> sumbool

          val eqb : X.t -> X.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = X.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : X.t -> X.t -> sumbool

            val lt_dec : X.t -> X.t -> sumbool

            val eqb : X.t -> X.t -> bool
           end
         end

        type key = X.t

        type 'elt t = (X.t, 'elt) prod list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        val find : key -> 'a1 t -> 'a1 option

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        val remove : key -> 'a1 t -> 'a1 t

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
          'a3) prod list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key, 'a1) prod list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = E.t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key, 'a1) prod list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module N_as_OT :
 sig
  type t = n

  val compare : n -> n -> n compare0

  val eq_dec : n -> n -> sumbool
 end

module DeclarationBuckets :
 sig
  module E :
   sig
    type t = n

    val compare : n -> n -> n compare0

    val eq_dec : n -> n -> sumbool
   end

  module Raw :
   sig
    type key = n

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val height : 'a1 tree -> Z_as_Int.t

    val cardinal : 'a1 tree -> nat

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : n -> 'a1 tree -> bool

    val find : n -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : n -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : n -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux :
      (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list

    val elements : 'a1 tree -> (key, 'a1) prod list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> n -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = n
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : n -> n -> sumbool

        val lt_dec : n -> n -> sumbool

        val eqb : n -> n -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = n
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : n -> n -> sumbool

          val lt_dec : n -> n -> sumbool

          val eqb : n -> n -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = n
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : n -> n -> sumbool

          val lt_dec : n -> n -> sumbool

          val eqb : n -> n -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = n
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : n -> n -> sumbool

            val lt_dec : n -> n -> sumbool

            val eqb : n -> n -> bool
           end
         end

        type key = n

        type 'elt t = (n, 'elt) prod list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        val find : key -> 'a1 t -> 'a1 option

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        val remove : key -> 'a1 t -> 'a1 t

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
          'a3) prod list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key, 'a1) prod list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = n

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key, 'a1) prod list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

type declaration_index = declaration list DeclarationBuckets.t

val declaration_bucket : n -> declaration_index -> environment

val empty_declaration_index : declaration_index

val index_declaration :
  (name -> n) -> declaration -> declaration_index -> declaration_index

val index_environment : (name -> n) -> environment -> declaration_index

val indexed_find_decl :
  (name -> n) -> name -> declaration_index -> declaration option

type declaration_lookup = name -> declaration option

val prepare_lookup : (name -> n) -> environment -> declaration_lookup

val checker_with_lookup_mode :
  reduction_mode -> nat -> environment -> declaration_lookup -> name list ->
  methods

module PositiveMap :
 sig
  type key = positive

  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  type 'a t = 'a tree

  val empty : 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val add : key -> 'a1 -> 'a1 t -> 'a1 t
 end

type dag_node =
| DBVar of nat
| DFVar of name
| DMVar of name
| DSort of level
| DConst of name * level list
| DApp of positive * positive
| DLam of name * binder_info * positive * positive
| DPi of name * binder_info * positive * positive
| DLet of name * positive * positive * positive * bool
| DLit of literal
| DProj of name * nat * positive
| DMData of positive

type scope_entry = { scope_expr : expr; scope_need : n }

type scope_table = scope_entry PositiveMap.t

val scope_ref : scope_table -> positive -> scope_entry result

val scope_node : scope_table -> dag_node -> scope_entry result

type dag_arena = { arena_scope : scope_table;
                   arena_nodes : dag_node PositiveMap.t }

val empty_arena : dag_arena

val arena_add : dag_arena -> PositiveMap.key -> dag_node -> dag_arena result

val arena_build :
  dag_arena -> (PositiveMap.key, dag_node) prod list -> dag_arena result

type context_path = (positive, positive option) prod list

val value_key_eqb : positive option -> positive option -> bool

val path_eqb : context_path -> context_path -> bool

type input_query = (positive, context_path) prod

val path_bucket : context_path -> positive

type path_entries = (context_path, expr result) prod list

type path_index = path_entries PositiveMap.t

type query_cache = path_index PositiveMap.t

val find_path :
  context_path -> (context_path, expr result) prod list -> expr result option

val cache_find : input_query -> query_cache -> expr result option

val cache_add : input_query -> expr result -> query_cache -> query_cache

val path_from : context -> scope_table -> context_path -> context result

val step_eval :
  methods -> nat -> environment -> name list -> context -> dag_arena -> bool
  -> input_query -> expr result

type step_cache = { checked_cache : query_cache; unchecked_cache : query_cache }

val select_cache : bool -> step_cache -> query_cache

val update_cache : bool -> query_cache -> step_cache -> step_cache

val empty_step_cache : step_cache

type 'a action = step_cache -> ('a result, step_cache) prod

val pure : 'a1 result -> 'a1 action

val then_do : 'a1 action -> ('a1 -> 'a2 action) -> 'a2 action

val memo_action : bool -> input_query -> expr action -> expr action

val node_action :
  methods -> nat -> environment -> name list -> dag_arena -> (bool ->
  input_query -> expr action) -> bool -> context_path -> context -> dag_node
  -> expr action

val uncached_action :
  methods -> nat -> environment -> name list -> context -> dag_arena -> (bool
  -> input_query -> expr action) -> bool -> input_query -> expr action

val memo_infer :
  methods -> nat -> environment -> name list -> context -> dag_arena -> nat
  -> bool -> input_query -> expr action

val run_memo_infer :
  methods -> nat -> environment -> name list -> context -> dag_arena -> nat
  -> bool -> input_query -> expr result

type context_path0 = (positive, positive option) prod list

val value_key_eqb0 : positive option -> positive option -> bool

val path_eqb0 : context_path0 -> context_path0 -> bool

type input_query0 = (positive, context_path0) prod

type query_cache0 = (context_path0, expr result) prod list PositiveMap.t

val find_path0 :
  context_path0 -> (context_path0, expr result) prod list -> expr result
  option

val cache_find0 : input_query0 -> query_cache0 -> expr result option

val cache_add0 : input_query0 -> expr result -> query_cache0 -> query_cache0

val path_from0 : context -> scope_table -> context_path0 -> context result

val step_eval0 :
  methods -> nat -> environment -> name list -> context -> dag_arena -> bool
  -> input_query0 -> expr result

type step_cache0 = { checked_cache0 : query_cache0;
                     unchecked_cache0 : query_cache0 }

val select_cache0 : bool -> step_cache0 -> query_cache0

val update_cache0 : bool -> query_cache0 -> step_cache0 -> step_cache0

val empty_step_cache0 : step_cache0

type 'a action0 = step_cache0 -> ('a result, step_cache0) prod

val pure0 : 'a1 result -> 'a1 action0

val then_do0 : 'a1 action0 -> ('a1 -> 'a2 action0) -> 'a2 action0

val memo_action0 : bool -> input_query0 -> expr action0 -> expr action0

val node_action0 :
  methods -> nat -> environment -> name list -> dag_arena -> (bool ->
  input_query0 -> expr action0) -> bool -> context_path0 -> context ->
  dag_node -> expr action0

val uncached_action0 :
  methods -> nat -> environment -> name list -> context -> dag_arena -> (bool
  -> input_query0 -> expr action0) -> bool -> input_query0 -> expr action0

val memo_infer0 :
  methods -> nat -> environment -> name list -> context -> dag_arena -> nat
  -> bool -> input_query0 -> expr action0

val run_memo_infer0 :
  methods -> nat -> environment -> name list -> context -> dag_arena -> nat
  -> bool -> input_query0 -> expr result

val lookup_step :
  declaration_lookup -> methods -> nat -> environment -> name list -> bool ->
  context -> expr -> expr result

val lookup_eval :
  declaration_lookup -> methods -> nat -> environment -> name list -> context
  -> dag_arena -> bool -> input_query -> expr result

val node_action1 :
  declaration_lookup -> methods -> nat -> environment -> name list ->
  dag_arena -> (bool -> input_query -> expr action) -> bool -> context_path
  -> context -> dag_node -> expr action

val uncached_action1 :
  declaration_lookup -> methods -> nat -> environment -> name list -> context
  -> dag_arena -> (bool -> input_query -> expr action) -> bool -> input_query
  -> expr action

val memo_infer1 :
  declaration_lookup -> methods -> nat -> environment -> name list -> context
  -> dag_arena -> nat -> bool -> input_query -> expr action

val run_memo_infer1 :
  declaration_lookup -> methods -> nat -> environment -> name list -> context
  -> dag_arena -> nat -> bool -> input_query -> expr result
