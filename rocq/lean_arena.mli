
type unit0 =
| Tt

type bool =
| True
| False

val xorb : bool -> bool -> bool

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

val eqb : nat -> nat -> bool

val tail_add : nat -> nat -> nat

val tail_addmul : nat -> nat -> nat -> nat

val tail_mul : nat -> nat -> nat

val of_uint_acc : uint -> nat -> nat

val of_uint : uint -> nat

val of_hex_uint_acc : uint0 -> nat -> nat

val of_hex_uint : uint0 -> nat

val of_num_uint : uint1 -> nat

val eqb0 : bool -> bool -> bool

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
  val pred : nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val max : nat -> nat -> nat

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

  val leb : positive -> positive -> bool

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

val eqb1 : ascii -> ascii -> bool

val n_of_digits : bool list -> n

val n_of_ascii : ascii -> n

val nat_of_ascii : ascii -> nat

type string =
| EmptyString
| String of ascii * string

val eqb2 : string -> string -> bool

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

type reduction_mode =
| NormalReduction
| EagerReduction

val has_external_local_at : nat -> expr -> bool

val has_external_local : expr -> bool

val nat_probe_allowed : reduction_mode -> expr -> expr -> bool

val true_probe_allowed : reduction_mode -> expr -> bool

val eager_reduce_name : name

val is_eager_reduce_argument : expr -> bool

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

val core_pow_max_exp : n

val core_shiftr : n -> n -> n option

val core_reduce_bool_name : name

val core_reduce_nat_name : name

val core_reduce_native : expr -> expr option result

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

val core_eta_expand_pis :
  nat -> methods -> context -> expr -> expr -> expr list -> expr result

val core_eta_expand : nat -> methods -> context -> expr -> expr result

val core_alpha : nat -> expr -> expr -> (bool, nat) prod

val core_alpha_eq : expr -> expr -> bool

val core_compare_args :
  methods -> context -> expr list -> expr list -> bool result

val core_same_head : nat -> expr -> expr -> bool result

val core_congruent_apps :
  methods -> nat -> context -> expr -> expr -> bool result

val core_delta_info : environment -> expr -> declaration option

val core_delta_head : environment -> expr -> bool

val core_delta_sides : environment -> expr -> expr -> (bool, bool) prod

val core_erasing_delta : environment -> expr -> bool

val core_delta_congruent :
  methods -> nat -> environment -> context -> expr -> expr -> bool result

val core_is_cheap_arg : environment -> expr -> bool

val core_compare_args_filtered :
  bool -> methods -> environment -> context -> expr list -> expr list -> bool
  result

val core_compare_args_cheap_first :
  methods -> environment -> context -> expr list -> expr list -> bool result

val compare_heads :
  methods -> nat -> environment -> context -> expr -> expr -> bool result

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

val core_reduce_proj_core : environment -> nat -> expr -> expr option

val core_lazy_delta_proj :
  nat -> methods -> nat -> environment -> name list -> context -> nat -> expr
  -> expr -> bool result

val core_finish_conversion :
  methods -> nat -> environment -> name list -> context -> expr -> expr ->
  bool result

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

val primitive_consume_mdata : nat -> expr -> expr result

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

val primitive_has_decidable_intro : environment -> bool

val primitive_has_bool_dec_eq : environment -> bool

val primitive_reflection_make_v436 : bool -> primitive_reflection

val primitive_reflection_for : environment -> bool -> primitive_reflection

val primitive_bool_dec_v436 : expr

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

val primitive_has_decidable_decide : environment -> bool

val primitive_condition_dec_in : environment -> primitive_condition -> expr

val primitive_condition_ite :
  primitive_condition -> PQ.term -> PQ.term list -> PQ.term -> PQ.term ->
  PQ.term

val primitive_condition_ite_in :
  environment -> primitive_condition -> PQ.term -> PQ.term list -> PQ.term ->
  PQ.term -> PQ.term

val primitive_condition_dite :
  primitive_condition -> PQ.term list -> (PQ.term -> PQ.term) -> (PQ.term ->
  PQ.term) -> PQ.term

val primitive_condition_decide_in :
  environment -> primitive_condition -> PQ.term list -> PQ.term

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

module NilEmpty :
 sig
  val string_of_uint : uint -> string
 end

module NilZero :
 sig
  val string_of_uint : uint -> string
 end

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

val q_name : name

val q_mk_name : name

val q_lift_name : name

val q_ind_name : name

val q_eq_name : name

val q_arrow : expr -> expr -> expr

val q_local :
  ind_state -> string -> binder_info -> expr -> (ind_local, ind_state) prod

val quotient_eq_type : level -> expr

val quotient_eq_refl_type : level -> expr

val quotient_check_eq : environment -> unit0 result

val canonical_quotient : quotient_kind -> declaration

val quotient_header_matches : quotient_kind -> declaration -> bool

val quotient_dependency : environment -> quotient_kind -> bool

val quotient_dependencies : environment -> quotient_kind -> bool

val admit_quotient :
  nat -> environment -> name -> name list -> expr -> quotient_kind ->
  environment result

val safety_eqb : input_safety -> input_safety -> bool

val checking_view : input_safety -> declaration -> declaration

val safety_environment : input_safety -> declaration list -> declaration list

val safety_kind : input_safety -> decl_kind

val safe_name : name -> unit0 result

val check_value :
  nat -> environment -> name list -> expr -> expr -> unit0 result

val restricted_constant :
  name -> name list -> expr -> expr option -> decl_kind -> declaration

val restricted_definition :
  reducibility_hints -> name -> name list -> expr -> expr -> decl_kind ->
  declaration

val admit_extended : nat -> environment -> input_decl -> environment result

val mutual_name : input_decl -> name

val check_mutual_headers :
  nat -> environment -> name list -> input_safety -> input_decl list ->
  declaration list result

val check_mutual_values :
  nat -> environment -> input_decl list -> declaration list result

val admit_mutual : nat -> environment -> input_decl list -> environment result

val mark_unsafe_inductive : declaration -> declaration

val inductive_input_unsafe : declaration list -> bool

val admit_inductive_extended :
  nat -> environment -> declaration list -> declaration list -> declaration
  list -> environment result

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

module N_as_OT :
 sig
  type t = n

  val compare : n -> n -> n compare0

  val eq_dec : n -> n -> sumbool
 end

module PositiveOrderedTypeBits :
 sig
  type t = positive

  val compare : t -> t -> positive compare0

  val eq_dec : positive -> positive -> sumbool
 end

val append0 : positive -> positive -> positive

module PositiveMap :
 sig
  module E :
   sig
    type t = positive

    val compare : t -> t -> positive compare0

    val eq_dec : positive -> positive -> sumbool
   end

  module ME :
   sig
    module MO :
     sig
      module TO :
       sig
        type t = positive
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : positive -> positive -> sumbool

      val lt_dec : positive -> positive -> sumbool

      val eqb : positive -> positive -> bool
     end
   end

  type key = positive

  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  type 'a t = 'a tree

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val mem : key -> 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val xelements : 'a1 t -> key -> (key, 'a1) prod list

  val elements : 'a1 t -> (key, 'a1) prod list

  val cardinal : 'a1 t -> nat

  val xfind : key -> key -> 'a1 t -> 'a1 option

  val xmapi : (key -> 'a1 -> 'a2) -> 'a1 t -> key -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val xmap2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

  val xmap2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

  val _map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val xfoldi : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> key -> 'a2

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
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

val entry_scoped : nat -> scope_entry -> bool

val input_infer :
  nat -> nat -> environment -> name list -> dag_arena -> positive -> expr
  result

val input_header :
  nat -> nat -> environment -> name -> name list -> dag_arena -> positive ->
  scope_entry -> unit0 result

val input_check :
  nat -> nat -> environment -> name list -> dag_arena -> positive -> positive
  -> expr -> unit0 result

val safe_definition_in_arena :
  reducibility_hints -> nat -> nat -> environment -> name -> name list ->
  dag_arena -> positive -> positive -> scope_entry -> scope_entry ->
  environment result

val admit_dag_definition :
  reducibility_hints -> nat -> nat -> environment -> name -> name list ->
  (PositiveMap.key, dag_node) prod list -> positive -> positive ->
  environment result

val decode_then_admit_definition :
  reducibility_hints -> nat -> environment -> name -> name list ->
  (PositiveMap.key, dag_node) prod list -> positive -> positive ->
  environment result

val input_proposition :
  nat -> nat -> environment -> name list -> dag_arena -> positive -> unit0
  result

val input_checked_constant :
  nat -> nat -> environment -> name -> name list -> dag_arena -> positive ->
  positive -> scope_entry -> scope_entry -> decl_kind -> environment result

val theorem_in_arena :
  nat -> nat -> environment -> name -> name list -> dag_arena -> positive ->
  positive -> scope_entry -> scope_entry -> environment result

val safe_opaque_in_arena :
  nat -> nat -> environment -> name -> name list -> dag_arena -> positive ->
  positive -> scope_entry -> scope_entry -> environment result

val admit_dag_theorem :
  nat -> nat -> environment -> name -> name list -> (PositiveMap.key,
  dag_node) prod list -> positive -> positive -> environment result

val decode_then_admit_theorem :
  nat -> environment -> name -> name list -> (PositiveMap.key, dag_node) prod
  list -> positive -> positive -> environment result

val admit_dag_opaque :
  nat -> nat -> environment -> name -> name list -> (PositiveMap.key,
  dag_node) prod list -> positive -> positive -> environment result

val decode_then_admit_opaque :
  nat -> environment -> name -> name list -> (PositiveMap.key, dag_node) prod
  list -> positive -> positive -> environment result

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

  val core_supported :
    (name -> environment -> declaration option) -> environment -> expr -> bool

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

  val core_pow_max_exp : n

  val core_shiftr : n -> n -> n option

  val core_reduce_bool_name : name

  val core_reduce_nat_name : name

  val core_reduce_native : expr -> expr option result

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

  val core_delta_head :
    (name -> environment -> declaration option) -> environment -> expr -> bool

  val core_delta_sides :
    (name -> environment -> declaration option) -> environment -> expr ->
    expr -> (bool, bool) prod

  val core_erasing_delta :
    (name -> environment -> declaration option) -> environment -> expr -> bool

  val core_delta_congruent :
    (name -> environment -> declaration option) -> methods -> nat ->
    environment -> context -> expr -> expr -> bool result

  val core_is_cheap_arg :
    (name -> environment -> declaration option) -> environment -> expr -> bool

  val core_compare_args_filtered :
    (name -> environment -> declaration option) -> bool -> methods ->
    environment -> context -> expr list -> expr list -> bool result

  val core_compare_args_cheap_first :
    (name -> environment -> declaration option) -> methods -> environment ->
    context -> expr list -> expr list -> bool result

  val compare_heads :
    (name -> environment -> declaration option) -> methods -> nat ->
    environment -> context -> expr -> expr -> bool result

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

  val core_reduce_proj_core :
    (name -> environment -> declaration option) -> environment -> nat -> expr
    -> expr option

  val core_lazy_delta_proj :
    (name -> environment -> declaration option) -> nat -> methods -> nat ->
    environment -> name list -> context -> nat -> expr -> expr -> bool result

  val core_finish_conversion :
    (name -> environment -> declaration option) -> methods -> nat ->
    environment -> name list -> context -> expr -> expr -> bool result

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

val checker_with_lookup_mode :
  reduction_mode -> nat -> environment -> declaration_lookup -> name list ->
  methods

val checker_with_lookup :
  nat -> environment -> declaration_lookup -> name list -> methods

val supported_with_lookup : declaration_lookup -> environment -> expr -> bool

val defeq_with_methods :
  declaration_lookup -> environment -> methods -> context -> expr -> expr ->
  bool result

val prepared_whnf :
  declaration_lookup -> nat -> environment -> name list -> context -> expr ->
  expr result

val prepared_defeq :
  declaration_lookup -> nat -> environment -> name list -> context -> expr ->
  expr -> bool result

val lookup_step :
  declaration_lookup -> methods -> nat -> environment -> name list -> bool ->
  context -> expr -> expr result

val lookup_eval :
  declaration_lookup -> methods -> nat -> environment -> name list -> context
  -> dag_arena -> bool -> input_query -> expr result

val node_action0 :
  declaration_lookup -> methods -> nat -> environment -> name list ->
  dag_arena -> (bool -> input_query -> expr action) -> bool -> context_path
  -> context -> dag_node -> expr action

val uncached_action0 :
  declaration_lookup -> methods -> nat -> environment -> name list -> context
  -> dag_arena -> (bool -> input_query -> expr action) -> bool -> input_query
  -> expr action

val memo_infer0 :
  declaration_lookup -> methods -> nat -> environment -> name list -> context
  -> dag_arena -> nat -> bool -> input_query -> expr action

val run_memo_infer0 :
  declaration_lookup -> methods -> nat -> environment -> name list -> context
  -> dag_arena -> nat -> bool -> input_query -> expr result

val suffix_zero : ascii

val suffix_bit : bool -> positive -> positive

val suffix_byte : ascii -> positive -> positive

val suffix_xor_rotate : ascii -> ascii -> ascii

val suffix_fold8 : ascii -> string -> positive

val suffix_lift : (string -> positive) -> name -> n

val suffix_bitfold8 : name -> n

val at_least : nat -> environment -> bool

val use_index : nat -> environment -> bool

type dag_admission_kind =
| DagDefinition of reducibility_hints
| DagTheorem
| DagOpaque

val linear_env_admit :
  dag_admission_kind -> nat -> nat -> environment -> name -> name list ->
  (PositiveMap.key, dag_node) prod list -> positive -> positive ->
  environment result

module PreparedDag :
 sig
  val input_infer :
    declaration_lookup -> environment -> nat -> nat -> name list -> dag_arena
    -> positive -> expr result

  val input_header :
    declaration_lookup -> environment -> nat -> nat -> name -> name list ->
    dag_arena -> positive -> scope_entry -> unit0 result

  val input_check :
    declaration_lookup -> environment -> nat -> nat -> name list -> dag_arena
    -> positive -> positive -> expr -> unit0 result

  val input_proposition :
    declaration_lookup -> environment -> nat -> nat -> name list -> dag_arena
    -> positive -> unit0 result

  val checked_constant :
    declaration_lookup -> environment -> nat -> nat -> name -> name list ->
    dag_arena -> positive -> positive -> scope_entry -> scope_entry ->
    decl_kind -> declaration list result

  val in_arena :
    declaration_lookup -> environment -> dag_admission_kind -> nat -> nat ->
    name -> name list -> dag_arena -> positive -> positive -> scope_entry ->
    scope_entry -> declaration list result
 end

val cheap_header_error :
  environment -> name -> name list -> scope_entry -> reject_reason option

val early_header_error :
  dag_admission_kind -> environment -> name -> name list -> scope_entry ->
  reject_reason option

val admit_with_preparation :
  (unit0 -> declaration_lookup) -> dag_admission_kind -> nat -> nat ->
  environment -> name -> name list -> (PositiveMap.key, dag_node) prod list
  -> positive -> positive -> environment result

val indexed_admit :
  (name -> n) -> dag_admission_kind -> nat -> nat -> environment -> name ->
  name list -> (PositiveMap.key, dag_node) prod list -> positive -> positive
  -> environment result

val indexed_dag_admit :
  dag_admission_kind -> nat -> nat -> environment -> name -> name list ->
  (PositiveMap.key, dag_node) prod list -> positive -> positive ->
  environment result

val indexed_admit_dag_definition :
  reducibility_hints -> nat -> nat -> environment -> name -> name list ->
  (PositiveMap.key, dag_node) prod list -> positive -> positive ->
  environment result

val indexed_admit_dag_theorem :
  nat -> nat -> environment -> name -> name list -> (PositiveMap.key,
  dag_node) prod list -> positive -> positive -> environment result

val indexed_admit_dag_opaque :
  nat -> nat -> environment -> name -> name list -> (PositiveMap.key,
  dag_node) prod list -> positive -> positive -> environment result

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

val node_action1 :
  methods -> nat -> environment -> name list -> dag_arena -> (bool ->
  input_query0 -> expr action0) -> bool -> context_path0 -> context ->
  dag_node -> expr action0

val uncached_action1 :
  methods -> nat -> environment -> name list -> context -> dag_arena -> (bool
  -> input_query0 -> expr action0) -> bool -> input_query0 -> expr action0

val memo_infer1 :
  methods -> nat -> environment -> name list -> context -> dag_arena -> nat
  -> bool -> input_query0 -> expr action0

val run_memo_infer1 :
  methods -> nat -> environment -> name list -> context -> dag_arena -> nat
  -> bool -> input_query0 -> expr result

val entry_scoped0 : nat -> scope_entry -> bool

val input_infer0 :
  nat -> nat -> environment -> name list -> dag_arena -> positive -> expr
  result

val input_header0 :
  nat -> nat -> environment -> name -> name list -> dag_arena -> positive ->
  scope_entry -> unit0 result

val input_check0 :
  nat -> nat -> environment -> name list -> dag_arena -> positive -> positive
  -> expr -> unit0 result

val safe_definition_in_arena0 :
  reducibility_hints -> nat -> nat -> environment -> name -> name list ->
  dag_arena -> positive -> positive -> scope_entry -> scope_entry ->
  environment result

val admit_dag_definition0 :
  reducibility_hints -> nat -> nat -> environment -> name -> name list ->
  (PositiveMap.key, dag_node) prod list -> positive -> positive ->
  environment result

val input_proposition0 :
  nat -> nat -> environment -> name list -> dag_arena -> positive -> unit0
  result

val input_checked_constant0 :
  nat -> nat -> environment -> name -> name list -> dag_arena -> positive ->
  positive -> scope_entry -> scope_entry -> decl_kind -> environment result

val theorem_in_arena0 :
  nat -> nat -> environment -> name -> name list -> dag_arena -> positive ->
  positive -> scope_entry -> scope_entry -> environment result

val safe_opaque_in_arena0 :
  nat -> nat -> environment -> name -> name list -> dag_arena -> positive ->
  positive -> scope_entry -> scope_entry -> environment result

val admit_dag_theorem0 :
  nat -> nat -> environment -> name -> name list -> (PositiveMap.key,
  dag_node) prod list -> positive -> positive -> environment result

val admit_dag_opaque0 :
  nat -> nat -> environment -> name -> name list -> (PositiveMap.key,
  dag_node) prod list -> positive -> positive -> environment result

val linear_cache_new_admit :
  dag_admission_kind -> nat -> nat -> environment -> name -> name list ->
  (PositiveMap.key, dag_node) prod list -> positive -> positive ->
  environment result

val new_ordinary_decode_admit :
  dag_admission_kind -> nat -> environment -> name -> name list ->
  (PositiveMap.key, dag_node) prod list -> positive -> positive ->
  environment result

type indexed_state = { state_environment : environment;
                       state_index : declaration_index }

val state_environment : (name -> n) -> indexed_state -> environment

val seed_state : (name -> n) -> environment -> indexed_state

val prepend_index :
  (name -> n) -> declaration list -> declaration_index -> declaration_index

val extend_state :
  (name -> n) -> indexed_state -> declaration list -> indexed_state

val state_lookup : (name -> n) -> indexed_state -> name -> declaration option

val result_map : ('a1 -> 'a2) -> 'a1 result -> 'a2 result

val single_delta : environment result -> declaration list result

val mutual_delta :
  nat -> declaration list -> input_decl list -> environment result

val nested_delta :
  nat -> environment -> declaration list -> declaration list -> declaration
  list -> environment result

val inductive_delta :
  nat -> declaration list -> declaration list -> declaration list ->
  declaration list -> environment result

val cached_dag_admit :
  (name -> n) -> indexed_state -> dag_admission_kind -> nat -> nat -> name ->
  name list -> (PositiveMap.key, dag_node) prod list -> positive -> positive
  -> environment result

type admission_batch =
| BatchDag of dag_admission_kind * nat * name * name list
   * (positive, dag_node) prod list * positive * positive
| BatchOrdinary of input_decl
| BatchQuotient of name * name list * expr * quotient_kind
| BatchInductive of declaration list * declaration list * declaration list
| BatchMutual of input_decl list

val batch_delta :
  (name -> n) -> nat -> indexed_state -> admission_batch -> environment result

val state_step :
  (name -> n) -> nat -> indexed_state -> admission_batch -> indexed_state
  result

type runtime_state = indexed_state

val initial_state : runtime_state

val admit_batch :
  nat -> runtime_state -> admission_batch -> indexed_state result

type quotient_transaction_state = (environment, bool) prod

val quotient_transaction_names : name list

val quotient_names_fresh : environment -> name list -> bool

val canonical_quotient_block : environment

val initialize_quotient :
  quotient_transaction_state -> quotient_transaction_state result

val quotient_delta_prefix : quotient_transaction_state -> environment

type quotient_transaction_delta = (environment, bool) prod

val initialize_quotient_delta :
  quotient_transaction_state -> quotient_transaction_delta result

type quotient_indexed_state = { quotient_indexed_base : indexed_state;
                                quotient_indexed_initialized : bool }

val quotient_indexed_project :
  (name -> n) -> quotient_indexed_state -> quotient_transaction_state

val quotient_indexed_empty : (name -> n) -> quotient_indexed_state

val quotient_indexed_step :
  (name -> n) -> quotient_indexed_state -> quotient_indexed_state result

val quotient_indexed_transaction :
  (name -> n) -> quotient_indexed_state -> (quotient_indexed_state, unit0
  result) prod

type quotient_runtime_state = quotient_indexed_state

val quotient_runtime_initial : quotient_runtime_state

val quotient_runtime_initialize :
  quotient_runtime_state -> (quotient_indexed_state, unit0 result) prod

module CacheMap :
 sig
  module E :
   sig
    type t = positive

    val compare : t -> t -> positive compare0

    val eq_dec : positive -> positive -> sumbool
   end

  module ME :
   sig
    module MO :
     sig
      module TO :
       sig
        type t = positive
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : positive -> positive -> sumbool

      val lt_dec : positive -> positive -> sumbool

      val eqb : positive -> positive -> bool
     end
   end

  type key = positive

  type 'a tree = 'a PositiveMap.tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  type 'a t = 'a tree

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val mem : key -> 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val xelements : 'a1 t -> key -> (key, 'a1) prod list

  val elements : 'a1 t -> (key, 'a1) prod list

  val cardinal : 'a1 t -> nat

  val xfind : key -> key -> 'a1 t -> 'a1 option

  val xmapi : (key -> 'a1 -> 'a2) -> 'a1 t -> key -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val xmap2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

  val xmap2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

  val _map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val xfoldi : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> key -> 'a2

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

val option_expr_eqb : expr option -> expr option -> bool

val binding_eqb : binding -> binding -> bool

val free_entry_eqb : (name, binding) prod -> (name, binding) prod -> bool

val context_eqb : context -> context -> bool

val core_alpha_opt : nat -> expr option -> expr option -> (bool, nat) prod

val core_alpha_binding : nat -> binding -> binding -> (bool, nat) prod

val core_alpha_bindings :
  nat -> binding list -> binding list -> (bool, nat) prod

val core_alpha_free :
  nat -> (name, binding) prod list -> (name, binding) prod list -> (bool,
  nat) prod

val core_alpha_context : nat -> context -> context -> bool

val pos_trunc : nat -> positive -> positive

val pos_xor_trunc : nat -> positive -> positive -> positive

val hash_mix : positive -> positive -> positive

val hash_ascii : ascii -> positive

val hash_string_bounded : nat -> string -> positive -> positive

val hash_nat_small : nat -> positive

val hash_N_fast : n -> positive

val hash_name_bounded : nat -> name -> positive

val hash_level_bounded : nat -> level -> positive

val hash_levels_bounded : nat -> level list -> positive -> positive

val hash_expr_bounded : nat -> expr -> positive

val hash_expr : expr -> positive

val hash_binding : binding -> positive

val hash_bound_prefix : nat -> binding list -> positive -> positive

val hash_free_prefix :
  nat -> (name, binding) prod list -> positive -> positive

val hash_context : context -> positive

type defeq_cache_key = { dck_context : context; dck_lhs : expr; dck_rhs : expr }

val defeq_cache_key_eqb : defeq_cache_key -> defeq_cache_key -> bool

val defeq_cache_key_hash : defeq_cache_key -> positive

type defeq_cache_entry = { dce_key : defeq_cache_key; dce_verdict : bool }

type defeq_cache = defeq_cache_entry list CacheMap.t

val empty_defeq_cache : defeq_cache

val bucket_lookup : defeq_cache_key -> defeq_cache_entry list -> bool option

val cache_find1 : positive -> 'a1 CacheMap.t -> 'a1 option

val cache_lookup : defeq_cache_key -> defeq_cache -> bool option

val cache_insert : defeq_cache_key -> bool -> defeq_cache -> defeq_cache

val key_of_query : context -> expr -> expr -> defeq_cache_key

val cached_defeq :
  nat -> environment -> name list -> context -> defeq_cache -> expr -> expr
  -> (defeq_cache, bool result) prod

type equiv_manager = { em_parent : positive PositiveMap.t;
                       em_next : positive;
                       em_nodes : ((context, expr) prod, positive) prod list
                                  CacheMap.t }

val em_empty : equiv_manager

val em_find_aux :
  nat -> positive PositiveMap.t -> positive -> (positive, positive
  PositiveMap.t) prod

val em_find : equiv_manager -> positive -> (positive, equiv_manager) prod

val em_merge : equiv_manager -> positive -> positive -> equiv_manager

val em_bucket_find :
  context -> expr -> ((context, expr) prod, positive) prod list -> positive
  option

val em_to_node_hashed :
  equiv_manager -> positive -> context -> expr -> (positive, equiv_manager)
  prod

val em_add_equiv_hashed :
  equiv_manager -> positive -> positive -> context -> expr -> expr ->
  equiv_manager

val em_add_equiv : equiv_manager -> context -> expr -> expr -> equiv_manager

val em_root_aux : nat -> positive PositiveMap.t -> positive -> positive

val em_root : equiv_manager -> positive -> positive

val em_is_equiv_ro_hashed :
  equiv_manager -> positive -> positive -> context -> expr -> expr -> bool

val em_is_equiv_ro : equiv_manager -> context -> expr -> expr -> bool

type fuel_config = { fc_whnf : nat; fc_whnf_eager : nat; fc_lazy_delta : 
                     nat; fc_eta_expand : nat; fc_rec_depth : nat;
                     fc_inductive_fuel : nat }

val default_lazy_delta_rounds : nat

val default_eta_expand_rounds : nat

val default_rec_depth : nat

val default_inductive_fuel : nat

val default_fuel_config : fuel_config

val fuel_config_with_rec_depth : nat -> fuel_config

val uniform_fuel_config : nat -> fuel_config

val fuel_config_nonzero : fuel_config -> bool

val infer_with_config :
  fuel_config -> environment -> name list -> context -> expr -> expr result

val whnf_with_config :
  fuel_config -> environment -> name list -> context -> expr -> expr result

val defeq_with_config :
  fuel_config -> environment -> name list -> context -> expr -> expr -> bool
  result

val eta_expand_with_config :
  fuel_config -> environment -> name list -> context -> expr -> expr result

val check_with_config :
  fuel_config -> environment -> name list -> context -> expr -> expr -> unit0
  result

val admit_with_config :
  fuel_config -> environment -> input_decl -> environment result

val chash_mix : positive -> positive -> positive

val pos_of_nat_fast : nat -> positive

val pos_of_N_fast : n -> positive

val hash_name : name -> positive

val hash_level : level -> positive

val hash_levels : level list -> positive

val hash_string : string -> positive

type cmeta = { cm_lbr : nat; cm_hfv : bool; cm_supp : bool;
               cm_dag : positive option }

val cmeta_closed_supp : cmeta

val cmeta_closed_unsupp : cmeta

val cmeta_fvar : cmeta

type cexpr =
| CBVar of cmeta * nat
| CFVar of cmeta * name
| CMVar of cmeta * name
| CSort of cmeta * level
| CConst of cmeta * name * level list
| CApp of cmeta * cexpr * cexpr
| CLam of cmeta * name * binder_info * cexpr * cexpr
| CPi of cmeta * name * binder_info * cexpr * cexpr
| CLet of cmeta * name * cexpr * cexpr * cexpr * bool
| CProj of cmeta * name * nat * cexpr
| CMData of cmeta * cexpr
| CLit of cmeta * literal

val c_meta : cexpr -> cmeta

val ce_lbr : cexpr -> nat

val ce_hfv : cexpr -> bool

val ce_supp : cexpr -> bool

val ce_dag : cexpr -> positive option

val c_hash_expr_bounded : nat -> cexpr -> positive

val ce_hash : cexpr -> positive

val c_tag_dag : positive -> cexpr -> cexpr

val mk_cmeta : nat -> bool -> bool -> cmeta

val mk_cbvar : nat -> cexpr

val mk_cfvar : name -> cexpr

val mk_cmvar : name -> cexpr

val mk_csort : level -> cexpr

val mk_cconst : name -> level list -> cexpr

val mk_capp : cexpr -> cexpr -> cexpr

val mk_clam : name -> binder_info -> cexpr -> cexpr -> cexpr

val mk_cpi : name -> binder_info -> cexpr -> cexpr -> cexpr

val mk_clet : name -> cexpr -> cexpr -> cexpr -> bool -> cexpr

val mk_cproj : name -> nat -> cexpr -> cexpr

val mk_cmdata : cexpr -> cexpr

val mk_clit : bool -> bool -> literal -> cexpr

val mk_cnat : n -> cexpr

val c_of_expr : bool -> bool -> expr -> cexpr

val c_lift_go : nat -> nat -> cexpr -> cexpr

val c_lift : nat -> nat -> cexpr -> cexpr

val c_subst : nat -> cexpr -> cexpr -> cexpr

val c_instantiate : cexpr -> cexpr -> cexpr

val c_subst_many_go : nat -> nat -> cexpr list -> cexpr -> cexpr

val c_subst_many : nat -> cexpr list -> cexpr -> cexpr

val c_instantiate_many : cexpr -> cexpr list -> cexpr

val c_subst_levels_go : name list -> level list -> cexpr -> cexpr

val c_subst_levels : name list -> level list -> cexpr -> cexpr

val c_spine : cexpr -> cexpr list -> (cexpr, cexpr list) prod

val c_apps : cexpr -> cexpr list -> cexpr

val c_beta_collect : cexpr -> cexpr list -> cexpr list -> cexpr

val c_beta : cexpr -> cexpr list -> cexpr

val c_dag_same : cexpr -> cexpr -> bool

val c_alpha : nat -> cexpr -> cexpr -> (bool, nat) prod

val c_alpha_eq : cexpr -> cexpr -> bool

val c_expr_eqb : cexpr -> cexpr -> bool

val c_nat_value : cexpr -> n option

val c_nat_constructor : n -> cexpr

val c_is_true : cexpr -> bool

val c_is_eager_reduce_argument : cexpr -> bool

val c_same_head : nat -> cexpr -> cexpr -> bool result

val c_reduce_native : cexpr -> cexpr option result

val c_char_expr : n -> cexpr

val c_char_list : n list -> cexpr

val c_expand_string : string -> cexpr result

val c_core_nat : cexpr

val c_core_string : cexpr

type c_arena_table = cexpr PositiveMap.t

val c_arena_ref : c_arena_table -> positive -> cexpr result

val c_arena_compile_node :
  bool -> bool -> c_arena_table -> positive -> dag_node -> cexpr result

val c_arena_build :
  bool -> bool -> c_arena_table -> (positive, dag_node) prod list ->
  c_arena_table result

type c_binding = { cb_type : cexpr; cb_value : cexpr option }

type c_context = { cc_id : positive; cc_bound : c_binding list;
                   cc_free : (name, c_binding) prod list }

val empty_c_context : c_context

val c_find_free : name -> (name, c_binding) prod list -> c_binding option

val c_is_non_let_local : c_context -> cexpr -> bool

type c_equiv_manager = { cem_next : positive;
                         cem_nodes : ((positive, cexpr) prod, positive) prod
                                     list CacheMap.t;
                         cem_parent : positive PositiveMap.t }

val cem_empty : c_equiv_manager

val cem_find_root_fuel : nat -> positive PositiveMap.t -> positive -> positive

val cem_find_root : c_equiv_manager -> positive -> positive

val cem_bucket_lookup :
  positive -> cexpr -> ((positive, cexpr) prod, positive) prod list ->
  positive option

val cem_is_equiv_ro :
  c_equiv_manager -> positive -> positive -> positive -> cexpr -> cexpr ->
  bool

val cem_intern :
  c_equiv_manager -> positive -> positive -> cexpr -> (positive,
  c_equiv_manager) prod

val cem_add_equiv :
  c_equiv_manager -> positive -> positive -> positive -> cexpr -> cexpr ->
  c_equiv_manager

type compiled_decl = { cd_decl : declaration; cd_type : cexpr;
                       cd_value : cexpr option;
                       cd_rules : ((name, nat) prod, cexpr) prod list }

type checker_state = { cs_whnf_cache : ((positive, cexpr) prod, cexpr) prod
                                       list CacheMap.t;
                       cs_infer_cache : (((bool, positive) prod, cexpr) prod,
                                        cexpr) prod list CacheMap.t;
                       cs_defeq_cache : (((positive, cexpr) prod, cexpr)
                                        prod, bool) prod list CacheMap.t;
                       cs_fail_cache : ((positive, cexpr) prod, cexpr) prod
                                       list CacheMap.t;
                       cs_equiv : c_equiv_manager;
                       cs_decl_cache : (name, compiled_decl) prod list
                                       CacheMap.t;
                       cs_ctx_trie : ((cexpr, cexpr option) prod, positive)
                                     prod list PositiveMap.t;
                       cs_next_ctx : positive }

val empty_checker_state : checker_state

val cache_bucket_cap : nat

val c_push_capped : 'a1 -> 'a1 list -> 'a1 list

val c_should_cache_whnf : c_context -> cexpr -> bool

val c_should_cache_infer : cexpr -> bool

val c_is_trivial_defeq_expr : cexpr -> bool

val c_whnf_bucket_find :
  positive -> cexpr -> ((positive, cexpr) prod, cexpr) prod list -> cexpr
  option

val c_whnf_find_h :
  positive -> positive -> cexpr -> checker_state -> cexpr option

val c_whnf_put_h :
  positive -> positive -> cexpr -> cexpr -> checker_state -> checker_state

val c_infer_bucket_find :
  bool -> positive -> cexpr -> (((bool, positive) prod, cexpr) prod, cexpr)
  prod list -> cexpr option

val c_infer_find_h :
  positive -> bool -> positive -> cexpr -> checker_state -> cexpr option

val c_infer_put_h :
  positive -> bool -> positive -> cexpr -> cexpr -> checker_state ->
  checker_state

val c_defeq_bucket_find :
  positive -> cexpr -> cexpr -> (((positive, cexpr) prod, cexpr) prod, bool)
  prod list -> bool option

val c_fail_bucket_mem :
  positive -> cexpr -> cexpr -> ((positive, cexpr) prod, cexpr) prod list ->
  bool

val c_defeq_hashes :
  positive -> cexpr -> cexpr -> ((positive, positive) prod, positive) prod

val c_defeq_find_h :
  positive -> positive -> positive -> positive -> cexpr -> cexpr ->
  checker_state -> bool option

val c_defeq_put_h :
  positive -> positive -> positive -> positive -> cexpr -> cexpr -> bool ->
  checker_state -> checker_state

val c_fail_mem_h :
  positive -> positive -> cexpr -> cexpr -> checker_state -> bool

val c_fail_put_h :
  positive -> positive -> cexpr -> cexpr -> checker_state -> checker_state

val c_decl_bucket_find :
  name -> (name, compiled_decl) prod list -> compiled_decl option

val c_find_compiled_rule :
  name -> ((name, nat) prod, cexpr) prod list -> (nat, cexpr) prod option

type 'a c_act = checker_state -> ('a result, checker_state) prod

val c_ret : 'a1 -> 'a1 c_act

val c_pure : 'a1 result -> 'a1 c_act

val c_bind : 'a1 c_act -> ('a1 -> 'a2 c_act) -> 'a2 c_act

val c_opt_alpha : nat -> cexpr option -> cexpr option -> bool

val c_ctx_trie_find :
  cexpr -> cexpr option -> ((cexpr, cexpr option) prod, positive) prod list
  -> positive option

val c_push_binding : c_context -> cexpr -> cexpr option -> c_context c_act

type c_methods = { cm_infer : (c_context -> cexpr -> cexpr c_act);
                   cm_infer_type : (c_context -> cexpr -> cexpr c_act);
                   cm_whnf : (c_context -> cexpr -> cexpr c_act);
                   cm_whnf_core : (bool -> c_context -> cexpr -> cexpr c_act);
                   cm_defeq : (c_context -> cexpr -> cexpr -> bool c_act);
                   cm_mode : reduction_mode;
                   cm_eager_defeq : (c_context -> cexpr -> cexpr -> bool
                                    c_act) }

val cm_inference_only : c_methods -> c_methods

val cm_app_type_defeq :
  c_methods -> c_context -> cexpr -> cexpr -> cexpr -> bool c_act

val cm_sort_of : c_methods -> c_context -> cexpr -> level c_act

val c_compile_decl : bool -> bool -> declaration -> compiled_decl

val c_get_compiled :
  declaration_lookup -> bool -> bool -> name -> compiled_decl option c_act

val c_get_constant :
  declaration_lookup -> bool -> bool -> name list -> name -> level list ->
  compiled_decl c_act

val c_unfold :
  declaration_lookup -> bool -> bool -> name list -> cexpr -> cexpr option
  c_act

val c_delta_info : declaration_lookup -> cexpr -> declaration option

val c_delta_sides : declaration_lookup -> cexpr -> cexpr -> (bool, bool) prod

val c_erasing_delta : declaration_lookup -> cexpr -> bool

val c_is_cheap_arg : declaration_lookup -> cexpr -> bool

val c_nat_probe_head : declaration_lookup -> cexpr -> bool

val c_make_structure :
  declaration_lookup -> environment -> name -> level list -> cexpr list ->
  cexpr -> cexpr option

val c_reduce_proj_core :
  declaration_lookup -> environment -> nat -> cexpr -> cexpr option

val c_apply_type :
  c_methods -> c_context -> cexpr -> cexpr list -> cexpr c_act

val c_occurs : nat -> cexpr -> bool

val c_projection_field :
  c_methods -> nat -> c_context -> name -> cexpr -> bool -> nat -> nat ->
  cexpr -> cexpr c_act

val c_infer_projection :
  declaration_lookup -> environment -> bool -> bool -> c_methods -> nat ->
  c_context -> name -> nat -> cexpr -> cexpr c_act

val c_binary_nat :
  bool -> nat -> primitive_kind -> n -> n -> cexpr option result

val c_reduce_nat :
  declaration_lookup -> bool -> bool -> c_methods -> nat -> c_context ->
  cexpr -> cexpr option c_act

val c_to_constructor :
  declaration_lookup -> environment -> bool -> c_methods -> nat -> c_context
  -> name -> bool -> cexpr -> cexpr c_act

val c_reduce_recursor_compiled :
  declaration_lookup -> environment -> bool -> c_methods -> nat -> c_context
  -> compiled_decl -> level list -> cexpr list -> cexpr option c_act

val c_reduce_recursor :
  declaration_lookup -> environment -> bool -> bool -> c_methods -> nat ->
  c_context -> cexpr -> cexpr option c_act

val c_reduce_projection_with :
  declaration_lookup -> environment -> c_methods -> (c_context -> cexpr ->
  cexpr c_act) -> c_context -> name -> nat -> cexpr -> cexpr option c_act

val c_reduce_quotient_parts :
  declaration_lookup -> c_methods -> c_context -> quotient_kind -> cexpr list
  -> cexpr option c_act

val c_reduce_quotient :
  declaration_lookup -> c_methods -> c_context -> cexpr -> cexpr option c_act

val c_infer_step :
  declaration_lookup -> environment -> bool -> bool -> c_methods -> nat ->
  name list -> bool -> c_context -> cexpr -> cexpr c_act

val c_is_closed_no_fvar : cexpr -> bool

val c_nat_probe_allowed : reduction_mode -> cexpr -> cexpr -> bool

val c_true_probe_allowed : reduction_mode -> cexpr -> bool

val c_whnf_core_step :
  declaration_lookup -> environment -> bool -> bool -> c_methods -> nat ->
  name list -> bool -> c_context -> cexpr -> cexpr c_act

val c_nat_add_outer_limit : nat

val c_nat_add_inner_limit : nat

val c_is_nat_add : declaration_lookup -> cexpr -> (cexpr, cexpr) prod option

type c_add_step_res =
| CAddDone of n
| CAddFallback
| CAddNext of cexpr * n

val c_nat_add_one_step :
  declaration_lookup -> environment -> bool -> bool -> c_methods -> nat ->
  name list -> c_context -> cexpr -> n -> c_add_step_res c_act

val c_nat_add_inner :
  declaration_lookup -> environment -> bool -> bool -> nat -> c_methods ->
  nat -> name list -> c_context -> cexpr -> n -> c_add_step_res c_act

val c_nat_add_outer :
  declaration_lookup -> environment -> bool -> bool -> nat -> c_methods ->
  nat -> name list -> c_context -> cexpr -> n -> cexpr option c_act

type c_whnf_round =
| CWhnfDone of cexpr
| CWhnfContinue of cexpr

val c_whnf_round_step :
  declaration_lookup -> environment -> bool -> bool -> bool -> c_methods ->
  nat -> name list -> c_context -> cexpr -> c_whnf_round c_act

val c_whnf_loop_aux :
  declaration_lookup -> environment -> bool -> bool -> bool -> nat ->
  c_methods -> nat -> name list -> c_context -> cexpr -> cexpr c_act

val c_whnf_loop :
  declaration_lookup -> environment -> bool -> bool -> bool -> nat ->
  c_methods -> nat -> name list -> c_context -> cexpr -> cexpr c_act

val c_eta_compare :
  c_methods -> c_context -> cexpr -> cexpr -> cexpr -> bool c_act

val c_compare_args_filtered :
  declaration_lookup -> bool -> c_methods -> c_context -> cexpr list -> cexpr
  list -> bool c_act

val c_compare_args_cheap_first :
  declaration_lookup -> c_methods -> c_context -> cexpr list -> cexpr list ->
  bool c_act

val c_congruent_apps :
  declaration_lookup -> c_methods -> nat -> c_context -> cexpr -> cexpr ->
  bool c_act

val c_delta_congruent :
  declaration_lookup -> c_methods -> nat -> c_context -> cexpr -> cexpr ->
  bool c_act

val c_compare_heads :
  declaration_lookup -> c_methods -> nat -> c_context -> cexpr -> cexpr ->
  bool c_act

val c_compare_fields :
  c_methods -> c_context -> name -> cexpr -> nat -> cexpr list -> bool c_act

val c_structure_eta :
  declaration_lookup -> environment -> c_methods -> c_context -> cexpr ->
  cexpr -> bool c_act

val c_unit_like :
  declaration_lookup -> environment -> c_methods -> c_context -> cexpr ->
  cexpr -> bool c_act

val c_try_string_expansion :
  c_methods -> c_context -> cexpr -> cexpr -> bool option c_act

val c_compare_fallback :
  declaration_lookup -> environment -> c_methods -> nat -> c_context -> cexpr
  -> cexpr -> bool c_act

val c_compare_after_whnf :
  declaration_lookup -> environment -> c_methods -> nat -> c_context -> cexpr
  -> cexpr -> bool c_act

val c_quick :
  c_methods -> nat -> c_context -> cexpr -> cexpr -> bool option c_act

val c_proof_irrel :
  c_methods -> nat -> c_context -> cexpr -> cexpr -> bool option c_act

val c_offset :
  bool -> c_methods -> c_context -> cexpr -> cexpr -> bool option c_act

val c_try_unfold_proj_app :
  c_methods -> c_context -> cexpr -> cexpr option c_act

val c_opposite_projection :
  declaration_lookup -> c_methods -> c_context -> cexpr -> cexpr -> (cexpr,
  cexpr) prod option c_act

type c_conversion_progress =
| CConversionDone of bool
| CConversionStuck of cexpr * cexpr

val c_nat_congr_worth_trying : declaration_lookup -> cexpr -> cexpr -> bool

val c_lazy_delta :
  declaration_lookup -> bool -> bool -> bool -> nat -> c_methods -> nat ->
  name list -> c_context -> cexpr -> cexpr -> c_conversion_progress c_act

val c_lazy_delta_proj :
  declaration_lookup -> environment -> bool -> bool -> nat -> c_methods ->
  nat -> name list -> c_context -> nat -> cexpr -> cexpr -> bool c_act

val c_finish_conversion :
  declaration_lookup -> fuel_config -> environment -> bool -> bool ->
  c_methods -> nat -> name list -> c_context -> cexpr -> cexpr -> bool c_act

val c_true_shortcut :
  bool -> c_methods -> c_context -> cexpr -> cexpr -> bool c_act

val c_defeq_step :
  declaration_lookup -> fuel_config -> environment -> bool -> bool -> bool ->
  c_methods -> nat -> name list -> c_context -> cexpr -> cexpr -> bool c_act

val c_checker_mode :
  declaration_lookup -> fuel_config -> environment -> bool -> bool -> bool ->
  reduction_mode -> nat -> name list -> c_methods

val c_checker :
  declaration_lookup -> fuel_config -> environment -> bool -> bool -> bool ->
  name list -> c_methods

type path_trie =
  ((positive, positive option) prod, c_context) prod list PositiveMap.t
  (* singleton inductive, whose constructor was Build_path_trie *)

val empty_path_trie : path_trie

val pt_find_edge :
  positive -> positive option -> ((positive, positive option) prod,
  c_context) prod list -> c_context option

type dag_infer_state = { dis_trie : path_trie;
                         dis_checked : cexpr PositiveMap.t PositiveMap.t;
                         dis_unchecked : cexpr PositiveMap.t PositiveMap.t;
                         dis_cs : checker_state }

val empty_dag_infer_state : checker_state -> dag_infer_state

val dis_find : bool -> positive -> positive -> dag_infer_state -> cexpr option

val dis_put :
  bool -> positive -> positive -> cexpr -> dag_infer_state -> dag_infer_state

type 'a d_act = dag_infer_state -> ('a result, dag_infer_state) prod

val d_ret : 'a1 -> 'a1 d_act

val d_pure : 'a1 result -> 'a1 d_act

val d_lift : 'a1 c_act -> 'a1 d_act

val d_bind : 'a1 d_act -> ('a1 -> 'a2 d_act) -> 'a2 d_act

val d_push_binding :
  c_context -> positive -> cexpr -> positive option -> cexpr option ->
  c_context d_act

val c_dag_infer :
  declaration_lookup -> environment -> bool -> bool -> nat -> c_methods ->
  nat -> name list -> dag_arena -> c_arena_table -> bool -> positive ->
  c_context -> cexpr d_act

val c_run_dag_infer :
  declaration_lookup -> fuel_config -> environment -> bool -> bool -> bool ->
  nat -> name list -> dag_arena -> c_arena_table -> positive -> cexpr c_act

val c_whnf_top :
  declaration_lookup -> fuel_config -> environment -> bool -> bool -> bool ->
  name list -> c_context -> cexpr -> cexpr c_act

val c_defeq_top :
  declaration_lookup -> fuel_config -> environment -> bool -> bool -> bool ->
  name list -> c_context -> cexpr -> cexpr -> bool c_act

val c_input_header :
  declaration_lookup -> fuel_config -> environment -> bool -> bool -> bool ->
  nat -> name -> name list -> dag_arena -> c_arena_table -> positive ->
  scope_entry -> unit0 c_act

val c_input_check :
  declaration_lookup -> fuel_config -> environment -> bool -> bool -> bool ->
  nat -> name list -> dag_arena -> c_arena_table -> positive -> positive ->
  cexpr -> unit0 c_act

val c_input_proposition :
  declaration_lookup -> fuel_config -> environment -> bool -> bool -> bool ->
  nat -> name list -> dag_arena -> c_arena_table -> positive -> unit0 c_act

val c_admit_dag_delta :
  declaration_lookup -> fuel_config -> environment -> bool -> bool -> bool ->
  dag_admission_kind -> nat -> name -> name list -> (positive, dag_node) prod
  list -> positive -> positive -> environment result

val cached_batch_delta :
  fuel_config -> runtime_state -> admission_batch -> environment result

val admit_batch_cached :
  fuel_config -> runtime_state -> admission_batch -> runtime_state result

val cached_transaction :
  fuel_config -> runtime_state -> admission_batch -> (runtime_state, unit0
  result) prod
