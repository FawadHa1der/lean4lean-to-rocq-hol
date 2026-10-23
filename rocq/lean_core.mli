
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

module Nat :
 sig
  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val max : nat -> nat -> nat
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val seq : nat -> nat -> nat list

val firstn : nat -> 'a1 list -> 'a1 list

val skipn : nat -> 'a1 list -> 'a1 list

val nth_error : 'a1 list -> nat -> 'a1 option

val rev : 'a1 list -> 'a1 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val find : ('a1 -> bool) -> 'a1 list -> 'a1 option

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Pos :
 sig
  val succ : positive -> positive

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

  val pow : positive -> positive -> positive

  val size_nat : positive -> nat

  val size : positive -> positive

  val gcdn : nat -> positive -> positive -> positive

  val gcd : positive -> positive -> positive

  val shiftl : positive -> n -> positive
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
 end

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val zero : ascii

val one : ascii

val shift : bool -> ascii -> ascii

val eqb0 : ascii -> ascii -> bool

val ascii_of_pos : positive -> ascii

val ascii_of_N : n -> ascii

val ascii_of_nat : nat -> ascii

val n_of_digits : bool list -> n

val n_of_ascii : ascii -> n

val nat_of_ascii : ascii -> nat

type string =
| EmptyString
| String of ascii * string

val eqb1 : string -> string -> bool

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

val level_eval : (name -> nat) -> level -> nat

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

val guard_holds : (name -> nat) -> name list -> bool

val sublevel_eval : (name -> nat) -> sublevel -> nat

val sublevels_eval : (name -> nat) -> sublevel list -> nat

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

val close_lam : ind_local list -> expr -> expr

val apply_exprs : expr -> expr list -> expr

val apply_locals : expr -> ind_local list -> expr

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

val check_declarations :
  nat -> environment -> input_decl list -> environment result

val nm : string -> name

val u : level

val v : level

val w : level

val one0 : level

val two0 : level

val prop0 : expr

val type1 : expr

val type2 : expr

val id_type : expr

val id_term : expr

val prop_id_type : expr

val prop_id : expr

val proof_context : context

val function_context : context

val eta_f : expr

val id_decl : decl_kind -> declaration

val level_decl : declaration

val cyclic_decl : declaration

val accepted : 'a1 result -> bool

val rejected : 'a1 result -> bool

val declined : 'a1 result -> bool

val decided_true : bool result -> bool

val regression_checks : unit0 -> bool list

val ext_ctor : name -> nat -> nat -> constructor_data

val ext_ind : name -> name list -> bool -> inductive_data

val ext_decl : name -> expr -> decl_kind -> expr option -> declaration

val ext_nat_decl : declaration

val ext_zero_decl : declaration

val ext_succ_decl : declaration

val ext_nat_env : declaration list

val ext_box_name : name

val ext_box_mk : name

val ext_box : expr

val ext_box_decl : declaration

val ext_box_ctor : declaration

val ext_box_env : declaration list

val ext_box_value : expr

val ext_box_ctx : context

val ext_box_motive : expr

val ext_box_minor : expr

val ext_box_rec_type : expr

val ext_box_rule : expr

val ext_box_rec_data : recursor_data

val ext_box_rec_name : name

val ext_box_rec_decl : declaration

val ext_rec_env : declaration list

val ext_unbox : expr -> expr

val ext_utf8_emoji : string

val ext_q_name : name

val ext_q_mk : name

val ext_q_lift : name

val ext_q_ind : name

val ext_q_env : declaration list

val ext_q_value : expr

val ext_q_function : expr

val ext_q_lift_app : expr

val ext_safety_name : name

val ext_safety_decl : decl_kind -> declaration

val ext_safety_term : expr

val extension_checks : unit0 -> bool list

val perf_delay : nat -> expr -> expr

val perf_arrow : expr

val perf_slow : name

val perf_slow_opaque : declaration

val perf_slow_decl : declaration

val perf_env : declaration list

val perf_two : expr

val perf_beta_two : expr

val perf_app : expr -> expr

val perf_discard : name

val perf_discard_decl : declaration

val perf_prop : name

val perf_proof : name

val perf_slow_proof : name

val perf_proof_type : expr

val perf_proof_env : declaration list

val perf_succs : nat -> expr

val perf_fnbox : name

val perf_fnmk : name

val perf_fnind : declaration

val perf_fnctor : declaration

val perf_fnvalue : expr

val perf_fnalias : declaration

val perf_fnenv : declaration list

val perf_fnapp : expr

val perf_peano : name

val perf_zero : name

val perf_succ : name

val perf_peano_type : expr

val perf_peano_env : declaration list

val perf_peano_numeral : nat -> expr

val perf_batch_function : expr

val performance_checks : unit0 -> bool list
