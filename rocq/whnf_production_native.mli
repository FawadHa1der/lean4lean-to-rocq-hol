
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
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val seq : nat -> nat -> nat list

val firstn : nat -> 'a1 list -> 'a1 list

val skipn : nat -> 'a1 list -> 'a1 list

val nth_error : 'a1 list -> nat -> 'a1 option

val rev : 'a1 list -> 'a1 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

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

val eqb0 : ascii -> ascii -> bool

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

val normal_whnf_rounds : nat

val eager_whnf_rounds : nat

val whnf_round_limit : reduction_mode -> nat

type whnf_round =
| WhnfDone of expr
| WhnfContinue of expr

val run_whnf_rounds :
  nat -> (expr -> whnf_round result) -> expr -> expr result

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

val level_equiv : nat -> level -> level -> bool result

val levels_equiv : nat -> level list -> level list -> bool result

val nat_probe_head :
  (name -> environment -> declaration option) -> name -> environment ->
  (expr, expr list) prod -> bool

val pair_probe_guard : bool -> bool -> (unit0 -> bool) -> bool

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

val checker_eager_mode :
  reduction_mode -> nat -> environment -> name list -> methods

val checker_mode :
  reduction_mode -> nat -> environment -> name list -> methods

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

  val checker_eager_mode :
    (name -> environment -> declaration option) -> reduction_mode -> nat ->
    environment -> name list -> methods

  val checker_mode :
    (name -> environment -> declaration option) -> reduction_mode -> nat ->
    environment -> name list -> methods
 end
