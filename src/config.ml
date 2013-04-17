(** Configuration options. *)

(** Compiler related options. *)
module Compiler = struct
  let coerce = ref false

  module Coerce = struct
    (** Coerce (x,a=...,b=...) into x. *)
    let records = ref true
  end

  let optimize = ref false
end

(** Debugging options. *)
module Debug = struct
  let reduce = ref true

  module Typing = struct
    (** Show types of variables declared by lets. *)
    let show_decl_types = ref false

    (** Show assignations of universal variables (during unification). *)
    let show_assignations = ref false

    (** Show unique names for universal variables. *)
    let show_unique_names = ref false

    (** Show typing levels for universal variables. *)
    let show_levels = ref false
  end
end
