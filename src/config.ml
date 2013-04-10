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

(** Debuggin options. *)
module Debug = struct
  let reduce = ref true
end
