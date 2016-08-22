(** Configuration options. *)

module Debug = struct
  module Typing = struct
    let show_links = ref false

    (** Show levels of variables. *)
    let show_levels = ref false

    (** Show assignations of type variables. *)
    let show_assignations = ref false
  end
end

module Compiler = struct
  (** Optimize the code. *)
  let optimize = ref false
end
