(** Configuration options. *)

module Debug = struct
  module Typing = struct
    let show_levels = ref true
  end
end

module Compiler = struct
  let optimize = ref false
end
