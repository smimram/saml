module Compiler = struct
  let coerce = ref true

  module Coerce = struct
    (** Coerce (x,a=...,b=...) into x. *)
    let records = ref false
  end

  let optimize = ref false
end

module Debug = struct
  let reduce = ref true
end
