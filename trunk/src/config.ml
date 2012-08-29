module Compiler = struct
  let coerce = ref true

  module Coerce = struct
    let records = ref true
  end

  let optimize = ref false
end

module Debug = struct
  let reduce = ref true
end
