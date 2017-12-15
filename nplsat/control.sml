structure Control = struct
  datatype errorCode = InputError | UnexpectedError
  exception Error of errorCode
  exception Unsatisfiable
  exception EndOfInput
end
