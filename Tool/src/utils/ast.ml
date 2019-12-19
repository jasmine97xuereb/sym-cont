module rec Literal : sig
  type t =
    | Int of int
    | Bool of bool
end = Literal

and Identifier : sig
  type t = {
    name: string
  }
end = Identifier

and Expression : sig
  module UnaryExp : sig
    type operator =
      | Not

    type t = {
      operator: operator;
      arg: Expression.t;
    }
  end

  module BinaryExp : sig
    type operator =
      | Plus
      | Minus
      | Mult
      | Div
      | Lt
      | Gt
      | Leq
      | Geq
      | Compare
      | And
      | Or
      | Mod

    type t = {
      operator: operator;
      arg_lt: Expression.t;
      arg_rt: Expression.t;
    }
  end

  type t =
    | Identifier of Identifier.t
    | Literal of Literal.t
    | BinaryExp of BinaryExp.t
    | UnaryExp of UnaryExp.t
end = Expression

and TVar : sig
  type t = {
    tvar: string
  }
end = TVar

and Monitor : sig
  module Verdict : sig
    type v =
      | ZERO
      | ONE
      | TWO
      | ERR

    type t = {
      verd: v;
    }
  end

  module ExpressionGuard : sig
    type t = {
      label: Identifier.t;
      payload: Expression.t;
      consume: Monitor.t;
    }
  end

  module QuantifiedGuard : sig
    type t = {
      label: Identifier.t;
      payload: Expression.t;
      consume: Monitor.t;
    }
  end

  module Choice : sig
    type t = {
      left: Monitor.t;
      right: Monitor.t;
    }
  end

  module Conditional : sig
    type t = {
      condition: Expression.t;
      if_true: Monitor.t;
      if_false: Monitor.t;
    }
  end

  module Evaluate : sig
    type t = {
      var: Expression.t;
      subst: Expression.t;
      stmt: Monitor.t;
    }
  end

  module Recurse : sig
    type t = {
      monvar: TVar.t;
      consume: Monitor.t;
    }
  end

  type t =
    | TVar of TVar.t
    | Verdict of Verdict.t
    | ExpressionGuard of ExpressionGuard.t
    | QuantifiedGuard of QuantifiedGuard.t
    | Choice of Choice.t
    | Conditional of Conditional.t
    | Evaluate of Evaluate.t
    | Recurse of Recurse.t
end = Monitor

and TraceElement : sig
  type t = {
    label: Identifier.t;
    payload: Literal.t;
  }
end = TraceElement

and SymbolicEvent : sig
  type t = {
    label: Identifier.t;
    payload: Identifier.t;
  }
end = SymbolicEvent

and Trace : sig
  module SingleTrace : sig
    type t = {
      label: Identifier.t;
      payload: Literal.t;
    }
  end

  type t = Traces of SingleTrace.t list
end = Trace
