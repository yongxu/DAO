/-
# Sexp — S-expression AST + parser for the R-hierarchy Lisp

Hand-written recursive-descent parser. ASCII-friendly input (UTF-8 atoms supported
since `Char.isWhitespace` and the atom-char predicate are byte-safe).

## Sexp constructors

- `atom s` — a bare token (identifier, numeric literal, …)
- `list xs` — parenthesized list
- `named lbl body` — F.2 forward-compat hook for 文言 phrases.
  Surface syntax: `lbl:body` parses to `Sexp.named lbl body`. e.g. `若:X` →
  `Sexp.named "若" "X"`. Used later when the 文言 grammar surface lands; v1
  Lisp programs ignore this constructor.

## Quote shorthand

`'sexp` parses to `Sexp.list [Sexp.atom "quote", sexp]`. Standard Lisp.

## Parser surface

`Sexp.parse : String → Except ParseErr Sexp` — parses one top-level form.
-/

namespace SSBX.Foundation.Lang

/-- S-expression AST for the R-hierarchy Lisp surface. -/
inductive Sexp : Type
  | atom (s : String)
  | list (xs : List Sexp)
  | named (label : String) (body : String)
  deriving Repr, Inhabited

namespace Sexp

-- Hand-rolled `beq` because the default `deriving DecidableEq` doesn't handle
-- the `List Sexp` recursive case. We define `beq` and `listBeq` mutually and
-- expose `BEq Sexp` from it.
mutual
  def beq : Sexp → Sexp → Bool
    | atom a, atom b              => a == b
    | named la lb, named ra rb    => la == ra && lb == rb
    | list xs,    list ys         => listBeq xs ys
    | _, _                        => false
  def listBeq : List Sexp → List Sexp → Bool
    | [],       []       => true
    | x :: xs,  y :: ys  => beq x y && listBeq xs ys
    | _,        _        => false
end

instance : BEq Sexp := ⟨beq⟩

end Sexp

/-- Parse error variants. -/
inductive ParseErr : Type
  | unexpectedEOF
  | unmatchedClose
  | empty
  | trailingGarbage (rest : String)
  deriving Repr, Inhabited

namespace Parser

/-- A character is part of a bare atom token iff it is not whitespace and
not a structural delimiter. -/
@[inline] def isAtomChar (c : Char) : Bool :=
  !c.isWhitespace && c != '(' && c != ')' && c != '\'' && c != ':'

partial def skipWS : List Char → List Char
  | [] => []
  | c :: rest => if c.isWhitespace then skipWS rest else c :: rest

/-- Take a maximal prefix of atom-chars; return (atom-string, remaining-input). -/
def takeAtom (cs : List Char) : String × List Char :=
  let taken := cs.takeWhile isAtomChar
  let rest  := cs.dropWhile isAtomChar
  (String.ofList taken, rest)

mutual
partial def parseOne (cs : List Char) : Except ParseErr (Sexp × List Char) :=
  let cs := skipWS cs
  match cs with
  | [] => .error .empty
  | '(' :: rest => parseList rest []
  | ')' :: _    => .error .unmatchedClose
  | '\'' :: rest =>
      match parseOne rest with
      | .ok (s, r) => .ok (.list [.atom "quote", s], r)
      | .error e   => .error e
  | _ =>
      let (a, r) := takeAtom cs
      match r with
      | ':' :: r' =>
          let (b, r'') := takeAtom r'
          .ok (.named a b, r'')
      | _ => .ok (.atom a, r)

partial def parseList (cs : List Char) (acc : List Sexp) :
    Except ParseErr (Sexp × List Char) :=
  let cs := skipWS cs
  match cs with
  | [] => .error .unexpectedEOF
  | ')' :: rest => .ok (.list acc.reverse, rest)
  | _ =>
      match parseOne cs with
      | .ok (s, rest) => parseList rest (s :: acc)
      | .error e      => .error e
end

end Parser

namespace Sexp

/-- Parse a single top-level S-expression. Trailing whitespace is allowed; any
non-whitespace remainder is reported as `trailingGarbage`. -/
def parse (s : String) : Except ParseErr Sexp :=
  match Parser.parseOne s.toList with
  | .error e => .error e
  | .ok (sexp, rest) =>
      let trimmed := Parser.skipWS rest
      if trimmed.isEmpty then .ok sexp
      else .error (.trailingGarbage (String.ofList trimmed))

/-- Pretty-print an Sexp. Round-trips with `parse` modulo whitespace. -/
partial def toStr : Sexp → String
  | atom s        => s
  | named l b     => l ++ ":" ++ b
  | list xs       => "(" ++ String.intercalate " " (xs.map toStr) ++ ")"

instance : ToString Sexp := ⟨toStr⟩

end Sexp

/-! ## Smoke checks (runtime, since `Sexp.parse` is partial)

`#eval` lines below verify the parser at elaboration time. These are not
theorems (partial defs don't reduce under `rfl`), but they catch regressions
when this file is rebuilt.
-/

#eval (Sexp.parse "yao" : Except ParseErr Sexp)
#eval (Sexp.parse "()" : Except ParseErr Sexp)
#eval (Sexp.parse "(yao 1)" : Except ParseErr Sexp)
#eval (Sexp.parse "'(yao 0)" : Except ParseErr Sexp)
#eval (Sexp.parse "若:X" : Except ParseErr Sexp)
#eval (Sexp.parse "(rule (=> a b))" : Except ParseErr Sexp)

end SSBX.Foundation.Lang
