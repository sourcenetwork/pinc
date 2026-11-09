/-!
# A small JSON reader

Just enough JSON for the trace files: integers (a leading minus gives `neg`), strings without escapes beyond `\"` and `\\`,
booleans, `null`, arrays and objects. Used only by the `replay` executable.
-/

namespace Vinc.Json

/-- A JSON value. -/
inductive J where
  | num (n : Nat)
  | neg (n : Nat)
  | str (s : String)
  | bool (b : Bool)
  | null
  | arr (a : Array J)
  | obj (kv : Array (String × J))
  deriving Inhabited

private def skipWs (cs : Array Char) (i : Nat) : Nat :=
  if h : i < cs.size then
    if cs[i].isWhitespace then skipWs cs (i + 1) else i
  else i
termination_by cs.size - i

private def parseNum (cs : Array Char) (i acc : Nat) : Nat × Nat :=
  if h : i < cs.size then
    let c := cs[i]
    if c.isDigit then parseNum cs (i + 1) (acc * 10 + (c.toNat - '0'.toNat)) else (acc, i)
  else (acc, i)
termination_by cs.size - i

private def parseStr (cs : Array Char) (i : Nat) (acc : String) : Except String (String × Nat) :=
  if h : i < cs.size then
    let c := cs[i]
    if c == '"' then .ok (acc, i + 1)
    else if c == '\\' then
      match cs[i + 1]? with
      | some d => parseStr cs (i + 2) (acc.push d)
      | none => .error "unterminated escape"
    else parseStr cs (i + 1) (acc.push c)
  else .error "unterminated string"
termination_by cs.size - i

private def expect (cs : Array Char) (i : Nat) (lit : String) : Except String Nat :=
  let l := lit.toList
  if (l.mapIdx fun k c => cs[i + k]? == some c).all id then .ok (i + l.length)
  else .error s!"expected {lit} at {i}"

mutual
  private partial def parseVal (cs : Array Char) (i : Nat) : Except String (J × Nat) := do
    let i := skipWs cs i
    match cs[i]? with
    | some '{' => parseObj cs (skipWs cs (i + 1)) #[]
    | some '[' => parseArr cs (skipWs cs (i + 1)) #[]
    | some '"' =>
      let (s, j) ← parseStr cs (i + 1) ""
      pure (.str s, j)
    | some 't' => let j ← expect cs i "true"; pure (.bool true, j)
    | some 'f' => let j ← expect cs i "false"; pure (.bool false, j)
    | some 'n' => let j ← expect cs i "null"; pure (.null, j)
    | some '-' =>
      let (n, j) := parseNum cs (i + 1) 0
      pure (.neg n, j)
    | some c =>
      if c.isDigit then
        let (n, j) := parseNum cs i 0
        pure (.num n, j)
      else throw s!"unexpected '{c}' at {i}"
    | none => throw "unexpected end of input"

  private partial def parseArr (cs : Array Char) (i : Nat) (acc : Array J) : Except String (J × Nat) := do
    if cs[i]? == some ']' then return (.arr acc, i + 1)
    let (v, j) ← parseVal cs i
    let j := skipWs cs j
    match cs[j]? with
    | some ',' => parseArr cs (skipWs cs (j + 1)) (acc.push v)
    | some ']' => pure (.arr (acc.push v), j + 1)
    | _ => throw s!"expected ',' or ']' at {j}"

  private partial def parseObj (cs : Array Char) (i : Nat) (acc : Array (String × J)) : Except String (J × Nat) := do
    if cs[i]? == some '}' then return (.obj acc, i + 1)
    if cs[i]? != some '"' then throw s!"expected a key at {i}"
    let (k, j) ← parseStr cs (i + 1) ""
    let j := skipWs cs j
    if cs[j]? != some ':' then throw s!"expected ':' at {j}"
    let (v, j) ← parseVal cs (j + 1)
    let j := skipWs cs j
    match cs[j]? with
    | some ',' => parseObj cs (skipWs cs (j + 1)) (acc.push (k, v))
    | some '}' => pure (.obj (acc.push (k, v)), j + 1)
    | _ => throw s!"expected ',' or '}' at {j}"
end

/-- Parse one JSON document. -/
def parse (s : String) : Except String J := do
  let cs := s.toList.toArray
  let (v, i) ← parseVal cs 0
  if skipWs cs i < cs.size then throw s!"trailing input at {i}"
  pure v

/-- The member `k` of an object. -/
def J.get? (j : J) (k : String) : Option J :=
  match j with
  | .obj kv => kv.find? (·.1 == k) |>.map (·.2)
  | _ => none

def J.nat? : J → Option Nat
  | .num n => some n
  | _ => none

def J.int? : J → Option Int
  | .num n => some n
  | .neg n => some (-(n : Int))
  | _ => none

def J.bool? : J → Option Bool
  | .bool b => some b
  | _ => none

def J.str? : J → Option String
  | .str s => some s
  | _ => none

def J.arr? : J → Option (Array J)
  | .arr a => some a
  | _ => none

/-! ## Reading fields -/

def field (j : J) (k : String) : Except String J :=
  match j.get? k with
  | some v => pure v
  | none => throw s!"missing field {k}"

def natF (j : J) (k : String) : Except String Nat := do
  match (← field j k).nat? with
  | some n => pure n
  | none => throw s!"field {k} is not a number"

def intF (j : J) (k : String) : Except String Int := do
  match (← field j k).int? with
  | some n => pure n
  | none => throw s!"field {k} is not an integer"

def boolF (j : J) (k : String) : Except String Bool := do
  match (← field j k).bool? with
  | some n => pure n
  | none => throw s!"field {k} is not a bool"

def strF (j : J) (k : String) : Except String String := do
  match (← field j k).str? with
  | some n => pure n
  | none => throw s!"field {k} is not a string"

def natList (j : J) : Except String (List Nat) := do
  match j.arr? with
  | some a => a.toList.mapM fun v => match v.nat? with
    | some n => pure n
    | none => throw "expected a number"
  | none => throw "expected an array"

def intList (j : J) : Except String (List Int) := do
  match j.arr? with
  | some a => a.toList.mapM fun v => match v.int? with
    | some n => pure n
    | none => throw "expected an integer"
  | none => throw "expected an array"

def pairList (j : J) : Except String (List (Nat × Nat)) := do
  match j.arr? with
  | some a => a.toList.mapM fun v => do
    match ← natList v with
    | [x, y] => pure (x, y)
    | _ => throw "expected a pair"
  | none => throw "expected an array"

def check (ok : Bool) (msg : String) : Except String Unit :=
  if ok then pure () else throw msg

end Vinc.Json
