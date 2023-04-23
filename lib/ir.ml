type bin_op =
| Add
| Sub
| Mul
| Div
| Mod
| Eq
| Ne
| Lt
| Le
| Gt
| Ge
| LOr
| LAnd
;;

type un_op =
| LNot
;;

type cast_op =
| Truncate
| Extend
| Bitwise
;;

let fmt_cast_op op =
  match op with
  | Truncate -> "trunc"
  | Bitwise -> "bitwise"
  | Extend -> "extend"
;;

let fmt_un_op op =
  match op with
  | LNot -> "!"
;;

let fmt_bin_op op =
  match op with
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%%"
  | Eq -> "=="
  | Ne -> "!="
  | Lt -> "<"
  | Le -> "<="
  | Gt -> ">"
  | Ge -> ">="
  | LOr -> "||"
  | LAnd -> "&&"
;;
