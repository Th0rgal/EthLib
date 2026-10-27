import EthLib.Cryptography.Xmss.Blake2s
import Lean
namespace EthLib.Cryptography.Xmss.Blake2s.Fast
macro "origMix" : term =>
  pure (Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.mix))
macro "origCompress" : term =>
  pure (Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.compress))
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
structure Words16 where
  w0 : UInt32
  w1 : UInt32
  w2 : UInt32
  w3 : UInt32
  w4 : UInt32
  w5 : UInt32
  w6 : UInt32
  w7 : UInt32
  w8 : UInt32
  w9 : UInt32
  w10 : UInt32
  w11 : UInt32
  w12 : UInt32
  w13 : UInt32
  w14 : UInt32
  w15 : UInt32
  deriving DecidableEq
def Words16.toArray (s : Words16) : Array UInt32 := #[s.w0, s.w1, s.w2, s.w3, s.w4, s.w5, s.w6, s.w7, s.w8, s.w9, s.w10, s.w11, s.w12, s.w13, s.w14, s.w15]
structure Words4 where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  deriving DecidableEq
def ror (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32-n))
def quarter (a b c d x y : UInt32) : Words4 :=
  let a := a + b + x
  let d := ror (d ^^^ a) 16
  let c := c + d
  let b := ror (b ^^^ c) 12
  let a := a + b + y
  let d := ror (d ^^^ a) 8
  let c := c + d
  let b := ror (b ^^^ c) 7
  ⟨a,b,c,d⟩
def mix0 (s : Words16) (x y : UInt32) : Words16 :=
  let q := quarter s.w0 s.w4 s.w8 s.w12 x y
  { s with w0 := q.a, w4 := q.b, w8 := q.c, w12 := q.d }
macro "simpMix0" : tactic =>
  let n := Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.mix)
  let r := Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.rotateRight)
  `(tactic| simp [$n:ident, $r:ident, mix0, Words16.toArray, quarter, ror])
theorem mix0_eq (s : Words16) (x y : UInt32) : origMix s.toArray 0 4 8 12 x y = (mix0 s x y).toArray := by cases s; simpMix0
def mix1 (s : Words16) (x y : UInt32) : Words16 :=
  let q := quarter s.w1 s.w5 s.w9 s.w13 x y
  { s with w1 := q.a, w5 := q.b, w9 := q.c, w13 := q.d }
macro "simpMix1" : tactic =>
  let n := Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.mix)
  let r := Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.rotateRight)
  `(tactic| simp [$n:ident, $r:ident, mix1, Words16.toArray, quarter, ror])
theorem mix1_eq (s : Words16) (x y : UInt32) : origMix s.toArray 1 5 9 13 x y = (mix1 s x y).toArray := by cases s; simpMix1
def mix2 (s : Words16) (x y : UInt32) : Words16 :=
  let q := quarter s.w2 s.w6 s.w10 s.w14 x y
  { s with w2 := q.a, w6 := q.b, w10 := q.c, w14 := q.d }
macro "simpMix2" : tactic =>
  let n := Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.mix)
  let r := Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.rotateRight)
  `(tactic| simp [$n:ident, $r:ident, mix2, Words16.toArray, quarter, ror])
theorem mix2_eq (s : Words16) (x y : UInt32) : origMix s.toArray 2 6 10 14 x y = (mix2 s x y).toArray := by cases s; simpMix2
def mix3 (s : Words16) (x y : UInt32) : Words16 :=
  let q := quarter s.w3 s.w7 s.w11 s.w15 x y
  { s with w3 := q.a, w7 := q.b, w11 := q.c, w15 := q.d }
macro "simpMix3" : tactic =>
  let n := Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.mix)
  let r := Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.rotateRight)
  `(tactic| simp [$n:ident, $r:ident, mix3, Words16.toArray, quarter, ror])
theorem mix3_eq (s : Words16) (x y : UInt32) : origMix s.toArray 3 7 11 15 x y = (mix3 s x y).toArray := by cases s; simpMix3
def mix4 (s : Words16) (x y : UInt32) : Words16 :=
  let q := quarter s.w0 s.w5 s.w10 s.w15 x y
  { s with w0 := q.a, w5 := q.b, w10 := q.c, w15 := q.d }
macro "simpMix4" : tactic =>
  let n := Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.mix)
  let r := Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.rotateRight)
  `(tactic| simp [$n:ident, $r:ident, mix4, Words16.toArray, quarter, ror])
theorem mix4_eq (s : Words16) (x y : UInt32) : origMix s.toArray 0 5 10 15 x y = (mix4 s x y).toArray := by cases s; simpMix4
def mix5 (s : Words16) (x y : UInt32) : Words16 :=
  let q := quarter s.w1 s.w6 s.w11 s.w12 x y
  { s with w1 := q.a, w6 := q.b, w11 := q.c, w12 := q.d }
macro "simpMix5" : tactic =>
  let n := Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.mix)
  let r := Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.rotateRight)
  `(tactic| simp [$n:ident, $r:ident, mix5, Words16.toArray, quarter, ror])
theorem mix5_eq (s : Words16) (x y : UInt32) : origMix s.toArray 1 6 11 12 x y = (mix5 s x y).toArray := by cases s; simpMix5
def mix6 (s : Words16) (x y : UInt32) : Words16 :=
  let q := quarter s.w2 s.w7 s.w8 s.w13 x y
  { s with w2 := q.a, w7 := q.b, w8 := q.c, w13 := q.d }
macro "simpMix6" : tactic =>
  let n := Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.mix)
  let r := Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.rotateRight)
  `(tactic| simp [$n:ident, $r:ident, mix6, Words16.toArray, quarter, ror])
theorem mix6_eq (s : Words16) (x y : UInt32) : origMix s.toArray 2 7 8 13 x y = (mix6 s x y).toArray := by cases s; simpMix6
def mix7 (s : Words16) (x y : UInt32) : Words16 :=
  let q := quarter s.w3 s.w4 s.w9 s.w14 x y
  { s with w3 := q.a, w4 := q.b, w9 := q.c, w14 := q.d }
macro "simpMix7" : tactic =>
  let n := Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.mix)
  let r := Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.rotateRight)
  `(tactic| simp [$n:ident, $r:ident, mix7, Words16.toArray, quarter, ror])
theorem mix7_eq (s : Words16) (x y : UInt32) : origMix s.toArray 3 4 9 14 x y = (mix7 s x y).toArray := by cases s; simpMix7

def roundArray (s : Array UInt32) (m : Array UInt32) (t : Array Nat) : Array UInt32 :=
  let s := origMix s 0 4 8 12 m[t[0]!]! m[t[1]!]!
  let s := origMix s 1 5 9 13 m[t[2]!]! m[t[3]!]!
  let s := origMix s 2 6 10 14 m[t[4]!]! m[t[5]!]!
  let s := origMix s 3 7 11 15 m[t[6]!]! m[t[7]!]!
  let s := origMix s 0 5 10 15 m[t[8]!]! m[t[9]!]!
  let s := origMix s 1 6 11 12 m[t[10]!]! m[t[11]!]!
  let s := origMix s 2 7 8 13 m[t[12]!]! m[t[13]!]!
  let s := origMix s 3 4 9 14 m[t[14]!]! m[t[15]!]!
  s
def roundFast (s : Words16) (m : Array UInt32) (t : Array Nat) : Words16 :=
  let s := mix0 s m[t[0]!]! m[t[1]!]!
  let s := mix1 s m[t[2]!]! m[t[3]!]!
  let s := mix2 s m[t[4]!]! m[t[5]!]!
  let s := mix3 s m[t[6]!]! m[t[7]!]!
  let s := mix4 s m[t[8]!]! m[t[9]!]!
  let s := mix5 s m[t[10]!]! m[t[11]!]!
  let s := mix6 s m[t[12]!]! m[t[13]!]!
  let s := mix7 s m[t[14]!]! m[t[15]!]!
  s
theorem round_eq (s : Words16) (m : Array UInt32) (t : Array Nat) :
    roundArray s.toArray m t = (roundFast s m t).toArray := by
  simp only [roundArray, roundFast, mix0_eq, mix1_eq, mix2_eq, mix3_eq, mix4_eq, mix5_eq, mix6_eq, mix7_eq]

macro "origIV" : term =>
  pure (Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.IV))
structure Words8 where
  w0 : UInt32
  w1 : UInt32
  w2 : UInt32
  w3 : UInt32
  w4 : UInt32
  w5 : UInt32
  w6 : UInt32
  w7 : UInt32
def Words8.toArray (s : Words8) : Array UInt32 := #[s.w0,s.w1,s.w2,s.w3,s.w4,s.w5,s.w6,s.w7]
def fromWords8 (s : Words8) (last : Bool) (counter : UInt64) : Words16 :=
  let iv := origIV
  let w12 := iv[4]! ^^^ (counter.toUInt32)
  let w13 := iv[5]! ^^^ ((counter >>> 32).toUInt32)
  let w14 := if last then ~~~iv[6]! else iv[6]!
  { w0:=s.w0, w1:=s.w1, w2:=s.w2, w3:=s.w3,
    w4:=s.w4, w5:=s.w5, w6:=s.w6, w7:=s.w7,
    w8:=iv[0]!, w9:=iv[1]!, w10:=iv[2]!, w11:=iv[3]!,
    w12:=w12, w13:=w13, w14:=w14, w15:=iv[7]! }
def roundFast10 (s : Words16) (m : Array UInt32) : Words16 :=

  let s := roundFast s m (Internal.sigma[0]!)
  let s := roundFast s m (Internal.sigma[1]!)
  let s := roundFast s m (Internal.sigma[2]!)
  let s := roundFast s m (Internal.sigma[3]!)
  let s := roundFast s m (Internal.sigma[4]!)
  let s := roundFast s m (Internal.sigma[5]!)
  let s := roundFast s m (Internal.sigma[6]!)
  let s := roundFast s m (Internal.sigma[7]!)
  let s := roundFast s m (Internal.sigma[8]!)
  let s := roundFast s m (Internal.sigma[9]!)
  s
def output (ch : Words8) (w : Words16) : Words8 :=
  { w0 := ch.w0 ^^^ w.w0 ^^^ w.w8, w1 := ch.w1 ^^^ w.w1 ^^^ w.w9,
    w2 := ch.w2 ^^^ w.w2 ^^^ w.w10, w3 := ch.w3 ^^^ w.w3 ^^^ w.w11,
    w4 := ch.w4 ^^^ w.w4 ^^^ w.w12, w5 := ch.w5 ^^^ w.w5 ^^^ w.w13,
    w6 := ch.w6 ^^^ w.w6 ^^^ w.w14, w7 := ch.w7 ^^^ w.w7 ^^^ w.w15 }
def fastCompress (ch : Words8) (m : Array UInt32) (counter : UInt64) (last : Bool) : Words8 :=
  output ch (roundFast10 (fromWords8 ch last counter) m)
theorem ten_eq (s : Words16) (m : Array UInt32) :
    (List.range' 0 10).foldl (fun s r => roundArray s m Internal.sigma[r]!) s.toArray =
      (roundFast10 s m).toArray := by
  simp only [List.range', List.foldl, Nat.reduceAdd, round_eq, roundFast10]
macro "simpCompForm" : tactic =>
  let n := Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.compress)
  let v := Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.IV)
  `(tactic| simp [$n:ident, $v:ident, roundArray, fromWords8, Words8.toArray, Words16.toArray, Internal.counterLow, Internal.counterHigh])
theorem compress_form (ch : Words8) (m : Array UInt32) (counter : UInt64) (last : Bool) :
    origCompress ch.toArray m counter last =
      let w := (List.range' 0 10).foldl (fun s r => roundArray s m Internal.sigma[r]!) (fromWords8 ch last counter).toArray
      Array.ofFn (fun i : Fin 8 => ch.toArray[i.val]! ^^^ w[i.val]! ^^^ w[i.val+8]!) := by
  cases ch
  cases last <;> simpCompForm
theorem output_eq (ch : Words8) (w : Words16) :
    Array.ofFn (fun i : Fin 8 => ch.toArray[i.val]! ^^^ w.toArray[i.val]! ^^^ w.toArray[i.val+8]!) =
      (output ch w).toArray := by
  cases ch
  cases w
  rfl
theorem compress_eq (ch : Words8) (m : Array UInt32) (counter : UInt64) (last : Bool) :
    origCompress ch.toArray m counter last = (fastCompress ch m counter last).toArray := by
  rw [compress_form, ten_eq]
  exact output_eq ch _
#print axioms compress_eq
end EthLib.Cryptography.Xmss.Blake2s.Fast
