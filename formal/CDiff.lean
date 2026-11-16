/-
  Differential-testing driver: runs the MiniC semantics of the translated
  C code (NANO.C.Gen) and the Lean specification on inputs read from stdin,
  printing results in the same format as formal/tools/cdiff_c.c (which runs
  the real compiled C under ASan/UBSan). formal/tools/cdiff.py compares them.

  Input lines (all hex bytes are concatenated byte pairs, decimal integers
  for scalars):
    u16le <hex 2+ bytes>
    u32le <hex 4+ bytes>
    i32le <hex 4+ bytes>
    u16be <hex 2+ bytes>
    u32be <hex 4+ bytes>
    size_mul <a> <b>
    size_add <a> <b>
    clamp_u8 <v>
    scale_to_8bit <v> <bit_depth>
    packed_bits <row hex> <pixel_index> <bit_depth>
    paeth <a> <b> <c>
-/
import NANO.Basic
import NANO.Bmp
import NANO.Tga
import NANO.C.Gen

open NANO NANO.C

def parseHex (s : String) : List UInt8 :=
  let cs := s.toList
  let rec go : List Char → List UInt8
    | a :: b :: rest =>
      let h (c : Char) : Nat :=
        if c.isDigit then c.toNat - '0'.toNat
        else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
        else c.toNat - 'A'.toNat + 10
      (h a * 16 + h b).toUInt8 :: go rest
    | _ => []
  go cs

def fuel : Nat := 10000

/-- Run a Gen function with a fresh input block and an output block. -/
def runGen (fid : Nat) (args : List Val) (input : List UInt8) : Res (Option Val × Mem) :=
  let mem : Mem := fun b =>
    if b = 0 then some input
    else if b = 1 then some (List.replicate 16 0)
    else none
  callFunc Gen.prog fuel fid args mem

def showRes (r : Res (Option Val × Mem)) : String :=
  match r with
  | .ok (some (.int _ n), _) => toString n
  | .ok _ => "ERR"
  | .ub => "UB"
  | .timeout => "TIMEOUT"

def showOutBlock (r : Res (Option Val × Mem)) : String :=
  match r with
  | .ok (some (.int _ n), m) =>
    if n = 0 then "0"  -- failure: C prints no out value
    else
      match m 1 with
      | some blk => s!"1 {(decodeLE (blk.take 8))}"
      | none => "ERR"
  | .ok _ => "ERR"
  | .ub => "UB"
  | .timeout => "TIMEOUT"

def specPackedBits (row : List UInt8) (pixelIndex bitDepth : Nat) : Nat :=
  let bitIndex := pixelIndex * bitDepth
  let byteIndex := bitIndex / 8
  let shift := 8 - bitDepth - (bitIndex % 8)
  let mask := 2 ^ bitDepth - 1
  ((byteAt row byteIndex) / 2 ^ shift) &&& mask

def parseNatSigned (s : String) : Option Int :=
  if s.startsWith "-" then
    match (s.drop 1).toNat? with
    | some n => some (-(n : Int))
    | none => none
  else (s.toNat? : Option Nat).map (fun n => (n : Int))

def paethSpec (a b c : Nat) : Nat :=
  let p : Int := (a : Int) + (b : Int) - (c : Int)
  let pa := if p > (a : Int) then p - (a : Int) else (a : Int) - p
  let pb := if p > (b : Int) then p - (b : Int) else (b : Int) - p
  let pc := if p > (c : Int) then p - (c : Int) else (c : Int) - p
  if pa ≤ pb && pa ≤ pc then a else if pb ≤ pc then b else c

def scaleSpec (v bitDepth : Nat) : Option Nat :=
  if bitDepth = 0 || bitDepth > 8 then none
  else
    let maxv := 2 ^ bitDepth - 1
    -- C computes in u32: v*255 and + maxv/2 wrap mod 2^32.
    some ((((v * 255) % 4294967296 + maxv / 2) % 4294967296) / maxv % 256)


def bmpFuel : Nat := 3000000

def tgaFuel : Nat := 3000000

/-- `ni_tga_info` block size (8+8+4+4+1+1+1+1, padded to 32). -/
def tgaInfoSize : Nat := 32

/-- Little-endian field of a block. -/
def fieldAt (blk : List UInt8) (o n : Nat) : Nat := decodeLE ((blk.drop o).take n)

/-- `ni_bmp_info` fields, in the order printed by `formal/tools/cdiff_c.c`. -/
def infoFields (blk : List UInt8) : String :=
  s!"{fieldAt blk 0 8} {fieldAt blk 8 8} {fieldAt blk 16 8} {fieldAt blk 24 4} {fieldAt blk 28 4} {fieldAt blk 32 4} {fieldAt blk 36 4} {fieldAt blk 40 2} {fieldAt blk 42 1} {fieldAt blk 43 1}"

def hexByte (b : UInt8) : String :=
  let n := b.toNat
  let s := String.ofList (Nat.toDigits 16 n)
  if n < 16 then "0" ++ s else s

def toHex (bs : List UInt8) : String := String.join (bs.map hexByte)

def runLine (line : String) : String :=
  let parts := line.trimAscii.toString.splitOn " "
  match (if parts.length = 1 then parts ++ [""] else parts) with
  | ["u16le", hex] =>
    let d := parseHex hex
    let r := runGen Gen.fid_ni_read_u16le [.ptr 0 0] d
    s!"{showRes r} | {NANO.rd16le d 0}"
  | ["u32le", hex] =>
    let d := parseHex hex
    let r := runGen Gen.fid_ni_read_u32le [.ptr 0 0] d
    s!"{showRes r} | {NANO.rd32le d 0}"
  | ["i32le", hex] =>
    let d := parseHex hex
    let r := runGen Gen.fid_ni_read_i32le [.ptr 0 0] d
    -- C casts u32 -> i32 (two's complement re-interpretation).
    s!"{showRes r} | {NANO.rd32le d 0 % 4294967296}"
  | ["u16be", hex] =>
    let d := parseHex hex
    let r := runGen Gen.fid_ni_read_u16be [.ptr 0 0] d
    s!"{showRes r} | {NANO.rd16be d 0}"
  | ["u32be", hex] =>
    let d := parseHex hex
    let r := runGen Gen.fid_ni_read_u32be [.ptr 0 0] d
    s!"{showRes r} | {NANO.rd32be d 0}"
  | ["size_mul", a, b] =>
    let a := a.toNat!; let b := b.toNat!
    let r := runGen Gen.fid_ni_size_mul [.int IntTy.u64 a, .int IntTy.u64 b, .ptr 1 0] []
    let spec := if a != 0 ∧ b > (2 ^ 64 - 1) / a then "0" else s!"1 {a * b}"
    s!"{showOutBlock r} | {spec}"
  | ["size_add", a, b] =>
    let a := a.toNat!; let b := b.toNat!
    let r := runGen Gen.fid_ni_size_add [.int IntTy.u64 a, .int IntTy.u64 b, .ptr 1 0] []
    let spec := if a > (2 ^ 64 - 1) - b then "0" else s!"1 {a + b}"
    s!"{showOutBlock r} | {spec}"
  | ["clamp_u8", v] =>
    match parseNatSigned v with
    | none => "BADLINE"
    | some vi =>
      let r := runGen Gen.fid_ni_clamp_u8 [.int IntTy.i32 (IntTy.wrap IntTy.i32 vi)] []
      let spec := Int.natAbs (min 255 (max 0 vi))
      s!"{showRes r} | {spec}"
  | ["scale_to_8bit", v, depth] =>
    let v := v.toNat!; let depth := depth.toNat!
    -- MiniC writes through `out`; model validity as $1$ byte out on success.
    let mem := fun b => if b = 1 then some (List.replicate 16 0) else none
    let r := callFunc Gen.prog fuel Gen.fid_ni_scale_to_8bit
      [.int IntTy.u32 v, .int IntTy.u8 depth, .ptr 1 0] mem
    let c := match r with
      | .ok (some (.int _ n), m) =>
        if n = 0 then "0"
        else
          match m 1 with
          | some blk => s!"1 {blk.head!}"
          | none => "ERR"
      | .ok _ => "ERR"
      | .ub => "UB"
      | .timeout => "TIMEOUT"
    let spec := match scaleSpec v depth with
      | some s => s!"1 {s}"
      | none => "0"
    s!"{c} | {spec}"
  | ["packed_bits", row, pi, depth] =>
    let d := parseHex row; let pi := pi.toNat!; let depth := depth.toNat!
    let r := runGen Gen.fid_ni_read_packed_bits
      [.ptr 0 0, .int IntTy.u64 pi, .int IntTy.u8 depth] d
    s!"{showRes r} | {specPackedBits d pi depth}"
  | ["paeth", a, b, c] =>
    let a := a.toNat!; let b := b.toNat!; let c := c.toNat!
    let r := runGen Gen.fid_ni_paeth [.int IntTy.u8 a, .int IntTy.u8 b, .int IntTy.u8 c] []
    s!"{showRes r} | {paethSpec a b c}"
  | ["bmp_sig", hex] =>
    let d := parseHex hex
    let mem0 : Mem := fun b => if b = 0 then some d else none
    let r := callFunc Gen.prog bmpFuel Gen.fid_ni_bmp_sig_ok
      [.ptr 0 0, .int IntTy.u64 d.length] mem0
    s!"{showRes r} | {if sigOk d.length d then 1 else 0}"
  | ["bmp_layout", hex] =>
    let d := parseHex hex
    let mem0 : Mem := fun b => if b = 0 then some d else none
    let r := callFunc Gen.prog bmpFuel Gen.fid_ni_bmp_layout_ok
      [.ptr 0 0, .int IntTy.u64 d.length] mem0
    s!"{showRes r} | {if layoutOk d.length d then 1 else 0}"
  | ["bmp_mulfits", a, b] =>
    let a := a.toNat!; let b := b.toNat!
    let r := callFunc Gen.prog bmpFuel Gen.fid_ni_bmp_mul_fits
      [.int IntTy.u64 a, .int IntTy.u64 b] (fun _ => none)
    s!"{showRes r} | {if (a == 0 || b <= (2^64 - 1) / a) then 1 else 0}"
  | ["bmp_geometry", hex] =>
    let d := parseHex hex
    if d.length < 54 then "SKIP | SKIP"
    else
    let mem0 : Mem := fun b => if b = 0 then some d else if b = 1 then some (List.replicate 48 0) else none
    let r := callFunc Gen.prog bmpFuel Gen.fid_ni_bmp_geometry
      [.ptr 0 0, .int IntTy.u64 d.length, .ptr 1 0] mem0
    let c := match r with
      | .ok (some (.int _ code), m) =>
        if code = 0 then
          match m 1 with
          | some blk => s!"0 {fieldAt blk 24 4} {fieldAt blk 28 4} {fieldAt blk 40 2} {fieldAt blk 42 1} {fieldAt blk 43 1}"
          | none => "ERR"
        else toString code
      | .ok _ => "ERR"
      | .ub => "UB"
      | .timeout => "TIMEOUT"
    let spec := match bmpGeometry d with
      | .ok (w, h, bit, ch, td) => s!"0 {w} {h} {bit} {ch} {td}"
      | .error e => toString e
    s!"{c} | {spec}"
  | ["bmp_header", hex] =>
    let d := parseHex hex
    let mem0 : Mem := fun b => if b = 0 then some d else if b = 1 then some (List.replicate 48 0) else none
    let r := callFunc Gen.prog bmpFuel Gen.fid_ni_bmp_header
      [.ptr 0 0, .int IntTy.u64 d.length, .ptr 1 0] mem0
    let c := match r with
      | .ok (some (.int _ code), m) =>
        if code = 0 then
          match m 1 with
          | some blk => s!"0 {infoFields blk}"
          | none => "ERR"
        else toString code
      | .ok _ => "ERR"
      | .ub => "UB"
      | .timeout => "TIMEOUT"
    let spec := match bmpHeader d.length d with
      | .ok h => s!"0 {h.rowStride} {h.outSize} {h.paletteOffset} {h.width} {h.height} {h.pixelOffset} {h.paletteEntries} {h.bitCount} {h.channels} {h.topDown}"
      | .error e => toString e
    s!"{c} | {spec}"
  | ["bmp_decode", hex] =>
    let d := parseHex hex
    let mem0 : Mem := fun b => if b = 0 then some d else if b = 1 then some (List.replicate 48 0) else none
    let r0 := callFunc Gen.prog bmpFuel Gen.fid_ni_bmp_header
      [.ptr 0 0, .int IntTy.u64 d.length, .ptr 1 0] mem0
    let c := match r0 with
      | .ok (some (.int _ 0), m1) =>
        match m1 1 with
        | some info =>
          let outSize := fieldAt info 8 8
          let mem1 : Mem := fun b => if b = 2 then some (List.replicate outSize 0) else m1 b
          match callFunc Gen.prog bmpFuel Gen.fid_ni_bmp_decode_into
              [.ptr 0 0, .int IntTy.u64 d.length, .ptr 1 0, .ptr 2 0, .int IntTy.u64 outSize] mem1 with
          | .ok (some (.int _ 0), m2) =>
            match m2 2 with
            | some out => s!"0 {toHex (out.take outSize)}"
            | none => "ERR"
          | .ok (some (.int _ code), _) => toString code
          | .ok _ => "ERR"
          | .ub => "UB"
          | .timeout => "TIMEOUT"
        | none => "ERR"
      | .ok (some (.int _ code), _) => toString code
      | .ok _ => "ERR"
      | .ub => "UB"
      | .timeout => "TIMEOUT"
    let spec := match bmpDecode d with
      | .ok px => s!"0 {toHex px}"
      | .error e => toString e
    s!"{c} | {spec}"
  | ["tga_header", hex] =>
    let d := parseHex hex
    let mem0 : Mem := fun b => if b = 0 then some d else if b = 1 then some (List.replicate tgaInfoSize 0) else none
    let r := callFunc Gen.prog tgaFuel Gen.fid_ni_tga_header
      [.ptr 0 0, .int IntTy.u64 d.length, .ptr 1 0] mem0
    let c := match r with
      | .ok (some (.int _ code), m) =>
        if code = 0 then
          match m 1 with
          | some blk => s!"0 {fieldAt blk 0 8} {fieldAt blk 8 8} {fieldAt blk 16 4} {fieldAt blk 20 4} {fieldAt blk 24 1} {fieldAt blk 25 1} {fieldAt blk 26 1} {fieldAt blk 27 1}"
          | none => "ERR"
        else toString code
      | .ok _ => "ERR"
      | .ub => "UB"
      | .timeout => "TIMEOUT"
    let spec := match tgaHeader d.length d with
      | .ok h => s!"0 {h.outputSize} {h.dataOffset} {h.width} {h.height} {h.channels} {h.rle} {h.topOrigin} {h.rightOrigin}"
      | .error e => toString e
    s!"{c} | {spec}"
  | ["tga_decode", hex] =>
    let d := parseHex hex
    let mem0 : Mem := fun b => if b = 0 then some d else if b = 1 then some (List.replicate tgaInfoSize 0) else none
    let r0 := callFunc Gen.prog tgaFuel Gen.fid_ni_tga_header
      [.ptr 0 0, .int IntTy.u64 d.length, .ptr 1 0] mem0
    let c := match r0 with
      | .ok (some (.int _ 0), m1) =>
        match m1 1 with
        | some info =>
          let outSize := fieldAt info 0 8
          let mem1 : Mem := fun b => if b = 2 then some (List.replicate outSize 0) else m1 b
          match callFunc Gen.prog tgaFuel Gen.fid_ni_tga_decode_into
              [.ptr 0 0, .int IntTy.u64 d.length, .ptr 1 0, .ptr 2 0, .int IntTy.u64 outSize] mem1 with
          | .ok (some (.int _ 0), m2) =>
            match m2 2 with
            | some out => s!"0 {toHex (out.take outSize)}"
            | none => "ERR"
          | .ok (some (.int _ code), _) => toString code
          | .ok _ => "ERR"
          | .ub => "UB"
          | .timeout => "TIMEOUT"
        | none => "ERR"
      | .ok (some (.int _ code), _) => toString code
      | .ok _ => "ERR"
      | .ub => "UB"
      | .timeout => "TIMEOUT"
    let spec := match tgaDecode d with
      | .ok px => s!"0 {toHex px}"
      | .error e => toString e
    s!"{c} | {spec}"
  | _ => "BADLINE"

def main : IO Unit := do
  let stdin ← IO.getStdin
  let mut line ← stdin.getLine
  while line != "" do
    IO.println (runLine line)
    line ← stdin.getLine
