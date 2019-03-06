module Ascii : sig
  type t

  val box: string list -> t
  val shift: int -> int -> t -> t
  val line: int -> t
  val zcat: t -> t -> t
  val vcat: t -> t -> t

  val overlaps: t -> t -> bool

  val size: t -> int * int
  val render: t -> string
end = struct
  type t =
    | Box of string list
    | Shift of int * int * t
    | Line of int
    | Overlap of t * t

  let box l = Box l
  let line n = Line n
  let shift x y i = Shift (x, y, i)
  let zcat i1 i2 = Overlap (i1, i2)

  type rect =
    {
      x: int;
      y: int;
      width: int;
      height: int;
    }

  let rec bounding_rect i =
    let rec loop x y = function
      | Box l ->
          let width =
            let acc = ref 1 in
            List.iter (fun s -> acc := !acc + String.length s + 1) l;
            !acc
          in
          {x; y; width; height = 3}
      | Shift (dx, dy, i) ->
          loop (x + dx) (y + dy) i
      | Line height ->
          {x; y; width = 3; height}
      | Overlap (i1, i2) ->
          let r1 = loop x y i1 in
          let r2 = loop x y i2 in
          let x = min r1.x r2.x in
          let y = min r1.y r2.y in
          let width = max (r1.x + r1.width) (r2.x + r2.width) - x in
          let height = max (r1.y + r1.height) (r2.y + r2.height) - y in
          {x; y; width; height}
    in
    loop 0 0 i

  let shift_rect dx dy r =
    assert (0 <= dx && 0 <= dy);
    {r with x = r.x + dx; y = r.y + dy}

  let overlap_rect r1 r2 =
    let between min x max = min <= x && x <= max in
    (between r2.x r1.x (r2.x + r2.width) ||
     between r1.x r2.x (r1.x + r1.width)) &&
    (between r2.y r1.y (r2.y + r2.height) ||
     between r1.y r2.y (r1.y + r1.height))

  let rec overlaps i1 i2 =
    let rec loop (x1, y1, i1) (x2, y2, i2) =
      match i1, i2 with
      | Shift (dx1, dy1, i1), _ ->
          loop (x1 + dx1, y1 + dy1, i1) (x2, y2, i2)
      | _, Shift (dx2, dy2, i2) ->
          loop (x1, y1, i1) (x2 + dx2, y2 + dy2, i2)
      | Overlap (i1', i1''), _ ->
          loop (x1, y1, i1') (x2, y2, i2) || loop (x1, y1, i1'') (x2, y2, i2)
      | _, Overlap (i2', i2'') ->
          loop (x1, y1, i1) (x2, y2, i2') || loop (x1, y1, i1) (x2, y2, i2'')
      | Box _, Line _ | Line _, Box _ | Line _, Line _ | Box _, Box _ ->
          let r1 = bounding_rect i1 in
          let r2 = bounding_rect i2 in
          overlap_rect (shift_rect x1 y1 r1) (shift_rect x2 y2 r2)
    in
    loop (0, 0, i1) (0, 0, i2)

  let rec render a x y = function
    | Box l ->
        a.(y).(x) <- 0x250c;
        a.(y+1).(x) <- 0x2502;
        a.(y+2).(x) <- 0x2514;
        let x = ref x in
        List.iteri (fun idx s ->
            for i = 1 to String.length s do
              a.(y).(!x+i) <- 0x2500;
              a.(y+1).(!x+i) <- int_of_char s.[i-1];
              a.(y+2).(!x+i) <- 0x2500
            done;
            x := !x + String.length s + 1;
            if idx < List.length l - 1 then begin
              a.(y).(!x) <- 0x252c;
              a.(y+2).(!x) <- 0x2534;
            end else begin
              a.(y).(!x) <- 0x2510;
              a.(y+2).(!x) <- 0x2518
            end;
            a.(y+1).(!x) <- 0x2502
          ) l
    | Shift (dx, dy, i) ->
        render a (x + dx) (y + dy) i
    | Line n ->
        a.(y).(x) <- 0x252c;
        for i = 1 to n - 2 do
          a.(y+i).(x) <- 0x2502
        done;
        a.(y+n-1).(x) <- 0x2514;
        a.(y+n-1).(x+1) <- 0x2500;
        a.(y+n-1).(x+2) <- 0x2524
    | Overlap (i1, i2) ->
        render a x y i1;
        render a x y i2

  let size i =
    let r = bounding_rect i in
    r.x + r.width, r.y + r.height

  let vcat i1 i2 =
    let _, height = size i1 in
    zcat i1 (shift 0 height i2)

  let render i =
    let width, height = size i in
    let a = Array.make_matrix height width 0 in
    render a 0 0 i;
    let buf = Buffer.create ((width+1) * height) in
    for y = 0 to height - 1 do
      for x = 0 to width - 1 do
        let n = a.(y).(x) in
        if n <> 0 then
          Buffer.add_utf_8_uchar buf (Uchar.of_int n)
        else
          Buffer.add_char buf ' '
      done;
      Buffer.add_char buf '\n'
    done;
    Buffer.contents buf
end

let explode s =
  List.init (String.length s) (String.get s)

let min_field_size = 10

let fix s =
  if String.length s <= min_field_size then
    String.make (min_field_size - String.length s) ' ' ^ s
  else
    s

let rec block x =
  let tag = Obj.tag x in
  let size = Obj.size x in
  let fields =
    if Obj.first_non_constant_constructor_tag <= tag &&
       tag <= Obj.last_non_constant_constructor_tag
    then
      List.init size (fun i ->
          let x = Obj.field x i in
          if Obj.is_int x then
            Printf.sprintf "%d" (Obj.obj x)
          else
            ""
        )
    else if tag = Obj.double_tag then
      [Printf.sprintf "%F" (Obj.double_field x 0)]
    else if tag = Obj.double_array_tag then
      List.init size (fun i ->
          let x = Obj.double_field x i in
          Printf.sprintf "%F" x
        )
    else if tag = Obj.string_tag then
      let len = String.length (Obj.obj x) in
      let padding_len = (len + 8) / 8 * 8 - len in
      let padding = String.init padding_len (fun i -> if i = padding_len - 1 then char_of_int (padding_len - 1) else '\x00') in
      let chars = explode (Obj.obj x ^ padding) in
      [String.concat " "
         (List.map (fun c ->
              let n = int_of_char c in
              if 0x20 <= n && n <= 0x7e then
                Printf.sprintf "%c" c
              else
                Printf.sprintf "%02x" n
            ) chars)]
    else
      [Printf.sprintf "<abstract>"]
  in
  let fields = List.map fix fields in
  let fields = Printf.sprintf "%4d" size :: Printf.sprintf "%4d" tag :: fields in
  let image = Ascii.box fields in
  let rec loop image sl i =
    if i < 0 then
      image
    else
      let s, sl = match sl with s :: sl -> s, sl | [] -> assert false in
      let pivot =
        List.fold_left (fun acc s -> acc + String.length s + 1) 1 sl + String.length s / 2
      in
      let x = Obj.field x i in
      if Obj.is_block x then
        let b = block x in
        let rec sub skip =
          let i = Ascii.shift (pivot + 2) (skip + 3) b in
          if Ascii.overlaps i image then
            sub (skip + 1)
          else
            Ascii.(zcat i (shift pivot 1 (line (4 + skip))))
        in
        loop Ascii.(zcat image (sub 0)) sl (i - 1)
      else
        loop image sl (i - 1)
  in
  if Obj.first_non_constant_constructor_tag <= tag &&
     tag <= Obj.last_non_constant_constructor_tag
  then
    loop image (List.rev fields) (size - 1)
  else
    image

let pp ppf (x : Obj.t) =
  if Obj.is_int x then
    Format.fprintf ppf "0x%nx" Nativeint.(logor (shift_left (of_int (Obj.obj x)) 1) one)
  else
    try
      let s = Ascii.render (block x) in
      Format.fprintf ppf "@.%s" s
    with e ->
      Printf.eprintf "Error: %s\n" (Printexc.to_string e);
      Printexc.print_backtrace stderr;
      flush stderr
