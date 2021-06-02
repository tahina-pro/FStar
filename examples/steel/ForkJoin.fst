module ForkJoin

open FStar.Ghost
open Steel.Memory
open Steel.Effect
open Steel.Reference
open Steel.Primitive.ForkJoin.Unix2

(* Examples from Steel.Primitive.ForkJoin.Unix but directly within Steel, without the additional layered effect *)

assume val q : int -> vprop
assume val f : unit -> SteelT unit emp (fun _ -> emp)
assume val g : i:int -> SteelT unit emp (fun _ -> q i)
assume val h : unit -> SteelT unit emp (fun _ -> emp)

let example () : SteelT unit emp (fun _ -> q 1 `star` q 2) =
  let p1:thread_id (q 1) = fork (fun () -> g 1) in
  let p2:thread_id (q 2) = fork (fun () -> g 2) in
  join p1;
  h();
  join p2

open Steel.FractionalPermission

let example2 (r:ref int) : SteelT (thread_id (pts_to r full_perm 1)) (pts_to r full_perm 0) (fun t -> thread_resource t) =
  let p1 = fork (fun _ -> write_pt #_ #0 r 1) in
  p1

let example3 (r:ref int) : SteelT (ref int) (pts_to r full_perm 0) (fun x -> pts_to r full_perm 1 `star` pts_to x full_perm 2) =
  let p1 = fork (fun _ -> write_pt #_ #0 r 1) in
  let x = alloc_pt 2 in
  join p1;
  x

let example4 () : SteelT (ref int) emp (fun r -> pts_to r full_perm 2) =
  let x = alloc_pt 0 in
  let y = alloc_pt 1 in
  let p1:thread_id (pts_to x full_perm 1) = fork (fun _ -> write_pt #_ #0 x 1) in
  let p2:thread_id emp = fork (fun _ -> free_pt #_ #1 y) in
  join p1;
  write_pt #_ #1 x 2;
  join p2;
  x
