module Steel.Primitive.ForkJoin.Unix2
open Steel.Effect.Atomic

module P = Steel.Primitive.ForkJoin
module R = Steel.Reference

let thread_id p = R.ref (option (P.thread p))
  
let thread_resource t =
  R.vptr t `vrefine` (fun s -> Some? s == true)

let fork #p #q f =
  let t : thread_id q = R.alloc None in
  P.fork
    #p
    #q
    #(R.vptr t)
    #(thread_resource t)
    f
    (fun i _ ->
      R.write t (Some i);
      intro_vrefine (R.vptr t) (fun s -> Some? s == true)
    );
  t

let join #p t =
  elim_vrefine (R.vptr t) (fun s -> Some? s == true);
  let r = R.read t in
  R.free t;
  let Some i = r in
  P.join i
