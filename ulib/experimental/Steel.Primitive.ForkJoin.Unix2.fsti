module Steel.Primitive.ForkJoin.Unix2
open Steel.Effect
open Steel.Memory

val thread_id
  (p: vprop)
: Tot Type0

val thread_resource
  (#p: vprop)
  (t: thread_id p)
: Tot vprop

val fork
  (#p #q: vprop)
  (f: unit -> SteelT unit p (fun _ -> q))
: SteelT (thread_id q) p (fun t -> thread_resource t)

val join
  (#q: vprop)
  (t: thread_id q)
: SteelT unit (thread_resource t) (fun _ -> q)
