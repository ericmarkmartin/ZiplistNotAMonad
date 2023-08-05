(lang dune 3.10)
(using coq 0.8)
(name zlist-not-a-monad)


(package
 (name zlist-not-a-monad)
 (depends
  (coq (>= 8.13))
  (coq-ext-lib (>= 0.11.1)))
)


(generate_opam_files true)
