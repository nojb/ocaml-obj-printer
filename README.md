```
$ ocamlc -c obj_pp.mli obj_pp.ml
# ocaml obj_pp.cmo
# #install_printer Obj_pp.pp;;
# Obj.repr [`first [|1.2; 3.4|]; `second (ref 1.2, ref "hola")];;
- : Obj.t =
┌────┬────┬──────────┬──────────┐
│   2│   0│     ┬ [0]│     ┬ [1]│
└────┴────┴─────│────┴─────│────┘
                │          │
                │          │ ┌────┬────┬──────────┬──────────┐
                │          └─┤   2│   0│     ┬ [0]│         0│
                │            └────┴────┴─────│────┴──────────┘
                │                            │
                │                            │ ┌────┬────┬──────────┬──────────┐
                │                            └─┤   2│   0│-465055884│     ┬ [1]│
                │                              └────┴────┴──────────┴─────│────┘
                │                                                         │
                │ ┌────┬────┬──────────┬──────────┐                       │ ┌────┬────┬──────────┬──────────┐
                └─┤   2│   0│  10319920│     ┬ [1]│                       └─┤   2│   0│     ┬ [0]│     ┬ [1]│
                  └────┴────┴──────────┴─────│────┘                         └────┴────┴─────│────┴─────│────┘
                                             │                                              │          │
                                             │ ┌────┬────┬──────────┬──────────┐            │          │ ┌────┬────┬──────────┐
                                             └─┤   2│ 254│       1.2│       3.4│            │          └─┤   1│   0│     ┬ [0]│
                                               └────┴────┴──────────┴──────────┘            │            └────┴────┴─────│────┘
                                                                                            │                            │
                                                                                            │ ┌────┬────┬──────────┐     │ ┌────┬────┬───────────────────┐
                                                                                            └─┤   1│   0│     ┬ [0]│     └─┤   1│ 252│h o l a 00 00 00 03│
                                                                                              └────┴────┴─────│────┘       └────┴────┴───────────────────┘
                                                                                                              │
                                                                                                              │ ┌────┬────┬──────────┐
                                                                                                              └─┤   1│ 253│       1.2│
                                                                                                                └────┴────┴──────────┘
```
