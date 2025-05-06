open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0460Theory;
val () = new_theory "vfmTest0460";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0460") $ get_result_defs "vfmTestDefs0460";
val () = export_theory_no_docs ();
