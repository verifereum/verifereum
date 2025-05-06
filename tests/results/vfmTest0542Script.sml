open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0542Theory;
val () = new_theory "vfmTest0542";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0542") $ get_result_defs "vfmTestDefs0542";
val () = export_theory_no_docs ();
