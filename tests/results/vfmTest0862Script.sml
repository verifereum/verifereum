open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0862Theory;
val () = new_theory "vfmTest0862";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0862") $ get_result_defs "vfmTestDefs0862";
val () = export_theory_no_docs ();
