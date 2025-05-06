open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0525Theory;
val () = new_theory "vfmTest0525";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0525") $ get_result_defs "vfmTestDefs0525";
val () = export_theory_no_docs ();
