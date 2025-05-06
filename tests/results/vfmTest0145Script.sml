open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0145Theory;
val () = new_theory "vfmTest0145";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0145") $ get_result_defs "vfmTestDefs0145";
val () = export_theory_no_docs ();
