open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0461Theory;
val () = new_theory "vfmTest0461";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0461") $ get_result_defs "vfmTestDefs0461";
val () = export_theory_no_docs ();
