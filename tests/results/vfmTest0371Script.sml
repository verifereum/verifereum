open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0371Theory;
val () = new_theory "vfmTest0371";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0371") $ get_result_defs "vfmTestDefs0371";
val () = export_theory_no_docs ();
