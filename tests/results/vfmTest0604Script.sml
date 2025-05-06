open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0604Theory;
val () = new_theory "vfmTest0604";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0604") $ get_result_defs "vfmTestDefs0604";
val () = export_theory_no_docs ();
