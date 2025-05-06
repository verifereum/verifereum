open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0089Theory;
val () = new_theory "vfmTest0089";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0089") $ get_result_defs "vfmTestDefs0089";
val () = export_theory_no_docs ();
