open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0081Theory;
val () = new_theory "vfmTest0081";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0081") $ get_result_defs "vfmTestDefs0081";
val () = export_theory_no_docs ();
