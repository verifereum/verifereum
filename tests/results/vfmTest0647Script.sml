open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0647Theory;
val () = new_theory "vfmTest0647";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0647") $ get_result_defs "vfmTestDefs0647";
val () = export_theory_no_docs ();
