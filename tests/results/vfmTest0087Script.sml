open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0087Theory;
val () = new_theory "vfmTest0087";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0087") $ get_result_defs "vfmTestDefs0087";
val () = export_theory_no_docs ();
