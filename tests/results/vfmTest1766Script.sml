open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1766Theory;
val () = new_theory "vfmTest1766";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1766") $ get_result_defs "vfmTestDefs1766";
val () = export_theory_no_docs ();
