open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1186Theory;
val () = new_theory "vfmTest1186";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1186") $ get_result_defs "vfmTestDefs1186";
val () = export_theory_no_docs ();
