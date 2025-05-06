open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1052Theory;
val () = new_theory "vfmTest1052";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1052") $ get_result_defs "vfmTestDefs1052";
val () = export_theory_no_docs ();
