open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1312Theory;
val () = new_theory "vfmTest1312";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1312") $ get_result_defs "vfmTestDefs1312";
val () = export_theory_no_docs ();
