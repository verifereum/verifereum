open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1934Theory;
val () = new_theory "vfmTest1934";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1934") $ get_result_defs "vfmTestDefs1934";
val () = export_theory_no_docs ();
