open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1373Theory;
val () = new_theory "vfmTest1373";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1373") $ get_result_defs "vfmTestDefs1373";
val () = export_theory_no_docs ();
