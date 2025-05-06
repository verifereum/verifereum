open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1999Theory;
val () = new_theory "vfmTest1999";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1999") $ get_result_defs "vfmTestDefs1999";
val () = export_theory_no_docs ();
