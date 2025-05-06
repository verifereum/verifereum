open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1664Theory;
val () = new_theory "vfmTest1664";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1664") $ get_result_defs "vfmTestDefs1664";
val () = export_theory_no_docs ();
