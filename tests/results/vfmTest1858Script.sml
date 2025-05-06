open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1858Theory;
val () = new_theory "vfmTest1858";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1858") $ get_result_defs "vfmTestDefs1858";
val () = export_theory_no_docs ();
