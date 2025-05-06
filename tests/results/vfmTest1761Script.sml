open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1761Theory;
val () = new_theory "vfmTest1761";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1761") $ get_result_defs "vfmTestDefs1761";
val () = export_theory_no_docs ();
