open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1954Theory;
val () = new_theory "vfmTest1954";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1954") $ get_result_defs "vfmTestDefs1954";
val () = export_theory_no_docs ();
