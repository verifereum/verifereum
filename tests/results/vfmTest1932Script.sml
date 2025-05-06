open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1932Theory;
val () = new_theory "vfmTest1932";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1932") $ get_result_defs "vfmTestDefs1932";
val () = export_theory_no_docs ();
