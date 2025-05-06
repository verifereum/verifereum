open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1535Theory;
val () = new_theory "vfmTest1535";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1535") $ get_result_defs "vfmTestDefs1535";
val () = export_theory_no_docs ();
