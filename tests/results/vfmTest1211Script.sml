open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1211Theory;
val () = new_theory "vfmTest1211";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1211") $ get_result_defs "vfmTestDefs1211";
val () = export_theory_no_docs ();
