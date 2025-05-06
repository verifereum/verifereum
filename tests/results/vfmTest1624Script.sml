open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1624Theory;
val () = new_theory "vfmTest1624";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1624") $ get_result_defs "vfmTestDefs1624";
val () = export_theory_no_docs ();
