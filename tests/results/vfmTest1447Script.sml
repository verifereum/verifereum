open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1447Theory;
val () = new_theory "vfmTest1447";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1447") $ get_result_defs "vfmTestDefs1447";
val () = export_theory_no_docs ();
