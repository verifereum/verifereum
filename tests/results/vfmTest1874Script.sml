open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1874Theory;
val () = new_theory "vfmTest1874";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1874") $ get_result_defs "vfmTestDefs1874";
val () = export_theory_no_docs ();
