open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1001Theory;
val () = new_theory "vfmTest1001";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1001") $ get_result_defs "vfmTestDefs1001";
val () = export_theory_no_docs ();
