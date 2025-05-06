open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1979Theory;
val () = new_theory "vfmTest1979";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1979") $ get_result_defs "vfmTestDefs1979";
val () = export_theory_no_docs ();
