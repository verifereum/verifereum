open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1040Theory;
val () = new_theory "vfmTest1040";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1040") $ get_result_defs "vfmTestDefs1040";
val () = export_theory_no_docs ();
