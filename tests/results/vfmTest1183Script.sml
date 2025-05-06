open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1183Theory;
val () = new_theory "vfmTest1183";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1183") $ get_result_defs "vfmTestDefs1183";
val () = export_theory_no_docs ();
