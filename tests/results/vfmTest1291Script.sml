open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1291Theory;
val () = new_theory "vfmTest1291";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1291") $ get_result_defs "vfmTestDefs1291";
val () = export_theory_no_docs ();
