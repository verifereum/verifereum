open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1466Theory;
val () = new_theory "vfmTest1466";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1466") $ get_result_defs "vfmTestDefs1466";
val () = export_theory_no_docs ();
