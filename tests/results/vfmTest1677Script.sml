open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1677Theory;
val () = new_theory "vfmTest1677";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1677") $ get_result_defs "vfmTestDefs1677";
val () = export_theory_no_docs ();
