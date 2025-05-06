open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0592Theory;
val () = new_theory "vfmTest0592";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0592") $ get_result_defs "vfmTestDefs0592";
val () = export_theory_no_docs ();
