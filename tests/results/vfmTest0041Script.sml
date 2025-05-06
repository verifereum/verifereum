open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0041Theory;
val () = new_theory "vfmTest0041";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0041") $ get_result_defs "vfmTestDefs0041";
val () = export_theory_no_docs ();
