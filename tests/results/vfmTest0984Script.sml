open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0984Theory;
val () = new_theory "vfmTest0984";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0984") $ get_result_defs "vfmTestDefs0984";
val () = export_theory_no_docs ();
