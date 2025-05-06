open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0198Theory;
val () = new_theory "vfmTest0198";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0198") $ get_result_defs "vfmTestDefs0198";
val () = export_theory_no_docs ();
