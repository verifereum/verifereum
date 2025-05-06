open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0799Theory;
val () = new_theory "vfmTest0799";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0799") $ get_result_defs "vfmTestDefs0799";
val () = export_theory_no_docs ();
