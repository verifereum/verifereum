open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2793Theory;
val () = new_theory "vfmTest2793";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2793") $ get_result_defs "vfmTestDefs2793";
val () = export_theory_no_docs ();
