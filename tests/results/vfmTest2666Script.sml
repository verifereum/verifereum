open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2666Theory;
val () = new_theory "vfmTest2666";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2666") $ get_result_defs "vfmTestDefs2666";
val () = export_theory_no_docs ();
