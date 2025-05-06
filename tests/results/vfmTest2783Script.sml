open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2783Theory;
val () = new_theory "vfmTest2783";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2783") $ get_result_defs "vfmTestDefs2783";
val () = export_theory_no_docs ();
