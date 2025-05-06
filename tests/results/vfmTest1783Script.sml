open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1783Theory;
val () = new_theory "vfmTest1783";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1783") $ get_result_defs "vfmTestDefs1783";
val () = export_theory_no_docs ();
