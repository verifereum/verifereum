open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2428Theory;
val () = new_theory "vfmTest2428";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2428") $ get_result_defs "vfmTestDefs2428";
val () = export_theory_no_docs ();
