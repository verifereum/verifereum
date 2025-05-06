open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2245Theory;
val () = new_theory "vfmTest2245";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2245") $ get_result_defs "vfmTestDefs2245";
val () = export_theory_no_docs ();
