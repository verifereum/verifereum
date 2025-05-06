open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2444Theory;
val () = new_theory "vfmTest2444";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2444") $ get_result_defs "vfmTestDefs2444";
val () = export_theory_no_docs ();
