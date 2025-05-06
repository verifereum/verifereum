open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2857Theory;
val () = new_theory "vfmTest2857";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2857") $ get_result_defs "vfmTestDefs2857";
val () = export_theory_no_docs ();
