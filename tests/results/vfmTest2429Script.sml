open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2429Theory;
val () = new_theory "vfmTest2429";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2429") $ get_result_defs "vfmTestDefs2429";
val () = export_theory_no_docs ();
