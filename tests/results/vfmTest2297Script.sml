open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2297Theory;
val () = new_theory "vfmTest2297";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2297") $ get_result_defs "vfmTestDefs2297";
val () = export_theory_no_docs ();
