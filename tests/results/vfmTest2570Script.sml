open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2570Theory;
val () = new_theory "vfmTest2570";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2570") $ get_result_defs "vfmTestDefs2570";
val () = export_theory_no_docs ();
