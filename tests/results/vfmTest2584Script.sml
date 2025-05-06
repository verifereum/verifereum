open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2584Theory;
val () = new_theory "vfmTest2584";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2584") $ get_result_defs "vfmTestDefs2584";
val () = export_theory_no_docs ();
