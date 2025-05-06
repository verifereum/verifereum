open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2025Theory;
val () = new_theory "vfmTest2025";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2025") $ get_result_defs "vfmTestDefs2025";
val () = export_theory_no_docs ();
