open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2303Theory;
val () = new_theory "vfmTest2303";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2303") $ get_result_defs "vfmTestDefs2303";
val () = export_theory_no_docs ();
