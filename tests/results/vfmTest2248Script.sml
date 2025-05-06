open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2248Theory;
val () = new_theory "vfmTest2248";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2248") $ get_result_defs "vfmTestDefs2248";
val () = export_theory_no_docs ();
