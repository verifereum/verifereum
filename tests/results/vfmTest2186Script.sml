open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2186Theory;
val () = new_theory "vfmTest2186";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2186") $ get_result_defs "vfmTestDefs2186";
val () = export_theory_no_docs ();
