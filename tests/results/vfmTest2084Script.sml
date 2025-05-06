open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2084Theory;
val () = new_theory "vfmTest2084";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2084") $ get_result_defs "vfmTestDefs2084";
val () = export_theory_no_docs ();
