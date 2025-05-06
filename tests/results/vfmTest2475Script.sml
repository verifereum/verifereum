open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2475Theory;
val () = new_theory "vfmTest2475";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2475") $ get_result_defs "vfmTestDefs2475";
val () = export_theory_no_docs ();
