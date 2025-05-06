open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2816Theory;
val () = new_theory "vfmTest2816";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2816") $ get_result_defs "vfmTestDefs2816";
val () = export_theory_no_docs ();
