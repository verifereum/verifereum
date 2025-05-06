open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2824Theory;
val () = new_theory "vfmTest2824";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2824") $ get_result_defs "vfmTestDefs2824";
val () = export_theory_no_docs ();
