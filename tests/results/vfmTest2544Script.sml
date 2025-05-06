open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2544Theory;
val () = new_theory "vfmTest2544";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2544") $ get_result_defs "vfmTestDefs2544";
val () = export_theory_no_docs ();
