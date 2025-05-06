open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2726Theory;
val () = new_theory "vfmTest2726";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2726") $ get_result_defs "vfmTestDefs2726";
val () = export_theory_no_docs ();
