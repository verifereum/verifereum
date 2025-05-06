open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2126Theory;
val () = new_theory "vfmTest2126";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2126") $ get_result_defs "vfmTestDefs2126";
val () = export_theory_no_docs ();
