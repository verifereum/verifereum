open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2367Theory;
val () = new_theory "vfmTest2367";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2367") $ get_result_defs "vfmTestDefs2367";
val () = export_theory_no_docs ();
