open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2295Theory;
val () = new_theory "vfmTest2295";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2295") $ get_result_defs "vfmTestDefs2295";
val () = export_theory_no_docs ();
