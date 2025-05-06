open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2884Theory;
val () = new_theory "vfmTest2884";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2884") $ get_result_defs "vfmTestDefs2884";
val () = export_theory_no_docs ();
