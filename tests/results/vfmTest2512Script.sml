open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2512Theory;
val () = new_theory "vfmTest2512";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2512") $ get_result_defs "vfmTestDefs2512";
val () = export_theory_no_docs ();
