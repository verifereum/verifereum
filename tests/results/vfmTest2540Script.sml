open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2540Theory;
val () = new_theory "vfmTest2540";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2540") $ get_result_defs "vfmTestDefs2540";
val () = export_theory_no_docs ();
