open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2167Theory;
val () = new_theory "vfmTest2167";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2167") $ get_result_defs "vfmTestDefs2167";
val () = export_theory_no_docs ();
