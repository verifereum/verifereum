open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1940Theory;
val () = new_theory "vfmTest1940";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1940") $ get_result_defs "vfmTestDefs1940";
val () = export_theory_no_docs ();
