open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2443Theory;
val () = new_theory "vfmTest2443";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2443") $ get_result_defs "vfmTestDefs2443";
val () = export_theory_no_docs ();
