open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2348Theory;
val () = new_theory "vfmTest2348";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2348") $ get_result_defs "vfmTestDefs2348";
val () = export_theory_no_docs ();
