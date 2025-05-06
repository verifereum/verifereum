open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2868Theory;
val () = new_theory "vfmTest2868";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2868") $ get_result_defs "vfmTestDefs2868";
val () = export_theory_no_docs ();
