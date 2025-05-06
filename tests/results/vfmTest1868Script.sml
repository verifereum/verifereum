open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1868Theory;
val () = new_theory "vfmTest1868";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1868") $ get_result_defs "vfmTestDefs1868";
val () = export_theory_no_docs ();
