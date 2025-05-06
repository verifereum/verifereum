open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1965Theory;
val () = new_theory "vfmTest1965";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1965") $ get_result_defs "vfmTestDefs1965";
val () = export_theory_no_docs ();
