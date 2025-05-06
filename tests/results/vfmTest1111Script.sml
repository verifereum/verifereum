open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1111Theory;
val () = new_theory "vfmTest1111";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1111") $ get_result_defs "vfmTestDefs1111";
val () = export_theory_no_docs ();
