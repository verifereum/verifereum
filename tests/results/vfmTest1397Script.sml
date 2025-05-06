open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1397Theory;
val () = new_theory "vfmTest1397";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1397") $ get_result_defs "vfmTestDefs1397";
val () = export_theory_no_docs ();
