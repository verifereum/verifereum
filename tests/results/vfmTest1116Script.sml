open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1116Theory;
val () = new_theory "vfmTest1116";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1116") $ get_result_defs "vfmTestDefs1116";
val () = export_theory_no_docs ();
