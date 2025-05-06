open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1662Theory;
val () = new_theory "vfmTest1662";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1662") $ get_result_defs "vfmTestDefs1662";
val () = export_theory_no_docs ();
