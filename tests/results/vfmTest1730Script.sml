open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1730Theory;
val () = new_theory "vfmTest1730";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1730") $ get_result_defs "vfmTestDefs1730";
val () = export_theory_no_docs ();
