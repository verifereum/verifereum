open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1403Theory;
val () = new_theory "vfmTest1403";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1403") $ get_result_defs "vfmTestDefs1403";
val () = export_theory_no_docs ();
