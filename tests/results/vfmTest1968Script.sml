open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1968Theory;
val () = new_theory "vfmTest1968";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1968") $ get_result_defs "vfmTestDefs1968";
val () = export_theory_no_docs ();
