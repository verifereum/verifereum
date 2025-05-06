open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1922Theory;
val () = new_theory "vfmTest1922";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1922") $ get_result_defs "vfmTestDefs1922";
val () = export_theory_no_docs ();
