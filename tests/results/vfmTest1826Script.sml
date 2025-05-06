open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1826Theory;
val () = new_theory "vfmTest1826";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1826") $ get_result_defs "vfmTestDefs1826";
val () = export_theory_no_docs ();
