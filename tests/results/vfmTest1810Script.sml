open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1810Theory;
val () = new_theory "vfmTest1810";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1810") $ get_result_defs "vfmTestDefs1810";
val () = export_theory_no_docs ();
