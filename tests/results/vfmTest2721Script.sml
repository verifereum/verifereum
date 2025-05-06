open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2721Theory;
val () = new_theory "vfmTest2721";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2721") $ get_result_defs "vfmTestDefs2721";
val () = export_theory_no_docs ();
