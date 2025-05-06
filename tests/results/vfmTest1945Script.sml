open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1945Theory;
val () = new_theory "vfmTest1945";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1945") $ get_result_defs "vfmTestDefs1945";
val () = export_theory_no_docs ();
