open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1919Theory;
val () = new_theory "vfmTest1919";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1919") $ get_result_defs "vfmTestDefs1919";
val () = export_theory_no_docs ();
