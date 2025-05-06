open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1757Theory;
val () = new_theory "vfmTest1757";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1757") $ get_result_defs "vfmTestDefs1757";
val () = export_theory_no_docs ();
