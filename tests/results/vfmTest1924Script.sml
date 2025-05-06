open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1924Theory;
val () = new_theory "vfmTest1924";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1924") $ get_result_defs "vfmTestDefs1924";
val () = export_theory_no_docs ();
