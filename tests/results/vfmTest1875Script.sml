open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1875Theory;
val () = new_theory "vfmTest1875";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1875") $ get_result_defs "vfmTestDefs1875";
val () = export_theory_no_docs ();
