open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1981Theory;
val () = new_theory "vfmTest1981";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1981") $ get_result_defs "vfmTestDefs1981";
val () = export_theory_no_docs ();
