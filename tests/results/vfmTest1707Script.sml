open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1707Theory;
val () = new_theory "vfmTest1707";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1707") $ get_result_defs "vfmTestDefs1707";
val () = export_theory_no_docs ();
