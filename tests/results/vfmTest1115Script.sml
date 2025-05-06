open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1115Theory;
val () = new_theory "vfmTest1115";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1115") $ get_result_defs "vfmTestDefs1115";
val () = export_theory_no_docs ();
