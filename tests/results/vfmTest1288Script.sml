open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1288Theory;
val () = new_theory "vfmTest1288";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1288") $ get_result_defs "vfmTestDefs1288";
val () = export_theory_no_docs ();
