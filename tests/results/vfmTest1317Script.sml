open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1317Theory;
val () = new_theory "vfmTest1317";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1317") $ get_result_defs "vfmTestDefs1317";
val () = export_theory_no_docs ();
