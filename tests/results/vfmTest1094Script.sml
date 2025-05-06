open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1094Theory;
val () = new_theory "vfmTest1094";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1094") $ get_result_defs "vfmTestDefs1094";
val () = export_theory_no_docs ();
