open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1808Theory;
val () = new_theory "vfmTest1808";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1808") $ get_result_defs "vfmTestDefs1808";
val () = export_theory_no_docs ();
