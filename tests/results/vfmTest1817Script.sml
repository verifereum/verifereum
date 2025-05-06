open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1817Theory;
val () = new_theory "vfmTest1817";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1817") $ get_result_defs "vfmTestDefs1817";
val () = export_theory_no_docs ();
