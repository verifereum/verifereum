open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1229Theory;
val () = new_theory "vfmTest1229";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1229") $ get_result_defs "vfmTestDefs1229";
val () = export_theory_no_docs ();
