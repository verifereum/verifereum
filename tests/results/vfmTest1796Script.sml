open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1796Theory;
val () = new_theory "vfmTest1796";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1796") $ get_result_defs "vfmTestDefs1796";
val () = export_theory_no_docs ();
