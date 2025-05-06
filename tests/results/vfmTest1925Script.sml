open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1925Theory;
val () = new_theory "vfmTest1925";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1925") $ get_result_defs "vfmTestDefs1925";
val () = export_theory_no_docs ();
