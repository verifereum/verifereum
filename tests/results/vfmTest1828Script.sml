open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1828Theory;
val () = new_theory "vfmTest1828";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1828") $ get_result_defs "vfmTestDefs1828";
val () = export_theory_no_docs ();
