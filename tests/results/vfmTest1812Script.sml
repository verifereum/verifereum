open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1812Theory;
val () = new_theory "vfmTest1812";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1812") $ get_result_defs "vfmTestDefs1812";
val () = export_theory_no_docs ();
