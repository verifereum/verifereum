open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1786Theory;
val () = new_theory "vfmTest1786";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1786") $ get_result_defs "vfmTestDefs1786";
val () = export_theory_no_docs ();
