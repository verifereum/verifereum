open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1949Theory;
val () = new_theory "vfmTest1949";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1949") $ get_result_defs "vfmTestDefs1949";
val () = export_theory_no_docs ();
