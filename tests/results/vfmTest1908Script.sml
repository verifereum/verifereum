open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1908Theory;
val () = new_theory "vfmTest1908";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1908") $ get_result_defs "vfmTestDefs1908";
val () = export_theory_no_docs ();
