open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1500Theory;
val () = new_theory "vfmTest1500";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1500") $ get_result_defs "vfmTestDefs1500";
val () = export_theory_no_docs ();
