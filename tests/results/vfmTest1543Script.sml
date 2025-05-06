open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1543Theory;
val () = new_theory "vfmTest1543";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1543") $ get_result_defs "vfmTestDefs1543";
val () = export_theory_no_docs ();
