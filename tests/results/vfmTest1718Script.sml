open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1718Theory;
val () = new_theory "vfmTest1718";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1718") $ get_result_defs "vfmTestDefs1718";
val () = export_theory_no_docs ();
