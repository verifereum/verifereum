open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1576Theory;
val () = new_theory "vfmTest1576";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1576") $ get_result_defs "vfmTestDefs1576";
val () = export_theory_no_docs ();
