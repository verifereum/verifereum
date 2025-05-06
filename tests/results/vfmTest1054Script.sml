open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1054Theory;
val () = new_theory "vfmTest1054";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1054") $ get_result_defs "vfmTestDefs1054";
val () = export_theory_no_docs ();
