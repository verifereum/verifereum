open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1098Theory;
val () = new_theory "vfmTest1098";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1098") $ get_result_defs "vfmTestDefs1098";
val () = export_theory_no_docs ();
