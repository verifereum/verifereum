open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1520Theory;
val () = new_theory "vfmTest1520";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1520") $ get_result_defs "vfmTestDefs1520";
val () = export_theory_no_docs ();
