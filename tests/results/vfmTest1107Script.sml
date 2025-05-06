open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1107Theory;
val () = new_theory "vfmTest1107";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1107") $ get_result_defs "vfmTestDefs1107";
val () = export_theory_no_docs ();
