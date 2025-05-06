open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1095Theory;
val () = new_theory "vfmTest1095";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1095") $ get_result_defs "vfmTestDefs1095";
val () = export_theory_no_docs ();
