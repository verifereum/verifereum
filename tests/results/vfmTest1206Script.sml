open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1206Theory;
val () = new_theory "vfmTest1206";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1206") $ get_result_defs "vfmTestDefs1206";
val () = export_theory_no_docs ();
