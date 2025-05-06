open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1015Theory;
val () = new_theory "vfmTest1015";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1015") $ get_result_defs "vfmTestDefs1015";
val () = export_theory_no_docs ();
