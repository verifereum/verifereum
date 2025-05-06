open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1104Theory;
val () = new_theory "vfmTest1104";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1104") $ get_result_defs "vfmTestDefs1104";
val () = export_theory_no_docs ();
