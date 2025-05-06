open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1676Theory;
val () = new_theory "vfmTest1676";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1676") $ get_result_defs "vfmTestDefs1676";
val () = export_theory_no_docs ();
