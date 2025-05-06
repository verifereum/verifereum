open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1184Theory;
val () = new_theory "vfmTest1184";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1184") $ get_result_defs "vfmTestDefs1184";
val () = export_theory_no_docs ();
