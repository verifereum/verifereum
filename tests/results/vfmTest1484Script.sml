open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1484Theory;
val () = new_theory "vfmTest1484";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1484") $ get_result_defs "vfmTestDefs1484";
val () = export_theory_no_docs ();
