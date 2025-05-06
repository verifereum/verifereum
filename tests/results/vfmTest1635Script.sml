open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1635Theory;
val () = new_theory "vfmTest1635";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1635") $ get_result_defs "vfmTestDefs1635";
val () = export_theory_no_docs ();
