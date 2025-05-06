open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1135Theory;
val () = new_theory "vfmTest1135";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1135") $ get_result_defs "vfmTestDefs1135";
val () = export_theory_no_docs ();
