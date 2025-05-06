open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1174Theory;
val () = new_theory "vfmTest1174";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1174") $ get_result_defs "vfmTestDefs1174";
val () = export_theory_no_docs ();
