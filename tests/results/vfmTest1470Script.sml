open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1470Theory;
val () = new_theory "vfmTest1470";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1470") $ get_result_defs "vfmTestDefs1470";
val () = export_theory_no_docs ();
