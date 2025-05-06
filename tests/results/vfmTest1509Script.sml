open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1509Theory;
val () = new_theory "vfmTest1509";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1509") $ get_result_defs "vfmTestDefs1509";
val () = export_theory_no_docs ();
