open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1533Theory;
val () = new_theory "vfmTest1533";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1533") $ get_result_defs "vfmTestDefs1533";
val () = export_theory_no_docs ();
