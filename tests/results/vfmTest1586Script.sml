open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1586Theory;
val () = new_theory "vfmTest1586";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1586") $ get_result_defs "vfmTestDefs1586";
val () = export_theory_no_docs ();
