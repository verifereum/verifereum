open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1884Theory;
val () = new_theory "vfmTest1884";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1884") $ get_result_defs "vfmTestDefs1884";
val () = export_theory_no_docs ();
