open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1680Theory;
val () = new_theory "vfmTest1680";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1680") $ get_result_defs "vfmTestDefs1680";
val () = export_theory_no_docs ();
