open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1797Theory;
val () = new_theory "vfmTest1797";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1797") $ get_result_defs "vfmTestDefs1797";
val () = export_theory_no_docs ();
