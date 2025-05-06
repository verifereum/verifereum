open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1315Theory;
val () = new_theory "vfmTest1315";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1315") $ get_result_defs "vfmTestDefs1315";
val () = export_theory_no_docs ();
