open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1836Theory;
val () = new_theory "vfmTest1836";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1836") $ get_result_defs "vfmTestDefs1836";
val () = export_theory_no_docs ();
