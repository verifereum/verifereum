open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2530Theory;
val () = new_theory "vfmTest2530";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2530") $ get_result_defs "vfmTestDefs2530";
val () = export_theory_no_docs ();
