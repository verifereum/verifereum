open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2723Theory;
val () = new_theory "vfmTest2723";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2723") $ get_result_defs "vfmTestDefs2723";
val () = export_theory_no_docs ();
