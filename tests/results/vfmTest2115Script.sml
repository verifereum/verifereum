open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2115Theory;
val () = new_theory "vfmTest2115";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2115") $ get_result_defs "vfmTestDefs2115";
val () = export_theory_no_docs ();
