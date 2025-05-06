open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2685Theory;
val () = new_theory "vfmTest2685";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2685") $ get_result_defs "vfmTestDefs2685";
val () = export_theory_no_docs ();
