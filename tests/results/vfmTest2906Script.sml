open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2906Theory;
val () = new_theory "vfmTest2906";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2906") $ get_result_defs "vfmTestDefs2906";
val () = export_theory_no_docs ();
