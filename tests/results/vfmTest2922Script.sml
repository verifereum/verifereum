open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2922Theory;
val () = new_theory "vfmTest2922";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2922") $ get_result_defs "vfmTestDefs2922";
val () = export_theory_no_docs ();
