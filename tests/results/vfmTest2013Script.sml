open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2013Theory;
val () = new_theory "vfmTest2013";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2013") $ get_result_defs "vfmTestDefs2013";
val () = export_theory_no_docs ();
