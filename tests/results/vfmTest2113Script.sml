open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2113Theory;
val () = new_theory "vfmTest2113";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2113") $ get_result_defs "vfmTestDefs2113";
val () = export_theory_no_docs ();
