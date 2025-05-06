open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2565Theory;
val () = new_theory "vfmTest2565";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2565") $ get_result_defs "vfmTestDefs2565";
val () = export_theory_no_docs ();
