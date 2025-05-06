open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2034Theory;
val () = new_theory "vfmTest2034";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2034") $ get_result_defs "vfmTestDefs2034";
val () = export_theory_no_docs ();
