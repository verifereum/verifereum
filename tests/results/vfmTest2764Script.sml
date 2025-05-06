open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2764Theory;
val () = new_theory "vfmTest2764";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2764") $ get_result_defs "vfmTestDefs2764";
val () = export_theory_no_docs ();
