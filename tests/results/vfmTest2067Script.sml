open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2067Theory;
val () = new_theory "vfmTest2067";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2067") $ get_result_defs "vfmTestDefs2067";
val () = export_theory_no_docs ();
