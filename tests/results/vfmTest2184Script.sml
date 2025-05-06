open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2184Theory;
val () = new_theory "vfmTest2184";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2184") $ get_result_defs "vfmTestDefs2184";
val () = export_theory_no_docs ();
