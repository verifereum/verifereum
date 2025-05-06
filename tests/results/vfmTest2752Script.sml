open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2752Theory;
val () = new_theory "vfmTest2752";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2752") $ get_result_defs "vfmTestDefs2752";
val () = export_theory_no_docs ();
