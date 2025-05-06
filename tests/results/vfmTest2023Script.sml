open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2023Theory;
val () = new_theory "vfmTest2023";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2023") $ get_result_defs "vfmTestDefs2023";
val () = export_theory_no_docs ();
