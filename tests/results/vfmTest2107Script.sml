open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2107Theory;
val () = new_theory "vfmTest2107";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2107") $ get_result_defs "vfmTestDefs2107";
val () = export_theory_no_docs ();
