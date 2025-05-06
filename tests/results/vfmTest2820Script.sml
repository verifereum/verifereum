open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2820Theory;
val () = new_theory "vfmTest2820";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2820") $ get_result_defs "vfmTestDefs2820";
val () = export_theory_no_docs ();
