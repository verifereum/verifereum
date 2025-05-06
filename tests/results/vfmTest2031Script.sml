open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2031Theory;
val () = new_theory "vfmTest2031";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2031") $ get_result_defs "vfmTestDefs2031";
val () = export_theory_no_docs ();
