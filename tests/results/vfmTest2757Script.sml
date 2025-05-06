open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2757Theory;
val () = new_theory "vfmTest2757";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2757") $ get_result_defs "vfmTestDefs2757";
val () = export_theory_no_docs ();
