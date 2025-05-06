open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2317Theory;
val () = new_theory "vfmTest2317";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2317") $ get_result_defs "vfmTestDefs2317";
val () = export_theory_no_docs ();
