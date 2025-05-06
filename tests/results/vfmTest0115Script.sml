open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0115Theory;
val () = new_theory "vfmTest0115";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0115") $ get_result_defs "vfmTestDefs0115";
val () = export_theory_no_docs ();
