open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0563Theory;
val () = new_theory "vfmTest0563";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0563") $ get_result_defs "vfmTestDefs0563";
val () = export_theory_no_docs ();
