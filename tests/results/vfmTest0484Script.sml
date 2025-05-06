open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0484Theory;
val () = new_theory "vfmTest0484";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0484") $ get_result_defs "vfmTestDefs0484";
val () = export_theory_no_docs ();
