open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0359Theory;
val () = new_theory "vfmTest0359";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0359") $ get_result_defs "vfmTestDefs0359";
val () = export_theory_no_docs ();
