open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0936Theory;
val () = new_theory "vfmTest0936";
val thyn = "vfmTestDefs0936";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
