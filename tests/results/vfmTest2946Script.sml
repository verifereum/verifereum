Theory vfmTest2946[no_sig_docs]
Ancestors vfmTestDefs2946
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2946_0.nsv", "result2946_1.nsv", "result2946_2.nsv"];
val thyn = "vfmTestDefs2946";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
