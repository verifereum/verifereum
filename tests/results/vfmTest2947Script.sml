Theory vfmTest2947[no_sig_docs]
Ancestors vfmTestDefs2947
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2947_0.nsv", "result2947_1.nsv", "result2947_2.nsv", "result2947_3.nsv"];
val thyn = "vfmTestDefs2947";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
