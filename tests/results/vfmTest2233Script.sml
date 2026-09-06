Theory vfmTest2233[no_sig_docs]
Ancestors vfmTestDefs2233
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2233_0.nsv", "result2233_1.nsv", "result2233_2.nsv", "result2233_3.nsv", "result2233_4.nsv", "result2233_5.nsv"];
val thyn = "vfmTestDefs2233";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
