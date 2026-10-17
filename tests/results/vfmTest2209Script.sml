Theory vfmTest2209[no_sig_docs]
Ancestors vfmTestDefs2209
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2209_0.nsv", "result2209_1.nsv", "result2209_2.nsv", "result2209_3.nsv", "result2209_4.nsv", "result2209_5.nsv"];
val thyn = "vfmTestDefs2209";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
