Theory vfmTest2208[no_sig_docs]
Ancestors vfmTestDefs2208
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2208_0.nsv", "result2208_1.nsv", "result2208_2.nsv", "result2208_3.nsv", "result2208_4.nsv", "result2208_5.nsv", "result2208_6.nsv", "result2208_7.nsv", "result2208_8.nsv", "result2208_9.nsv", "result2208_10.nsv", "result2208_11.nsv", "result2208_12.nsv", "result2208_13.nsv", "result2208_14.nsv"];
val thyn = "vfmTestDefs2208";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
