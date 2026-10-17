Theory vfmTest2205[no_sig_docs]
Ancestors vfmTestDefs2205
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2205_0.nsv", "result2205_1.nsv", "result2205_2.nsv", "result2205_3.nsv", "result2205_4.nsv", "result2205_5.nsv", "result2205_6.nsv", "result2205_7.nsv", "result2205_8.nsv", "result2205_9.nsv", "result2205_10.nsv", "result2205_11.nsv", "result2205_12.nsv", "result2205_13.nsv", "result2205_14.nsv", "result2205_15.nsv"];
val thyn = "vfmTestDefs2205";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
