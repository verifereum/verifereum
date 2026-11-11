Theory vfmTest2104[no_sig_docs]
Ancestors vfmTestDefs2104
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2104_0.nsv", "result2104_1.nsv", "result2104_2.nsv", "result2104_3.nsv", "result2104_4.nsv", "result2104_5.nsv", "result2104_6.nsv", "result2104_7.nsv", "result2104_8.nsv", "result2104_9.nsv", "result2104_10.nsv", "result2104_11.nsv", "result2104_12.nsv", "result2104_13.nsv", "result2104_14.nsv", "result2104_15.nsv", "result2104_16.nsv"];
val thyn = "vfmTestDefs2104";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
