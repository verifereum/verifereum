Theory vfmTest2244[no_sig_docs]
Ancestors vfmTestDefs2244
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2244_0.nsv", "result2244_1.nsv", "result2244_2.nsv", "result2244_3.nsv", "result2244_4.nsv", "result2244_5.nsv", "result2244_6.nsv", "result2244_7.nsv", "result2244_8.nsv", "result2244_9.nsv", "result2244_10.nsv", "result2244_11.nsv", "result2244_12.nsv", "result2244_13.nsv", "result2244_14.nsv", "result2244_15.nsv", "result2244_16.nsv"];
val thyn = "vfmTestDefs2244";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
