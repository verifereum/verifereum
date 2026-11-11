Theory vfmTest2188[no_sig_docs]
Ancestors vfmTestDefs2188
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2188_0.nsv", "result2188_1.nsv", "result2188_2.nsv", "result2188_3.nsv", "result2188_4.nsv", "result2188_5.nsv", "result2188_6.nsv", "result2188_7.nsv", "result2188_8.nsv", "result2188_9.nsv", "result2188_10.nsv", "result2188_11.nsv", "result2188_12.nsv", "result2188_13.nsv", "result2188_14.nsv", "result2188_15.nsv", "result2188_16.nsv", "result2188_17.nsv", "result2188_18.nsv", "result2188_19.nsv"];
val thyn = "vfmTestDefs2188";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
