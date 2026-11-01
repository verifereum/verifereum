Theory vfmTest2340[no_sig_docs]
Ancestors vfmTestDefs2340
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2340_0.nsv", "result2340_1.nsv", "result2340_2.nsv", "result2340_3.nsv", "result2340_4.nsv", "result2340_5.nsv", "result2340_6.nsv", "result2340_7.nsv", "result2340_8.nsv", "result2340_9.nsv", "result2340_10.nsv", "result2340_11.nsv", "result2340_12.nsv", "result2340_13.nsv", "result2340_14.nsv", "result2340_15.nsv", "result2340_16.nsv", "result2340_17.nsv", "result2340_18.nsv", "result2340_19.nsv", "result2340_20.nsv", "result2340_21.nsv", "result2340_22.nsv", "result2340_23.nsv"];
val thyn = "vfmTestDefs2340";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
